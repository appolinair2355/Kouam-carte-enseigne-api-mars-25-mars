import os
import asyncio
import re
import logging
import sys
import io
from dataclasses import dataclass, field
from typing import List, Optional, Dict, Set, Tuple
from datetime import datetime, timedelta
from telethon import TelegramClient, events, utils
from telethon.sessions import StringSession
from telethon.errors import ChatWriteForbiddenError, UserBannedInChannelError
from aiohttp import web
from fpdf import FPDF

from config import (
    API_ID, API_HASH, BOT_TOKEN, ADMIN_ID,
    PREDICTION_CHANNEL_ID, PORT,
    ALL_SUITS, SUIT_DISPLAY
)
from api_utils import get_latest_results

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger(__name__)

if not API_ID or API_ID == 0:
    logger.error("API_ID manquant")
    exit(1)
if not API_HASH:
    logger.error("API_HASH manquant")
    exit(1)
if not BOT_TOKEN:
    logger.error("BOT_TOKEN manquant")
    exit(1)

# ============================================================================
# VARIABLES GLOBALES
# ============================================================================

pending_predictions: Dict[int, dict] = {}
current_game_number = 0
last_prediction_time: Optional[datetime] = None
prediction_channel_ok = False
client = None
suit_block_until: Dict[str, datetime] = {}

# Historique API des jeux
game_history: Dict[int, dict] = {}
processed_games: Set[int] = set()  # Jeux déjà comptabilisés (compteur2, compteur4)
prediction_checked_games: Set[int] = set()  # Jeux dont les prédictions ont été vérifiées

# Compteur2 - Gestion des costumes manquants
compteur2_trackers: Dict[str, 'Compteur2Tracker'] = {}
compteur2_seuil_B = 2
compteur2_active = True

# Compteur1 - Gestion des costumes présents consécutifs
compteur1_trackers: Dict[str, 'Compteur1Tracker'] = {}
compteur1_history: List[Dict] = []
MIN_CONSECUTIVE_FOR_STATS = 3

# Gestion des écarts entre prédictions
MIN_GAP_BETWEEN_PREDICTIONS = 3
last_prediction_number_sent = 0

# Historiques
finalized_messages_history: List[Dict] = []
MAX_HISTORY_SIZE = 50
prediction_history: List[Dict] = []

# File d'attente de prédictions
prediction_queue: List[Dict] = []
PREDICTION_SEND_AHEAD = 2

# Tâches d'animation en cours (original_game → asyncio.Task)
animation_tasks: Dict[int, asyncio.Task] = {}

# Canaux secondaires
DISTRIBUTION_CHANNEL_ID = None
COMPTEUR2_CHANNEL_ID = None

# ============================================================================
# SYSTÈME DE RESTRICTION HORAIRE
# ============================================================================

# Liste de fenêtres (start_hour, end_hour) pendant lesquelles les prédictions sont AUTORISÉES
# Si la liste est vide: pas de restriction
PREDICTION_HOURS: List[Tuple[int, int]] = []

def is_prediction_time_allowed() -> bool:
    """Retourne True si les prédictions sont autorisées à l'heure actuelle."""
    if not PREDICTION_HOURS:
        return True
    now = datetime.now()
    current_min = now.hour * 60 + now.minute
    for (start_h, end_h) in PREDICTION_HOURS:
        start_min = start_h * 60
        end_min = end_h * 60
        if start_min == end_min:
            return True  # Fenêtre nulle = toujours autorisé
        if start_min < end_min:
            if start_min <= current_min < end_min:
                return True
        else:
            # Fenêtre qui passe minuit (ex: 23-0 ou 18-17)
            if current_min >= start_min or current_min < end_min:
                return True
    return False

def format_hours_config() -> str:
    if not PREDICTION_HOURS:
        return "✅ Aucune restriction (prédictions 24h/24)"
    lines = []
    for i, (s, e) in enumerate(PREDICTION_HOURS, 1):
        lines.append(f"  {i}. {s:02d}h00 → {e:02d}h00")
    return "\n".join(lines)

# ============================================================================
# SYSTÈME COMPTEUR4 - ÉCARTS DE 10+
# ============================================================================

COMPTEUR4_THRESHOLD = 10  # Seuil d'absences consécutives
compteur4_trackers: Dict[str, int] = {'♠': 0, '♥': 0, '♦': 0, '♣': 0}
compteur4_events: List[Dict] = []  # Événements enregistrés
compteur4_pdf_msg_id: Optional[int] = None  # ID du message PDF envoyé à l'admin

def generate_compteur4_pdf(events_list: List[Dict]) -> bytes:
    """Génère un PDF avec le tableau des écarts Compteur4."""
    pdf = FPDF()
    pdf.set_auto_page_break(auto=True, margin=15)
    pdf.add_page()

    # Titre
    pdf.set_font('Helvetica', 'B', 16)
    pdf.set_fill_color(30, 30, 30)
    pdf.set_text_color(255, 255, 255)
    pdf.cell(0, 12, 'BACCARAT AI - Ecarts Compteur 4', ln=True, align='C', fill=True)
    pdf.ln(4)

    # Sous-titre
    pdf.set_font('Helvetica', '', 10)
    pdf.set_text_color(100, 100, 100)
    pdf.cell(0, 6, f'Seuil: {COMPTEUR4_THRESHOLD} absences consecutives | Genere le {datetime.now().strftime("%d/%m/%Y %H:%M")}', ln=True, align='C')
    pdf.ln(6)

    # En-tête du tableau
    col_widths = [38, 28, 28, 90]
    headers = ['Date', 'Heure', 'Numero', 'Cartes Joueur']

    pdf.set_font('Helvetica', 'B', 11)
    pdf.set_fill_color(50, 50, 50)
    pdf.set_text_color(255, 255, 255)
    for header, width in zip(headers, col_widths):
        pdf.cell(width, 9, header, border=1, fill=True, align='C')
    pdf.ln()

    # Lignes du tableau
    pdf.set_font('Helvetica', '', 11)
    fill = False
    for i, ev in enumerate(events_list, 1):
        if fill:
            pdf.set_fill_color(240, 240, 240)
            pdf.set_text_color(0, 0, 0)
        else:
            pdf.set_fill_color(255, 255, 255)
            pdf.set_text_color(0, 0, 0)

        date_str = ev['datetime'].strftime('%d/%m/%Y')
        time_str = ev['datetime'].strftime('%H:%M')
        game_str = f"{ev['game_number']:03d}"

        # Représentation des cartes joueur avec noms texte
        suit_names_map = {'♠': 'Pique', '♥': 'Coeur', '♦': 'Carreau', '♣': 'Trefle'}
        cards_display = ' | '.join([suit_names_map.get(s, s) for s in ev.get('player_suits', [])])
        if not cards_display:
            cards_display = '-'

        row = [date_str, time_str, game_str, cards_display]
        for data, width in zip(row, col_widths):
            pdf.cell(width, 8, data, border=1, fill=fill, align='C')
        pdf.ln()
        fill = not fill

    if not events_list:
        pdf.set_text_color(150, 150, 150)
        pdf.cell(0, 8, 'Aucun ecart enregistre', border=1, align='C')
        pdf.ln()

    # Pied de page
    pdf.ln(5)
    pdf.set_font('Helvetica', 'I', 9)
    pdf.set_text_color(120, 120, 120)
    pdf.cell(0, 6, f'Total: {len(events_list)} ecart(s) enregistre(s)', ln=True, align='R')

    return bytes(pdf.output())

async def send_compteur4_pdf():
    """Génère et envoie (ou remplace) le PDF Compteur4 à l'admin."""
    global compteur4_pdf_msg_id

    if not ADMIN_ID or ADMIN_ID == 0:
        logger.warning("⚠️ ADMIN_ID non configuré, PDF non envoyé")
        return

    try:
        pdf_bytes = generate_compteur4_pdf(compteur4_events)
        pdf_buffer = io.BytesIO(pdf_bytes)
        pdf_buffer.name = "compteur4_ecarts.pdf"

        admin_entity = await client.get_entity(ADMIN_ID)

        # Supprimer l'ancien message PDF si il existe
        if compteur4_pdf_msg_id:
            try:
                await client.delete_messages(admin_entity, [compteur4_pdf_msg_id])
                logger.info(f"🗑️ Ancien PDF supprimé (msg {compteur4_pdf_msg_id})")
            except Exception as e:
                logger.warning(f"⚠️ Impossible de supprimer ancien PDF: {e}")
            compteur4_pdf_msg_id = None

        caption = (
            f"📊 **COMPTEUR4 - ÉCARTS (seuil: {COMPTEUR4_THRESHOLD})**\n\n"
            f"Total enregistré: **{len(compteur4_events)}** écart(s)\n"
            f"Mis à jour: {datetime.now().strftime('%d/%m/%Y %H:%M')}"
        )

        sent = await client.send_file(
            admin_entity,
            pdf_buffer,
            caption=caption,
            parse_mode='markdown',
            attributes=[],
            file_name="compteur4_ecarts.pdf"
        )
        compteur4_pdf_msg_id = sent.id
        logger.info(f"✅ PDF Compteur4 envoyé à l'admin (msg {compteur4_pdf_msg_id})")

    except Exception as e:
        logger.error(f"❌ Erreur envoi PDF: {e}")
        import traceback
        logger.error(traceback.format_exc())

def update_compteur4(game_number: int, player_suits: Set[str], player_cards_raw: list) -> List[str]:
    """Met à jour Compteur4. Retourne la liste des costumes ayant atteint le seuil."""
    global compteur4_trackers, compteur4_events

    triggered = []

    for suit in ALL_SUITS:
        if suit in player_suits:
            compteur4_trackers[suit] = 0
        else:
            compteur4_trackers[suit] += 1
            if compteur4_trackers[suit] == COMPTEUR4_THRESHOLD:
                ev = {
                    'datetime': datetime.now(),
                    'game_number': game_number,
                    'suit': suit,
                    'player_suits': list(player_suits),
                }
                compteur4_events.append(ev)
                triggered.append(suit)
                logger.info(f"📊 Compteur4: {suit} absent {COMPTEUR4_THRESHOLD} fois! (jeu #{game_number})")

    return triggered

# ============================================================================
# NORMALISATION DES COSTUMES
# ============================================================================

def normalize_suit(s: str) -> str:
    """Normalise un costume API vers le format interne ('♠', '♥', '♦', '♣')."""
    s = s.strip()
    s = s.replace('\ufe0f', '')  # Retirer le variation selector
    s = s.replace('❤', '♥')
    return s

def get_player_suits(player_cards: list) -> Set[str]:
    """Extrait les costumes normalisés des cartes joueur."""
    suits = set()
    for card in player_cards:
        raw = card.get('S', '')
        normalized = normalize_suit(raw)
        if normalized in ALL_SUITS:
            suits.add(normalized)
    return suits

# ============================================================================
# CLASSES TRACKERS
# ============================================================================

@dataclass
class Compteur2Tracker:
    """Tracker pour le compteur2 (costumes manquants)."""
    suit: str
    counter: int = 0
    last_increment_game: int = 0

    def get_display_name(self) -> str:
        return SUIT_DISPLAY.get(self.suit, self.suit)

    def increment(self, game_number: int):
        self.counter += 1
        self.last_increment_game = game_number
        logger.info(f"📊 Compteur2 {self.suit}: {self.counter} (jeu #{game_number})")

    def reset(self, game_number: int):
        if self.counter > 0:
            logger.info(f"🔄 Compteur2 {self.suit}: reset {self.counter}→0 (jeu #{game_number})")
        self.counter = 0
        self.last_increment_game = 0

    def check_threshold(self, seuil_B: int) -> bool:
        return self.counter >= seuil_B


@dataclass
class Compteur1Tracker:
    """Tracker pour le compteur1 (costumes présents consécutivement)."""
    suit: str
    counter: int = 0
    start_game: int = 0
    last_game: int = 0

    def get_display_name(self) -> str:
        return SUIT_DISPLAY.get(self.suit, self.suit)

    def increment(self, game_number: int):
        if self.counter == 0:
            self.start_game = game_number
        self.counter += 1
        self.last_game = game_number

    def reset(self, game_number: int):
        if self.counter >= MIN_CONSECUTIVE_FOR_STATS:
            save_compteur1_series(self.suit, self.counter, self.start_game, self.last_game)
        self.counter = 0
        self.start_game = 0
        self.last_game = 0

    def get_status(self) -> str:
        if self.counter == 0:
            return "0"
        return f"{self.counter} (depuis #{self.start_game})"

# ============================================================================
# FONCTIONS COMPTEUR1
# ============================================================================

def save_compteur1_series(suit: str, count: int, start_game: int, end_game: int):
    global compteur1_history
    entry = {
        'suit': suit,
        'count': count,
        'start_game': start_game,
        'end_game': end_game,
        'timestamp': datetime.now()
    }
    compteur1_history.insert(0, entry)
    if len(compteur1_history) > 100:
        compteur1_history = compteur1_history[:100]

def get_compteur1_record(suit: str) -> int:
    max_count = 0
    for entry in compteur1_history:
        if entry['suit'] == suit and entry['count'] > max_count:
            max_count = entry['count']
    return max_count

def update_compteur1(game_number: int, player_suits: Set[str]):
    global compteur1_trackers
    for suit in ALL_SUITS:
        tracker = compteur1_trackers[suit]
        if suit in player_suits:
            tracker.increment(game_number)
        else:
            tracker.reset(game_number)

# ============================================================================
# FONCTIONS D'HISTORIQUE
# ============================================================================

def add_to_history(game_number: int, player_suits: Set[str]):
    global finalized_messages_history
    entry = {
        'timestamp': datetime.now(),
        'game_number': game_number,
        'player_suits': list(player_suits),
        'predictions_verified': []
    }
    finalized_messages_history.insert(0, entry)
    if len(finalized_messages_history) > MAX_HISTORY_SIZE:
        finalized_messages_history = finalized_messages_history[:MAX_HISTORY_SIZE]

def add_prediction_to_history(game_number: int, suit: str, verification_games: List[int], prediction_type: str = 'standard'):
    global prediction_history
    prediction_history.insert(0, {
        'predicted_game': game_number,
        'suit': suit,
        'predicted_at': datetime.now(),
        'verification_games': verification_games,
        'status': 'en_cours',
        'verified_at': None,
        'verified_by_game': None,
        'rattrapage_level': 0,
        'type': prediction_type
    })
    if len(prediction_history) > MAX_HISTORY_SIZE:
        prediction_history = prediction_history[:MAX_HISTORY_SIZE]

def update_prediction_in_history(game_number: int, suit: str, verified_by_game: int, rattrapage_level: int, final_status: str):
    global prediction_history
    for pred in prediction_history:
        if pred['predicted_game'] == game_number and pred['suit'] == suit:
            pred['status'] = final_status
            pred['verified_at'] = datetime.now()
            pred['verified_by_game'] = verified_by_game
            pred['rattrapage_level'] = rattrapage_level
            break

# ============================================================================
# INITIALISATION
# ============================================================================

def initialize_trackers():
    global compteur2_trackers, compteur1_trackers, compteur4_trackers
    for suit in ALL_SUITS:
        compteur2_trackers[suit] = Compteur2Tracker(suit=suit)
        compteur1_trackers[suit] = Compteur1Tracker(suit=suit)
        compteur4_trackers[suit] = 0
    logger.info("📊 Trackers initialisés (Compteur1, Compteur2, Compteur4)")

# ============================================================================
# UTILITAIRES CANAL
# ============================================================================

def normalize_channel_id(channel_id) -> int:
    if not channel_id:
        return None
    channel_str = str(channel_id)
    if channel_str.startswith('-100'):
        return int(channel_str)
    if channel_str.startswith('-'):
        return int(channel_str)
    return int(f"-100{channel_str}")

async def resolve_channel(entity_id):
    try:
        if not entity_id:
            return None
        normalized_id = normalize_channel_id(entity_id)
        entity = await client.get_entity(normalized_id)
        return entity
    except Exception as e:
        logger.error(f"❌ Impossible de résoudre le canal {entity_id}: {e}")
        return None

def block_suit(suit: str, minutes: int = 5):
    suit_block_until[suit] = datetime.now() + timedelta(minutes=minutes)
    logger.info(f"🔒 {suit} bloqué {minutes}min")

# ============================================================================
# SYSTÈME D'ANIMATION (BARRE DE CHARGEMENT)
# ============================================================================

BAR_SIZE = 10          # Taille totale de la barre
ANIM_INTERVAL = 3.5    # Secondes entre chaque frame (limite Telegram ~1 édit/3s)

# Amplitude max de la barre selon le niveau de rattrapage
# R0=2, R1=4, R2=7, R3=10
BAR_MAX_BY_RATTRAPAGE = [2, 4, 7, 10]

async def _run_animation(original_game: int, check_game: int, start_frame: int = 0):
    """Boucle d'animation: barre bleue ping-pong dont l'amplitude grandit à chaque rattrapage."""
    global pending_predictions, animation_tasks

    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not prediction_entity:
            return

        frame = start_frame
        while True:
            pred = pending_predictions.get(original_game)
            if not pred or pred.get('status') != 'en_cours':
                break

            msg_id = pred.get('message_id')
            if not msg_id:
                break

            suit = pred['suit']
            suit_display = SUIT_DISPLAY.get(suit, suit)
            rattrapage = pred.get('rattrapage', 0)

            # Amplitude max selon le rattrapage (ping-pong dans cette plage)
            max_fill = BAR_MAX_BY_RATTRAPAGE[min(rattrapage, len(BAR_MAX_BY_RATTRAPAGE) - 1)]
            period = max_fill * 2  # aller-retour complet
            pos = frame % period
            filled = pos if pos <= max_fill else period - pos
            bar = '🟦' * filled + '⬜' * (BAR_SIZE - filled)

            # Petits points animés
            dots = '.' * ((frame % 3) + 1)

            msg = (
                f"🎰 **PRÉDICTION #{original_game}**\n"
                f"🎯 Couleur: {suit_display}\n\n"
                f"🔍 Vérification jeu **#{check_game}**\n"
                f"`{bar}`\n"
                f"⏳ _Analyse{dots}_"
            )

            try:
                await client.edit_message(
                    prediction_entity, msg_id, msg, parse_mode='markdown'
                )
            except Exception as e:
                err = str(e).lower()
                if 'not modified' not in err and 'message_id_invalid' not in err:
                    logger.debug(f"🎬 Edit anim #{original_game}: {e}")

            frame += 1
            await asyncio.sleep(ANIM_INTERVAL)

    except asyncio.CancelledError:
        pass
    except Exception as e:
        logger.debug(f"🎬 Erreur animation #{original_game}: {e}")
    finally:
        animation_tasks.pop(original_game, None)


def start_animation(original_game: int, check_game: int, start_frame: int = 0):
    """Démarre (ou redémarre) l'animation pour une prédiction."""
    stop_animation(original_game)
    task = asyncio.create_task(_run_animation(original_game, check_game, start_frame))
    animation_tasks[original_game] = task
    logger.info(f"🎬 Animation démarrée #{original_game} → vérifie #{check_game} (frame={start_frame})")


def stop_animation(original_game: int):
    """Arrête l'animation d'une prédiction."""
    task = animation_tasks.pop(original_game, None)
    if task and not task.done():
        task.cancel()


def stop_all_animations():
    """Arrête toutes les animations en cours."""
    for game_num in list(animation_tasks.keys()):
        stop_animation(game_num)


# ============================================================================
# GESTION DES PRÉDICTIONS
# ============================================================================

def format_prediction_message(game_number: int, suit: str, status: str = 'en_cours',
                              current_check: int = None, verified_games: List[int] = None,
                              rattrapage: int = 0) -> str:
    suit_display = SUIT_DISPLAY.get(suit, suit)

    if status == 'en_cours':
        verif_parts = []
        for i in range(4):
            check_num = game_number + i
            if current_check == check_num:
                verif_parts.append(f"🔵#{check_num}")
            elif verified_games and check_num in verified_games:
                continue
            else:
                verif_parts.append(f"⬜#{check_num}")
        verif_line = " | ".join(verif_parts)
        return (
            f"🎰 PRÉDICTION #{game_number}\n"
            f"🎯 Couleur: {suit_display}\n"
            f"📊 Statut: En cours ⏳\n"
            f"🔍 Vérification: {verif_line}"
        )

    elif status == 'gagne':
        num_emoji = ['0️⃣', '1️⃣', '2️⃣', '3️⃣']
        badge = num_emoji[rattrapage] if rattrapage < len(num_emoji) else f'{rattrapage}️⃣'
        return (
            f"🏆 **PRÉDICTION #{game_number}**\n\n"
            f"🎯 **Couleur:** {suit_display}\n"
            f"✅ **Statut:** ✅{badge} GAGNÉ"
        )

    elif status == 'perdu':
        return (
            f"💔 **PRÉDICTION #{game_number}**\n\n"
            f"🎯 **Couleur:** {suit_display}\n"
            f"❌ **Statut:** PERDU 😭"
        )

    return ""

async def send_prediction_to_channel(channel_id: int, game_number: int, suit: str,
                                     prediction_type: str, is_secondary: bool = False) -> Optional[int]:
    try:
        if not is_secondary and suit in suit_block_until and datetime.now() < suit_block_until[suit]:
            logger.info(f"🔒 {suit} bloqué, prédiction annulée")
            return None
        if not channel_id:
            return None
        channel_entity = await resolve_channel(channel_id)
        if not channel_entity:
            logger.error(f"❌ Canal {channel_id} inaccessible")
            return None
        msg = format_prediction_message(game_number, suit, 'en_cours', game_number, [])
        sent = await client.send_message(channel_entity, msg, parse_mode='markdown')
        return sent.id
    except ChatWriteForbiddenError:
        logger.error(f"❌ Pas de permission dans {channel_id}")
        return None
    except UserBannedInChannelError:
        logger.error(f"❌ Bot banni de {channel_id}")
        return None
    except Exception as e:
        logger.error(f"❌ Erreur envoi à {channel_id}: {e}")
        return None

async def send_prediction_multi_channel(game_number: int, suit: str, prediction_type: str = 'standard') -> bool:
    global last_prediction_time, last_prediction_number_sent, DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID

    # Vérification restriction horaire
    if not is_prediction_time_allowed():
        logger.info(f"⏰ Heure non autorisée, prédiction #{game_number} bloquée")
        return False

    success = False

    if PREDICTION_CHANNEL_ID:
        if game_number in pending_predictions:
            logger.warning(f"⚠️ #{game_number} déjà dans pending")
            return False

        old_last = last_prediction_number_sent
        last_prediction_number_sent = game_number

        pending_predictions[game_number] = {
            'suit': suit,
            'message_id': None,
            'status': 'sending',
            'type': prediction_type,
            'sent_time': datetime.now(),
            'verification_games': [game_number, game_number + 1, game_number + 2],
            'verified_games': [],
            'found_at': None,
            'rattrapage': 0,
            'current_check': game_number
        }

        msg_id = await send_prediction_to_channel(
            PREDICTION_CHANNEL_ID, game_number, suit, prediction_type, is_secondary=False
        )

        if msg_id:
            last_prediction_time = datetime.now()
            pending_predictions[game_number]['message_id'] = msg_id
            pending_predictions[game_number]['status'] = 'en_cours'
            add_prediction_to_history(game_number, suit, [game_number, game_number + 1, game_number + 2], prediction_type)
            success = True
            logger.info(f"✅ Prédiction #{game_number} {suit} envoyée ({prediction_type})")
            # Démarrer l'animation dès l'envoi
            start_animation(game_number, game_number)

            secondary_channel_id = None
            if prediction_type == 'distribution' and DISTRIBUTION_CHANNEL_ID:
                secondary_channel_id = DISTRIBUTION_CHANNEL_ID
            elif prediction_type == 'compteur2' and COMPTEUR2_CHANNEL_ID:
                secondary_channel_id = COMPTEUR2_CHANNEL_ID

            if secondary_channel_id:
                sec_msg_id = await send_prediction_to_channel(
                    secondary_channel_id, game_number, suit, prediction_type, is_secondary=True
                )
                if sec_msg_id:
                    pending_predictions[game_number]['secondary_message_id'] = sec_msg_id
                    pending_predictions[game_number]['secondary_channel_id'] = secondary_channel_id
        else:
            if game_number in pending_predictions and pending_predictions[game_number]['status'] == 'sending':
                del pending_predictions[game_number]
            last_prediction_number_sent = old_last

    return success

async def update_prediction_message(game_number: int, status: str, rattrapage: int = 0):
    if game_number not in pending_predictions:
        return

    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    new_msg = format_prediction_message(game_number, suit, status, rattrapage=rattrapage)

    if 'gagne' in status:
        logger.info(f"✅ Gagné: #{game_number} (R{rattrapage})")
    else:
        logger.info(f"❌ Perdu: #{game_number}")
        block_suit(suit, 5)

    # Arrêter l'animation AVANT d'éditer le résultat final
    stop_animation(game_number)
    del pending_predictions[game_number]

    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if prediction_entity and msg_id:
            await client.edit_message(prediction_entity, msg_id, new_msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur édition message #{game_number}: {e}")

    sec_msg_id = pred.get('secondary_message_id')
    sec_channel_id = pred.get('secondary_channel_id')
    if sec_msg_id and sec_channel_id:
        try:
            sec_entity = await resolve_channel(sec_channel_id)
            if sec_entity:
                await client.edit_message(sec_entity, sec_msg_id, new_msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Erreur édition canal secondaire #{game_number}: {e}")

async def update_prediction_progress(game_number: int, current_check: int):
    if game_number not in pending_predictions:
        return
    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    verified_games = pred.get('verified_games', [])
    pred['current_check'] = current_check
    # Relancer l'animation depuis le max précédent pour la continuité visuelle
    new_rattrapage = pred.get('rattrapage', 0)
    prev_rattrapage = max(0, new_rattrapage - 1)
    start_frame = BAR_MAX_BY_RATTRAPAGE[min(prev_rattrapage, len(BAR_MAX_BY_RATTRAPAGE) - 1)]
    start_animation(game_number, current_check, start_frame)
    msg = format_prediction_message(game_number, suit, 'en_cours', current_check, verified_games)
    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if prediction_entity:
            await client.edit_message(prediction_entity, msg_id, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur update progress: {e}")

    sec_msg_id = pred.get('secondary_message_id')
    sec_channel_id = pred.get('secondary_channel_id')
    if sec_msg_id and sec_channel_id:
        try:
            sec_entity = await resolve_channel(sec_channel_id)
            if sec_entity:
                await client.edit_message(sec_entity, sec_msg_id, msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Erreur update progress canal secondaire: {e}")

async def check_prediction_result(game_number: int, player_suits: Set[str], is_finished: bool = False) -> bool:
    """
    Vérifie les prédictions en attente contre les cartes joueur.
    - Victoire immédiate si le costume est trouvé (même partie non finie).
    - Échec (rattrapage) uniquement quand la partie est terminée (is_finished=True).
    """

    # Vérification directe (game_number == numéro prédit)
    if game_number in pending_predictions:
        pred = pending_predictions[game_number]
        if pred['status'] != 'en_cours':
            return False
        target_suit = pred['suit']

        # Ne pas re-vérifier si déjà finalisé pour ce jeu
        if game_number in pred['verified_games']:
            return False

        logger.info(f"🔍 Vérif #{game_number} (fini={is_finished}): {target_suit} dans {player_suits}?")

        if target_suit in player_suits:
            # ✅ Costume trouvé → victoire immédiate
            pred['verified_games'].append(game_number)
            await update_prediction_message(game_number, 'gagne', 0)
            update_prediction_in_history(game_number, target_suit, game_number, 0, 'gagne_r0')
            return True
        elif is_finished:
            # ❌ Partie terminée, costume absent → passer au rattrapage
            pred['verified_games'].append(game_number)
            pred['rattrapage'] = 1
            next_check = game_number + 1
            logger.info(f"❌ #{game_number} terminé sans {target_suit}, attente #{next_check}")
            await update_prediction_progress(game_number, next_check)
            return False
        else:
            # ⏳ Partie en cours, costume pas encore là → on re-vérifiera au prochain poll
            logger.debug(f"⏳ #{game_number} en cours, {target_suit} absent pour l'instant")
            return False

    # Vérification rattrapage
    for original_game, pred in list(pending_predictions.items()):
        if pred['status'] != 'en_cours':
            continue
        target_suit = pred['suit']
        rattrapage = pred.get('rattrapage', 0)
        expected_game = original_game + rattrapage

        if game_number == expected_game and rattrapage > 0:
            if game_number in pred['verified_games']:
                return False

            logger.info(f"🔍 Vérif R{rattrapage} #{game_number} (fini={is_finished}): {target_suit} dans {player_suits}?")

            if target_suit in player_suits:
                # ✅ Costume trouvé → victoire immédiate
                pred['verified_games'].append(game_number)
                await update_prediction_message(original_game, 'gagne', rattrapage)
                update_prediction_in_history(original_game, target_suit, game_number, rattrapage, f'gagne_r{rattrapage}')
                return True
            elif is_finished:
                # ❌ Partie terminée, costume absent → rattrapage suivant ou perdu
                pred['verified_games'].append(game_number)
                if rattrapage < 3:
                    pred['rattrapage'] = rattrapage + 1
                    next_check = original_game + rattrapage + 1
                    logger.info(f"❌ R{rattrapage} terminé sans {target_suit}, attente #{next_check}")
                    await update_prediction_progress(original_game, next_check)
                    return False
                else:
                    logger.info(f"❌ R3 terminé sans {target_suit}, prédiction perdue")
                    await update_prediction_message(original_game, 'perdu', 3)
                    update_prediction_in_history(original_game, target_suit, game_number, 3, 'perdu')
                    return False
            else:
                # ⏳ Partie en cours, costume pas encore là → on attend
                logger.debug(f"⏳ R{rattrapage} #{game_number} en cours, {target_suit} absent pour l'instant")
                return False

    return False

# ============================================================================
# GESTION DE LA FILE D'ATTENTE
# ============================================================================

def can_accept_prediction(pred_number: int) -> bool:
    global prediction_queue, pending_predictions, last_prediction_number_sent, MIN_GAP_BETWEEN_PREDICTIONS

    if last_prediction_number_sent > 0:
        gap = pred_number - last_prediction_number_sent
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            return False

    for active_num in pending_predictions:
        gap = abs(pred_number - active_num)
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            return False

    for queued_pred in prediction_queue:
        existing_num = queued_pred['game_number']
        gap = abs(pred_number - existing_num)
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            return False

    return True

def add_to_prediction_queue(game_number: int, suit: str, prediction_type: str) -> bool:
    global prediction_queue

    for pred in prediction_queue:
        if pred['game_number'] == game_number:
            return False

    if not can_accept_prediction(game_number):
        return False

    prediction_queue.append({
        'game_number': game_number,
        'suit': suit,
        'type': prediction_type,
        'added_at': datetime.now()
    })
    prediction_queue.sort(key=lambda x: x['game_number'])
    logger.info(f"📥 #{game_number} ({suit}) en file. Total: {len(prediction_queue)}")
    return True

async def process_prediction_queue(current_game: int):
    global prediction_queue, pending_predictions

    if pending_predictions:
        return

    to_remove = []
    to_send = None

    for pred in list(prediction_queue):
        pred_number = pred['game_number']

        if current_game > pred_number - PREDICTION_SEND_AHEAD:
            logger.warning(f"⏰ #{pred_number} EXPIRÉ (canal #{current_game})")
            to_remove.append(pred)
            continue

        if current_game == pred_number - PREDICTION_SEND_AHEAD:
            to_send = pred
            break

    for pred in to_remove:
        prediction_queue.remove(pred)

    if to_send:
        if pending_predictions:
            return
        pred_number = to_send['game_number']
        suit = to_send['suit']
        pred_type = to_send['type']
        logger.info(f"📤 Envoi depuis file: #{pred_number}")
        success = await send_prediction_multi_channel(pred_number, suit, pred_type)
        if success:
            prediction_queue.remove(to_send)

# ============================================================================
# MISE À JOUR COMPTEUR2
# ============================================================================

def update_compteur2(game_number: int, player_suits: Set[str]):
    global compteur2_trackers
    for suit in ALL_SUITS:
        tracker = compteur2_trackers[suit]
        if suit in player_suits:
            tracker.reset(game_number)
        else:
            tracker.increment(game_number)

def get_compteur2_ready_predictions(current_game: int) -> List[tuple]:
    global compteur2_trackers, compteur2_seuil_B
    ready = []
    for suit in ALL_SUITS:
        tracker = compteur2_trackers[suit]
        if tracker.check_threshold(compteur2_seuil_B):
            pred_number = current_game + 2
            ready.append((suit, pred_number))
            tracker.reset(current_game)
    return ready

# ============================================================================
# TRAITEMENT DES JEUX (API)
# ============================================================================

async def process_game_result(game_number: int, player_suits: Set[str], player_cards_raw: list, is_finished: bool = False):
    """Traite un résultat de jeu venant de l'API 1xBet."""
    global current_game_number, processed_games

    if game_number > current_game_number:
        current_game_number = game_number

    # Vérification dynamique des prédictions
    # Victoire immédiate si costume trouvé, échec seulement si partie terminée
    await check_prediction_result(game_number, player_suits, is_finished)

    # Traiter la file d'attente
    await process_prediction_queue(game_number)

    # Comptabilisation (une seule fois par jeu)
    if game_number not in processed_games:
        processed_games.add(game_number)

        add_to_history(game_number, player_suits)
        update_compteur1(game_number, player_suits)
        update_compteur2(game_number, player_suits)

        # Compteur4: détecter les écarts de 10
        triggered_suits = update_compteur4(game_number, player_suits, player_cards_raw)
        if triggered_suits:
            asyncio.create_task(send_compteur4_pdf())

        # Prédictions Compteur2
        if compteur2_active:
            compteur2_preds = get_compteur2_ready_predictions(game_number)
            for suit, pred_num in compteur2_preds:
                added = add_to_prediction_queue(pred_num, suit, 'compteur2')
                if added:
                    logger.info(f"📊 Compteur2: #{pred_num} {suit} en file")

        logger.info(f"📊 Jeu #{game_number}: joueur {player_suits} | C4={dict(compteur4_trackers)}")

# ============================================================================
# BOUCLE DE POLLING API
# ============================================================================

async def api_polling_loop():
    """Boucle principale: interroge l'API 1xBet et traite les résultats."""
    global game_history

    logger.info("🔄 Démarrage boucle de polling API (toutes les 4s)...")
    loop = asyncio.get_event_loop()

    while True:
        try:
            results = await loop.run_in_executor(None, get_latest_results)

            if results:
                for result in results:
                    game_number = result['game_number']
                    player_cards = result.get('player_cards', [])

                    if not player_cards:
                        continue

                    player_suits = get_player_suits(player_cards)
                    if not player_suits:
                        continue

                    is_finished = result.get('is_finished', False)

                    # Mettre à jour l'historique
                    game_history[game_number] = result

                    # Victoire immédiate si costume trouvé, échec seulement si partie terminée
                    await process_game_result(game_number, player_suits, player_cards, is_finished)

                # Garder l'historique propre (max 500 jeux)
                if len(game_history) > 500:
                    oldest = sorted(game_history.keys())[:100]
                    for k in oldest:
                        game_history.pop(k, None)
            else:
                logger.debug("🔄 API: aucun résultat")

        except Exception as e:
            logger.error(f"❌ Erreur polling API: {e}")

        await asyncio.sleep(4)

# ============================================================================
# RESET ET NETTOYAGE
# ============================================================================

async def cleanup_stale_predictions():
    global pending_predictions
    from config import PREDICTION_TIMEOUT_MINUTES
    now = datetime.now()
    stale = []

    for game_number, pred in list(pending_predictions.items()):
        sent_time = pred.get('sent_time')
        if sent_time:
            age_minutes = (now - sent_time).total_seconds() / 60
            if age_minutes >= PREDICTION_TIMEOUT_MINUTES:
                stale.append(game_number)

    for game_number in stale:
        pred = pending_predictions.get(game_number)
        if pred:
            suit = pred.get('suit', '?')
            logger.warning(f"🧹 #{game_number} ({suit}) expiré (timeout)")
            try:
                prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                if prediction_entity and pred.get('message_id'):
                    suit_display = SUIT_DISPLAY.get(suit, suit)
                    expired_msg = f"⏰ **PRÉDICTION #{game_number}**\n🎯 {suit_display}\n⌛ **EXPIRÉE**"
                    await client.edit_message(prediction_entity, pred['message_id'], expired_msg, parse_mode='markdown')
            except Exception:
                pass
            del pending_predictions[game_number]

async def auto_reset_system():
    while True:
        try:
            await asyncio.sleep(60)
            if pending_predictions:
                await cleanup_stale_predictions()
        except Exception as e:
            logger.error(f"❌ Erreur auto_reset: {e}")
            await asyncio.sleep(60)

async def perform_full_reset(reason: str):
    global pending_predictions, last_prediction_time
    global last_prediction_number_sent, compteur2_trackers, prediction_queue
    global compteur1_trackers, compteur1_history, processed_games, prediction_checked_games

    stats = len(pending_predictions)
    queue_stats = len(prediction_queue)

    for tracker in compteur1_trackers.values():
        if tracker.counter >= MIN_CONSECUTIVE_FOR_STATS:
            save_compteur1_series(tracker.suit, tracker.counter, tracker.start_game, tracker.last_game)

    for tracker in compteur2_trackers.values():
        tracker.counter = 0
        tracker.last_increment_game = 0

    for tracker in compteur1_trackers.values():
        tracker.counter = 0
        tracker.start_game = 0
        tracker.last_game = 0

    for suit in ALL_SUITS:
        compteur4_trackers[suit] = 0

    stop_all_animations()
    pending_predictions.clear()
    prediction_queue.clear()
    processed_games.clear()
    prediction_checked_games.clear()
    last_prediction_time = None
    last_prediction_number_sent = 0
    suit_block_until.clear()

    logger.info(f"🔄 {reason} - {stats} actives, {queue_stats} file cleared")

    if ADMIN_ID and ADMIN_ID != 0:
        try:
            admin_entity = await client.get_entity(ADMIN_ID)
            msg = (
                f"🔄 **RESET SYSTÈME**\n\n"
                f"{reason}\n\n"
                f"✅ {stats} prédictions actives effacées\n"
                f"✅ {queue_stats} prédictions en file effacées\n"
                f"✅ Compteurs remis à zéro\n\n"
                f"🤖 Baccarat AI"
            )
            await client.send_message(admin_entity, msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Impossible de notifier l'admin: {e}")

# ============================================================================
# COMMANDES ADMIN
# ============================================================================

async def cmd_heures(event):
    """Gestion des plages horaires de prédiction."""
    global PREDICTION_HOURS

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    try:
        parts = event.message.message.split()

        if len(parts) == 1:
            now = datetime.now()
            allowed = "✅ OUI" if is_prediction_time_allowed() else "❌ NON"
            await event.respond(
                f"⏰ **RESTRICTION HORAIRE**\n\n"
                f"Heure actuelle: **{now.strftime('%H:%M')}**\n"
                f"Prédictions autorisées: {allowed}\n\n"
                f"**Plages actives:**\n{format_hours_config()}\n\n"
                f"**Usage:**\n"
                f"`/heures add HH-HH` — Ajouter une plage\n"
                f"`/heures del HH-HH` — Supprimer une plage\n"
                f"`/heures clear` — Supprimer toutes les plages (24h/24)"
            )
            return

        sub = parts[1].lower()

        if sub == 'clear':
            PREDICTION_HOURS.clear()
            await event.respond("✅ **Toutes les restrictions horaires supprimées** — prédictions 24h/24")
            return

        if sub == 'add' and len(parts) >= 3:
            raw = parts[2]
            if '-' not in raw:
                await event.respond("❌ Format: HH-HH (ex: `/heures add 18-17`)")
                return
            s_str, e_str = raw.split('-', 1)
            s_h, e_h = int(s_str.strip()), int(e_str.strip())
            if not (0 <= s_h <= 23 and 0 <= e_h <= 23):
                await event.respond("❌ Heures entre 0 et 23")
                return
            PREDICTION_HOURS.append((s_h, e_h))
            await event.respond(
                f"✅ **Plage ajoutée:** {s_h:02d}h00 → {e_h:02d}h00\n\n"
                f"**Plages actives:**\n{format_hours_config()}"
            )
            return

        if sub == 'del' and len(parts) >= 3:
            raw = parts[2]
            if '-' not in raw:
                await event.respond("❌ Format: HH-HH")
                return
            s_str, e_str = raw.split('-', 1)
            s_h, e_h = int(s_str.strip()), int(e_str.strip())
            if (s_h, e_h) in PREDICTION_HOURS:
                PREDICTION_HOURS.remove((s_h, e_h))
                await event.respond(f"✅ **Plage supprimée:** {s_h:02d}h00 → {e_h:02d}h00")
            else:
                await event.respond(f"❌ Plage {s_h:02d}h-{e_h:02d}h introuvable")
            return

        await event.respond(
            "❌ Usage:\n"
            "`/heures` — Voir config\n"
            "`/heures add HH-HH` — Ajouter plage\n"
            "`/heures del HH-HH` — Supprimer plage\n"
            "`/heures clear` — Tout supprimer"
        )

    except ValueError:
        await event.respond("❌ Format invalide. Utilisez des entiers (ex: `/heures add 18-17`)")
    except Exception as e:
        logger.error(f"Erreur cmd_heures: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur4(event):
    """Affiche le statut du Compteur4 et envoie le PDF des écarts."""
    global compteur4_trackers, compteur4_events, COMPTEUR4_THRESHOLD

    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    try:
        parts = event.message.message.split()

        if len(parts) >= 2:
            sub = parts[1].lower()

            if sub == 'seuil' and len(parts) >= 3:
                try:
                    val = int(parts[2])
                    if not 5 <= val <= 50:
                        await event.respond("❌ Seuil entre 5 et 50")
                        return
                    old = COMPTEUR4_THRESHOLD
                    COMPTEUR4_THRESHOLD = val
                    await event.respond(f"✅ **Seuil Compteur4:** {old} → {val}")
                    return
                except ValueError:
                    await event.respond("❌ Usage: `/compteur4 seuil 10`")
                    return

            if sub == 'pdf':
                await event.respond("📄 Génération du PDF en cours...")
                await send_compteur4_pdf()
                return

            if sub == 'reset':
                for suit in ALL_SUITS:
                    compteur4_trackers[suit] = 0
                compteur4_events.clear()
                await event.respond("🔄 **Compteur4 reset** — Compteurs et historique effacés")
                return

        # Affichage statut
        lines = [
            f"📊 **COMPTEUR4 — ÉCARTS** (seuil: {COMPTEUR4_THRESHOLD})",
            f"",
            f"**Absences consécutives actuelles:**",
        ]

        for suit in ALL_SUITS:
            count = compteur4_trackers.get(suit, 0)
            name = SUIT_DISPLAY.get(suit, suit)
            bar_len = min(count, COMPTEUR4_THRESHOLD)
            bar = "█" * bar_len + "░" * (COMPTEUR4_THRESHOLD - bar_len)
            pct = f"{count}/{COMPTEUR4_THRESHOLD}"
            alert = " 🚨" if count >= COMPTEUR4_THRESHOLD else ""
            lines.append(f"{name}: [{bar}] {pct}{alert}")

        lines.append(f"\n**Événements enregistrés:** {len(compteur4_events)}")

        if compteur4_events:
            lines.append(f"\n**Derniers écarts:**")
            for ev in compteur4_events[-5:][::-1]:
                suit_name = SUIT_DISPLAY.get(ev['suit'], ev['suit'])
                dt = ev['datetime'].strftime('%d/%m %H:%M')
                lines.append(f"  • {dt} | #{ev['game_number']:03d} | {suit_name}")

        lines.append(f"\n**Usage:**\n`/compteur4 pdf` — Envoyer le PDF\n`/compteur4 seuil N` — Changer le seuil (actuel: {COMPTEUR4_THRESHOLD})\n`/compteur4 reset` — Réinitialiser")

        await event.respond("\n".join(lines))

    except Exception as e:
        logger.error(f"Erreur cmd_compteur4: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_plus(event):
    global PREDICTION_SEND_AHEAD
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            await event.respond(f"➕ **PRÉDICTION SEND AHEAD**\n\nValeur actuelle: **{PREDICTION_SEND_AHEAD}**\n\n**Usage:** `/plus [1-5]`")
            return
        val = int(parts[1])
        if not 1 <= val <= 5:
            await event.respond("❌ La valeur doit être entre 1 et 5")
            return
        old = PREDICTION_SEND_AHEAD
        PREDICTION_SEND_AHEAD = val
        await event.respond(f"✅ **Send ahead modifié: {old} → {val}**")
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_gap(event):
    global MIN_GAP_BETWEEN_PREDICTIONS
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            await event.respond(f"📏 **ÉCART MINIMUM**\n\nValeur actuelle: **{MIN_GAP_BETWEEN_PREDICTIONS}**\n\n**Usage:** `/gap [2-10]`")
            return
        val = int(parts[1])
        if not 2 <= val <= 10:
            await event.respond("❌ L'écart doit être entre 2 et 10")
            return
        old = MIN_GAP_BETWEEN_PREDICTIONS
        MIN_GAP_BETWEEN_PREDICTIONS = val
        await event.respond(f"✅ **Écart modifié: {old} → {val}**")
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur1(event):
    global compteur1_trackers
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        lines = ["🎯 **COMPTEUR1** (Présences consécutives du joueur)", ""]
        for suit in ALL_SUITS:
            tracker = compteur1_trackers.get(suit)
            if tracker:
                if tracker.counter > 0:
                    lines.append(f"{tracker.get_display_name()}: **{tracker.counter}** consécutifs (depuis #{tracker.start_game})")
                else:
                    lines.append(f"{tracker.get_display_name()}: 0")
        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_stats(event):
    global compteur1_history, compteur1_trackers
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        lines = ["📊 **STATISTIQUES COMPTEUR1**", "Séries de présences consécutives (joueur, min 3)", ""]

        for tracker in compteur1_trackers.values():
            if tracker.counter >= MIN_CONSECUTIVE_FOR_STATS:
                already_saved = any(
                    e['suit'] == tracker.suit and e['count'] == tracker.counter and e['end_game'] == tracker.last_game
                    for e in compteur1_history[:5]
                )
                if not already_saved:
                    save_compteur1_series(tracker.suit, tracker.counter, tracker.start_game, tracker.last_game)

        stats_by_suit = {'♥': [], '♠': [], '♦': [], '♣': []}
        for entry in compteur1_history:
            suit = entry['suit']
            if suit in stats_by_suit:
                stats_by_suit[suit].append(entry)

        has_data = False
        for suit in ['♥', '♠', '♦', '♣']:
            entries = stats_by_suit[suit]
            if not entries:
                continue
            has_data = True
            record = get_compteur1_record(suit)
            lines.append(f"**{SUIT_DISPLAY.get(suit, suit)}** (Record: {record})")
            for i, entry in enumerate(entries[:5], 1):
                count = entry['count']
                start = entry['start_game']
                end = entry['end_game']
                star = "⭐" if count == record else ""
                lines.append(f"  {i}. {count} fois (#{start}-#{end}) {star}")
            lines.append("")

        if not has_data:
            lines.append("❌ Aucune série ≥3 enregistrée")

        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_compteur2(event):
    global compteur2_seuil_B, compteur2_active, compteur2_trackers
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            status_str = "✅ ON" if compteur2_active else "❌ OFF"
            lines = [f"📊 **COMPTEUR2** (Absences joueur)", f"Statut: {status_str} | Seuil B: {compteur2_seuil_B}", "", "Progression:"]
            for suit in ALL_SUITS:
                tracker = compteur2_trackers.get(suit)
                if tracker:
                    progress = min(tracker.counter, compteur2_seuil_B)
                    bar = f"[{'█' * progress}{'░' * (compteur2_seuil_B - progress)}]"
                    status = "🔮 PRÊT" if tracker.counter >= compteur2_seuil_B else f"{tracker.counter}/{compteur2_seuil_B}"
                    lines.append(f"{tracker.get_display_name()}: {bar} {status}")
            lines.append(f"\n**Usage:** `/compteur2 [B/on/off/reset]`")
            await event.respond("\n".join(lines))
            return

        arg = parts[1].lower()
        if arg == 'off':
            compteur2_active = False
            await event.respond("❌ **Compteur2 OFF**")
        elif arg == 'on':
            compteur2_active = True
            await event.respond("✅ **Compteur2 ON**")
        elif arg == 'reset':
            for tracker in compteur2_trackers.values():
                tracker.counter = 0
            await event.respond("🔄 **Compteur2 reset**")
        else:
            b_val = int(arg)
            if not 2 <= b_val <= 10:
                await event.respond("❌ B entre 2 et 10")
                return
            compteur2_seuil_B = b_val
            await event.respond(f"✅ **Seuil B = {b_val}**")
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_canal_distribution(event):
    global DISTRIBUTION_CHANNEL_ID
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            status = f"✅ Actif: `{DISTRIBUTION_CHANNEL_ID}`" if DISTRIBUTION_CHANNEL_ID else "❌ Inactif"
            await event.respond(f"🎯 **CANAL SECONDAIRE COMPTEUR2**\n\n{status}\n\n**Usage:** `/canaldistribution [ID]` ou `/canaldistribution off`")
            return
        arg = parts[1].lower()
        if arg == 'off':
            old = DISTRIBUTION_CHANNEL_ID
            DISTRIBUTION_CHANNEL_ID = None
            await event.respond(f"❌ **Canal secondaire désactivé** (était: `{old}`)")
            return
        new_id = int(arg)
        channel_entity = await resolve_channel(new_id)
        if not channel_entity:
            await event.respond(f"❌ Canal `{new_id}` inaccessible")
            return
        old = DISTRIBUTION_CHANNEL_ID
        DISTRIBUTION_CHANNEL_ID = new_id
        await event.respond(f"✅ **Canal secondaire: {old} → {new_id}**")
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_canal_compteur2(event):
    global COMPTEUR2_CHANNEL_ID
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        parts = event.message.message.split()
        if len(parts) == 1:
            status = f"✅ Actif: `{COMPTEUR2_CHANNEL_ID}`" if COMPTEUR2_CHANNEL_ID else "❌ Inactif"
            await event.respond(f"📊 **CANAL COMPTEUR2**\n\n{status}\n\n**Usage:** `/canalcompteur2 [ID]` ou `/canalcompteur2 off`")
            return
        arg = parts[1].lower()
        if arg == 'off':
            old = COMPTEUR2_CHANNEL_ID
            COMPTEUR2_CHANNEL_ID = None
            await event.respond(f"❌ **Canal Compteur2 désactivé** (était: `{old}`)")
            return
        new_id = int(arg)
        channel_entity = await resolve_channel(new_id)
        if not channel_entity:
            await event.respond(f"❌ Canal `{new_id}` inaccessible")
            return
        old = COMPTEUR2_CHANNEL_ID
        COMPTEUR2_CHANNEL_ID = new_id
        await event.respond(f"✅ **Canal Compteur2: {old} → {new_id}**")
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_canaux(event):
    global DISTRIBUTION_CHANNEL_ID, COMPTEUR2_CHANNEL_ID, PREDICTION_CHANNEL_ID
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    lines = [
        "📡 **CONFIGURATION DES CANAUX**",
        "",
        f"📤 **Principal:** `{PREDICTION_CHANNEL_ID}`",
        f"🎯 **Secondaire Compteur2:** {f'`{DISTRIBUTION_CHANNEL_ID}`' if DISTRIBUTION_CHANNEL_ID else '❌'}",
        f"📊 **Canal Compteur2:** {f'`{COMPTEUR2_CHANNEL_ID}`' if COMPTEUR2_CHANNEL_ID else '❌'}",
    ]
    await event.respond("\n".join(lines))


async def cmd_queue(event):
    global prediction_queue, current_game_number, MIN_GAP_BETWEEN_PREDICTIONS, PREDICTION_SEND_AHEAD
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        lines = [
            "📋 **FILE D'ATTENTE**",
            f"Écart: {MIN_GAP_BETWEEN_PREDICTIONS} | Envoi: N-{PREDICTION_SEND_AHEAD}",
            "",
        ]
        if not prediction_queue:
            lines.append("❌ Vide")
        else:
            lines.append(f"**{len(prediction_queue)} prédictions:**\n")
            for i, pred in enumerate(prediction_queue, 1):
                suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
                pred_type = pred['type']
                pred_num = pred['game_number']
                type_str = "📊C2" if pred_type == 'compteur2' else "🤖"
                send_threshold = pred_num - PREDICTION_SEND_AHEAD
                if current_game_number >= send_threshold:
                    status = "🟢 PRÊT" if not pending_predictions else "⏳ Attente"
                else:
                    wait_num = send_threshold - current_game_number
                    status = f"⏳ Dans {wait_num}"
                lines.append(f"{i}. #{pred_num} {suit} | {type_str} | {status}")
        lines.append(f"\n🎮 Jeu API actuel: #{current_game_number}")
        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {str(e)}")


async def cmd_pending(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    from config import PREDICTION_TIMEOUT_MINUTES
    now = datetime.now()
    try:
        if not pending_predictions:
            await event.respond("✅ **Aucune prédiction en cours**")
            return
        lines = [f"🔍 **PRÉDICTIONS EN COURS** ({len(pending_predictions)})", ""]
        for game_number, pred in pending_predictions.items():
            suit = pred.get('suit', '?')
            suit_display = SUIT_DISPLAY.get(suit, suit)
            rattrapage = pred.get('rattrapage', 0)
            current_check = pred.get('current_check', game_number)
            verified_games = pred.get('verified_games', [])
            sent_time = pred.get('sent_time')
            pred_type = pred.get('type', 'standard')
            type_str = "📊C2" if pred_type == 'compteur2' else "🤖"
            age_str = ""
            if sent_time:
                age_sec = int((now - sent_time).total_seconds())
                age_str = f"{age_sec // 60}m{age_sec % 60:02d}s"
            verif_parts = []
            for i in range(3):
                check_num = game_number + i
                if current_check == check_num:
                    verif_parts.append(f"🔵#{check_num}")
                elif check_num in verified_games:
                    verif_parts.append(f"❌#{check_num}")
                else:
                    verif_parts.append(f"⬜#{check_num}")
            lines.append(f"**#{game_number}** {suit_display} | {type_str} | R{rattrapage}")
            lines.append(f"  🔍 {' | '.join(verif_parts)}")
            lines.append(f"  ⏱️ Il y a {age_str}")
            lines.append("")
        lines.append(f"🎮 Jeu API actuel: #{current_game_number}")
        await event.respond("\n".join(lines))
    except Exception as e:
        await event.respond(f"❌ Erreur: {e}")


async def cmd_history(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    lines = ["📜 **HISTORIQUE PRÉDICTIONS**", ""]
    recent = prediction_history[:10]
    if not recent:
        lines.append("❌ Aucune prédiction")
    else:
        for i, pred in enumerate(recent, 1):
            suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            status = pred['status']
            pred_time = pred['predicted_at'].strftime('%H:%M:%S')
            rule = "📊C2" if pred.get('type') == 'compteur2' else "🤖"
            emoji = {'en_cours': '🎰', 'gagne_r0': '🏆', 'gagne_r1': '🏆', 'gagne_r2': '🏆', 'perdu': '💔'}.get(status, '❓')
            lines.append(f"{i}. {emoji} #{pred['predicted_game']} {suit} | {rule} | {status}")
            lines.append(f"   🕐 {pred_time}")
    await event.respond("\n".join(lines))


async def cmd_status(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return

    compteur2_str = "✅ ON" if compteur2_active else "❌ OFF"
    now = datetime.now()
    allowed = "✅" if is_prediction_time_allowed() else "❌"

    lines = [
        "📊 **STATUT COMPLET**",
        "",
        f"🎮 Jeu API actuel: #{current_game_number}",
        f"📊 Compteur2: {compteur2_str} (B={compteur2_seuil_B})",
        f"📏 Écart: {MIN_GAP_BETWEEN_PREDICTIONS}",
        f"⏰ Prédictions autorisées: {allowed} ({now.strftime('%H:%M')})",
        f"📋 File: {len(prediction_queue)} | Actives: {len(pending_predictions)}",
        f"📊 Écarts C4: {len(compteur4_events)}",
        "",
        f"**Plages horaires:**\n{format_hours_config()}",
        "",
        f"**Compteur4 (absences):**",
    ]

    for suit in ALL_SUITS:
        count = compteur4_trackers.get(suit, 0)
        name = SUIT_DISPLAY.get(suit, suit)
        lines.append(f"  {name}: {count}/{COMPTEUR4_THRESHOLD}")

    if pending_predictions:
        lines.append("")
        lines.append("🔍 **En vérification:**")
        for game_number, pred in pending_predictions.items():
            suit_display = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            rattrapage = pred.get('rattrapage', 0)
            sent_time = pred.get('sent_time')
            age_str = ""
            if sent_time:
                age_sec = int((now - sent_time).total_seconds())
                age_str = f" ({age_sec // 60}m{age_sec % 60:02d}s)"
            lines.append(f"  • #{game_number} {suit_display} — R{rattrapage}{age_str}")

    await event.respond("\n".join(lines))


async def cmd_help(event):
    if event.is_group or event.is_channel:
        return

    help_text = (
        f"📖 **BACCARAT AI - COMMANDES**\n\n"
        f"**⚙️ Configuration:**\n"
        f"`/plus [1-5]` — Envoi en avance (actuel: {PREDICTION_SEND_AHEAD})\n"
        f"`/gap [2-10]` — Écart min entre prédictions ({MIN_GAP_BETWEEN_PREDICTIONS})\n\n"
        f"**⏰ Restriction horaire:**\n"
        f"`/heures` — Voir/gérer les plages\n"
        f"`/heures add HH-HH` — Ajouter une plage\n"
        f"`/heures del HH-HH` — Supprimer une plage\n"
        f"`/heures clear` — 24h/24 sans restriction\n\n"
        f"**📊 Compteurs:**\n"
        f"`/compteur1` — Présences consécutives (joueur)\n"
        f"`/compteur2 [B/on/off/reset]` — Absences consécutives\n"
        f"`/stats` — Historique séries Compteur1\n"
        f"`/compteur4` — Écarts 10+ (avec PDF)\n"
        f"`/compteur4 pdf` — Envoyer le PDF maintenant\n"
        f"`/compteur4 seuil N` — Changer le seuil (actuel: {COMPTEUR4_THRESHOLD})\n\n"
        f"**📡 Canaux:**\n"
        f"`/canaldistribution [ID/off]`\n"
        f"`/canalcompteur2 [ID/off]`\n"
        f"`/canaux` — Voir config\n\n"
        f"**📋 Gestion:**\n"
        f"`/pending` — Prédictions en vérification\n"
        f"`/queue` — File d'attente\n"
        f"`/status` — Statut complet\n"
        f"`/history` — Historique\n"
        f"`/reset` — Reset manuel\n\n"
        f"🤖 Baccarat AI | Source: 1xBet API"
    )
    await event.respond(help_text)


async def cmd_reset(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    await event.respond("🔄 Reset en cours...")
    await perform_full_reset("Reset manuel")
    await event.respond("✅ Reset effectué!")


# ============================================================================
# SETUP ET DÉMARRAGE
# ============================================================================

def setup_handlers():
    client.add_event_handler(cmd_heures, events.NewMessage(pattern=r'^/heures'))
    client.add_event_handler(cmd_compteur4, events.NewMessage(pattern=r'^/compteur4'))
    client.add_event_handler(cmd_plus, events.NewMessage(pattern=r'^/plus'))
    client.add_event_handler(cmd_gap, events.NewMessage(pattern=r'^/gap'))
    client.add_event_handler(cmd_canal_distribution, events.NewMessage(pattern=r'^/canaldistribution'))
    client.add_event_handler(cmd_canal_compteur2, events.NewMessage(pattern=r'^/canalcompteur2'))
    client.add_event_handler(cmd_canaux, events.NewMessage(pattern=r'^/canaux$'))
    client.add_event_handler(cmd_compteur1, events.NewMessage(pattern=r'^/compteur1$'))
    client.add_event_handler(cmd_stats, events.NewMessage(pattern=r'^/stats$'))
    client.add_event_handler(cmd_queue, events.NewMessage(pattern=r'^/queue$'))
    client.add_event_handler(cmd_pending, events.NewMessage(pattern=r'^/pending$'))
    client.add_event_handler(cmd_compteur2, events.NewMessage(pattern=r'^/compteur2'))
    client.add_event_handler(cmd_status, events.NewMessage(pattern=r'^/status$'))
    client.add_event_handler(cmd_history, events.NewMessage(pattern=r'^/history$'))
    client.add_event_handler(cmd_reset, events.NewMessage(pattern=r'^/reset$'))
    client.add_event_handler(cmd_help, events.NewMessage(pattern=r'^/help$'))


async def start_bot():
    global client, prediction_channel_ok

    session = os.getenv('TELEGRAM_SESSION', '')
    client = TelegramClient(StringSession(session), API_ID, API_HASH)

    try:
        await client.start(bot_token=BOT_TOKEN)
        setup_handlers()
        initialize_trackers()

        if PREDICTION_CHANNEL_ID:
            try:
                pred_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                if pred_entity:
                    prediction_channel_ok = True
                    logger.info(f"✅ Canal prédiction OK")
            except Exception as e:
                logger.error(f"❌ Erreur canal prédiction: {e}")

        logger.info("🤖 Bot démarré")
        return True

    except Exception as e:
        logger.error(f"❌ Erreur démarrage: {e}")
        return False


async def main():
    try:
        if not await start_bot():
            return

        asyncio.create_task(auto_reset_system())
        asyncio.create_task(api_polling_loop())

        app = web.Application()
        app.router.add_get('/health', lambda r: web.Response(text="OK"))
        app.router.add_get('/', lambda r: web.Response(text="BACCARAT AI 🤖 Running | Source: 1xBet API"))

        runner = web.AppRunner(app)
        await runner.setup()
        site = web.TCPSite(runner, '0.0.0.0', PORT)
        await site.start()

        logger.info(f"🌐 Web server port {PORT}")
        logger.info(f"📏 Écart: {MIN_GAP_BETWEEN_PREDICTIONS}")
        logger.info(f"📡 Source: 1xBet API (polling toutes les 4s)")
        logger.info(f"📊 Compteur4 seuil: {COMPTEUR4_THRESHOLD}")
        logger.info(f"⏰ Restriction horaire: {'ACTIVE' if PREDICTION_HOURS else 'INACTIVE (24h/24)'}")

        await client.run_until_disconnected()

    except Exception as e:
        logger.error(f"❌ Erreur main: {e}")
    finally:
        if client and client.is_connected():
            await client.disconnect()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Arrêté")
    except Exception as e:
        logger.error(f"Fatal: {e}")
        sys.exit(1)
