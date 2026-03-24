"""
Configuration du bot Baccarat AI
Toutes les valeurs sont lues depuis les variables d'environnement.
Sur Render.com : définir ces variables dans Dashboard > Environment.
"""

import os

# ============================================================================
# TELEGRAM API CREDENTIALS
# Obtenir sur https://my.telegram.org/apps
# ============================================================================

API_ID = int(os.environ.get("API_ID", 0))
API_HASH = os.environ.get("API_HASH", "")
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")

# ============================================================================
# ADMIN ET CANAUX
# ADMIN_ID         : ID Telegram de l'administrateur (reçoit les PDFs, alertes)
# PREDICTION_CHANNEL_ID : ID du canal de prédictions (ex: -1001234567890)
# ============================================================================

ADMIN_ID = int(os.environ.get("ADMIN_ID", 1190237801))
PREDICTION_CHANNEL_ID = int(os.environ.get("PREDICTION_CHANNEL_ID", -1003501017916))

# ============================================================================
# PARAMÈTRES DU SERVEUR WEB
# PORT : 10000 par défaut (valeur attendue par Render.com)
# ============================================================================

PORT = int(os.environ.get("PORT", 10000))

# ============================================================================
# CONFIGURATION COSTUMES
# ============================================================================

ALL_SUITS = ['♠', '♥', '♦', '♣']

SUIT_DISPLAY = {
    '♠': '♠️ Pique',
    '♥': '❤️ Cœur',
    '♦': '♦️ Carreau',
    '♣': '♣️ Trèfle'
}

# ============================================================================
# PARAMÈTRES COMPTEUR2
# ============================================================================

COMPTEUR2_SEUIL_B_DEFAULT = 2
COMPTEUR2_ACTIVE_DEFAULT = True

# ============================================================================
# PARAMÈTRES DE SÉCURITÉ
# ============================================================================

FORCE_RESTART_THRESHOLD = 20
RESET_AT_GAME_NUMBER = 1440
PREDICTION_TIMEOUT_MINUTES = 10

# ============================================================================
# LOGGING
# ============================================================================

LOG_LEVEL = os.environ.get("LOG_LEVEL", "INFO")
