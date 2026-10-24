#!/usr/bin/env python3
"""
Telegram Session Migrator & Bulk Cleaner v100x+ Extreme Industrial
+ 7 параллельных потоков обработки (Semaphore)
+ Авто-прохождение рефералки и фруктовой капчи @GameUGSbot после очистки
+ Карантин проблемных сессий (/failed) с сохранением логов ошибок
+ Поддержка ротации прокси из proxies.txt и парных JSON
+ Безопасное экранирование HTML-сущностей
+ Гарантированное завершение старой сессии через LogOutRequest
"""

from __future__ import annotations

import asyncio
import html
import itertools
import json
import logging
import random
import re
import shutil
import signal
import sqlite3
import tempfile
import time
import uuid
import zipfile
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.filters import Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    Document,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)
from pydantic import Field, field_validator
from pydantic_settings import BaseSettings, SettingsConfigDict
from telethon import TelegramClient
from telethon.errors import (
    AuthKeyUnregisteredError,
    FloodWaitError,
    FreshResetAuthorisationForbiddenError,
    PasswordHashInvalidError,
    PhoneCodeExpiredError,
    PhoneCodeInvalidError,
    PhoneNumberBannedError,
    SessionPasswordNeededError,
    UserDeactivatedError,
)
from telethon.tl.functions.account import (
    ResetWebAuthorizationsRequest,
    SetAccountTTLRequest,
    SetPrivacyRequest,
    UpdateProfileRequest,
    UpdateUsernameRequest,
)
from telethon.tl.functions.auth import LogOutRequest, ResetAuthorizationsRequest
from telethon.tl.functions.channels import (
    DeleteChannelRequest,
    JoinChannelRequest,
    LeaveChannelRequest,
)
from telethon.tl.functions.contacts import (
    BlockRequest,
    DeleteContactsRequest,
    GetContactsRequest,
    ResetSavedRequest,
)
from telethon.tl.functions.messages import (
    ClearAllDraftsRequest,
    DeleteChatUserRequest,
    DeleteHistoryRequest,
    GetAllStickersRequest,
    GetDialogFiltersRequest,
    StartBotRequest,
    UninstallStickerSetRequest,
    UpdateDialogFilterRequest,
)
from telethon.tl.functions.payments import ClearSavedInfoRequest
from telethon.tl.functions.photos import DeletePhotosRequest, GetUserPhotosRequest
from telethon.tl.types import (
    AccountDaysTTL,
    Channel,
    Chat,
    InputPhoto,
    InputPrivacyKeyChatInvite,
    InputPrivacyKeyForwards,
    InputPrivacyKeyPhoneCall,
    InputPrivacyKeyPhoneNumber,
    InputPrivacyKeyProfilePhoto,
    InputPrivacyKeyStatusTimestamp,
    InputPrivacyValueDisallowAll,
    InputStickerSetID,
    User,
)


# ====================== КОНФИГУРАЦИЯ ======================

class Settings(BaseSettings):
    model_config = SettingsConfigDict(env_file=".env", env_file_encoding="utf-8", extra="ignore")

    api_id: int
    api_hash: str
    bot_token: str

    admin_ids: Set[int] = Field(default_factory=set)
    session_timeout_minutes: int = 15
    max_queue_per_user: int = 250
    default_auto_code: int = 6  # 1 = Auto Migrate, 2 = Fast Clean, 0 = Manual
    concurrent_workers_per_chat: int = 7
    db_file: str = "sessions_v100x.db"

    ugs_bot_username: str = "GameUGSbot"
    ugs_ref_param: str = "548858090"
    enable_ugs_referral: bool = True

    proxy_protocol: Optional[str] = None
    proxy_host: Optional[str] = None
    proxy_port: Optional[int] = None
    proxy_username: Optional[str] = None
    proxy_password: Optional[str] = None

    @field_validator("admin_ids", mode="before")
    @classmethod
    def parse_admin_ids(cls, v):
        if v is None:
            return set()
        if isinstance(v, int):
            return {v}
        if isinstance(v, str):
            return {int(x.strip()) for x in v.split(",") if x.strip()}
        if isinstance(v, (list, set, tuple)):
            return {int(x) for x in v}
        return set()

    @property
    def fallback_proxy(self) -> Optional[dict[str, Any]]:
        if self.proxy_host and self.proxy_port and self.proxy_protocol:
            return {
                "proxy_type": self.proxy_protocol.lower(),
                "addr": self.proxy_host,
                "port": self.proxy_port,
                "username": self.proxy_username,
                "password": self.proxy_password,
            }
        return None


settings = Settings()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-8s | %(name)s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("IndustrialWiper")


# ====================== ПУЛ ПРОКСИ И ОТПЕЧАТКОВ ======================

FINGERPRINTS = [
    {"device": "MacBook Pro 16", "sys": "macOS 14.5", "app": "5.4.1 x64", "lang": "en"},
    {"device": "Lenovo ThinkPad X1", "sys": "Windows 11 Pro", "app": "5.4.0 x64", "lang": "en"},
    {"device": "ASUS ROG Zephyrus", "sys": "Windows 10 Enterprise", "app": "5.3.8 x64", "lang": "en"},
    {"device": "Dell XPS 15", "sys": "Ubuntu 24.04 LTS", "app": "5.3.9 x64", "lang": "en"},
    {"device": "Surface Laptop Studio", "sys": "Windows 11 Home", "app": "5.4.1 x64", "lang": "en"},
    {"device": "HP Spectre x360", "sys": "Windows 11 Pro", "app": "5.4.0 x64", "lang": "en"},
]


def get_random_fingerprint() -> dict[str, str]:
    return random.choice(FINGERPRINTS)


class ProxyPool:
    def __init__(self, file_path: str = "proxies.txt"):
        self.file_path = Path(file_path)
        self.proxies: List[dict] = []
        self._cycle = None
        self.load_proxies()

    def load_proxies(self):
        if not self.file_path.exists():
            return
        loaded = []
        try:
            for line in self.file_path.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                parsed = self._parse_line(line)
                if parsed:
                    loaded.append(parsed)
        except Exception as e:
            logger.warning(f"Ошибка чтения proxies.txt: {e}")

        self.proxies = loaded
        if self.proxies:
            self._cycle = itertools.cycle(self.proxies)

    def _parse_line(self, line: str) -> Optional[dict]:
        try:
            if "://" in line:
                proto, rest = line.split("://", 1)
                auth, host_port = rest.split("@") if "@" in rest else (None, rest)
                host, port = host_port.split(":")
                user, password = auth.split(":") if auth else (None, None)
                return {
                    "proxy_type": proto.lower(),
                    "addr": host,
                    "port": int(port),
                    "username": user,
                    "password": password,
                }
            parts = line.split(":")
            if len(parts) == 4:
                return {
                    "proxy_type": "socks5",
                    "addr": parts[0],
                    "port": int(parts[1]),
                    "username": parts[2],
                    "password": parts[3],
                }
            elif len(parts) == 2:
                return {
                    "proxy_type": "socks5",
                    "addr": parts[0],
                    "port": int(parts[1]),
                    "username": None,
                    "password": None,
                }
        except Exception:
            return None
        return None

    def get_next_proxy(self) -> Optional[dict]:
        if not self._cycle:
            return None
        return next(self._cycle)


proxy_pool = ProxyPool("proxies.txt")


# ====================== КАРАНТИН ПРОБЛЕМНЫХ СЕССИЙ ======================

def save_to_quarantine(chat_id: int, session_path: Path, original_name: str, reason: str):
    q_dir = Path("quarantine") / str(chat_id)
    q_dir.mkdir(parents=True, exist_ok=True)
    safe_name = Path(original_name).name
    dest = q_dir / safe_name
    try:
        if session_path and session_path.exists():
            shutil.copy(session_path, dest)
        log_file = dest.with_suffix(".error.txt")
        log_file.write_text(
            f"Файл: {safe_name}\nПричина: {reason}\nВремя: {datetime.now().isoformat()}\n",
            encoding="utf-8",
        )
    except Exception as e:
        logger.error(f"Не удалось сохранить сессию в карантин: {e}")


def count_quarantine(chat_id: int) -> int:
    q_dir = Path("quarantine") / str(chat_id)
    if not q_dir.exists():
        return 0
    return len(list(q_dir.glob("*.session")))


# ====================== БАЗА ДАННЫХ SQLITE ======================

class Database:
    def __init__(self, db_path: str):
        self.db_path = db_path
        self._init_db()

    def _init_db(self):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS queue (
                    id TEXT PRIMARY KEY,
                    chat_id INTEGER,
                    file_path TEXT,
                    original_name TEXT,
                    auto_2fa TEXT,
                    proxy_json TEXT,
                    status TEXT,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                )
            """)
            conn.execute("""
                CREATE TABLE IF NOT EXISTS settings (
                    chat_id INTEGER PRIMARY KEY,
                    auto_mode INTEGER DEFAULT 1
                )
            """)
            conn.commit()

    def add_queue_item(
        self,
        item_id: str,
        chat_id: int,
        file_path: str,
        original_name: str,
        auto_2fa: Optional[str],
        proxy_dict: Optional[dict],
    ):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                "INSERT INTO queue (id, chat_id, file_path, original_name, auto_2fa, proxy_json, status) VALUES (?, ?, ?, ?, ?, ?, 'pending')",
                (item_id, chat_id, file_path, original_name, auto_2fa, json.dumps(proxy_dict) if proxy_dict else None),
            )
            conn.commit()

    def pop_next_item(self, chat_id: int) -> Optional[dict]:
        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            cur = conn.cursor()
            cur.execute(
                "SELECT * FROM queue WHERE chat_id = ? AND status = 'pending' ORDER BY created_at ASC LIMIT 1",
                (chat_id,),
            )
            row = cur.fetchone()
            if row:
                cur.execute("UPDATE queue SET status = 'processing' WHERE id = ?", (row["id"],))
                conn.commit()
                return dict(row)
        return None

    def remove_item(self, item_id: str):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("DELETE FROM queue WHERE id = ?", (item_id,))
            conn.commit()

    def clear_chat_queue(self, chat_id: int) -> List[str]:
        files_to_remove = []
        with sqlite3.connect(self.db_path) as conn:
            conn.row_factory = sqlite3.Row
            cur = conn.cursor()
            cur.execute("SELECT file_path FROM queue WHERE chat_id = ?", (chat_id,))
            files_to_remove = [r["file_path"] for r in cur.fetchall()]
            cur.execute("DELETE FROM queue WHERE chat_id = ?", (chat_id,))
            conn.commit()
        return files_to_remove

    def count_queue(self, chat_id: int) -> int:
        with sqlite3.connect(self.db_path) as conn:
            cur = conn.cursor()
            cur.execute("SELECT COUNT(*) FROM queue WHERE chat_id = ? AND status = 'pending'", (chat_id,))
            return cur.fetchone()[0]

    def set_clean_mode(self, chat_id: int, mode: int):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("INSERT OR REPLACE INTO settings (chat_id, auto_mode) VALUES (?, ?)", (chat_id, mode))
            conn.commit()

    def get_clean_mode(self, chat_id: int, default: int = 1) -> int:
        with sqlite3.connect(self.db_path) as conn:
            cur = conn.cursor()
            cur.execute("SELECT auto_mode FROM settings WHERE chat_id = ?", (chat_id,))
            row = cur.fetchone()
            return int(row[0]) if row is not None else default


db = Database(settings.db_file)


# ====================== МОДЕЛИ ДАННЫХ ======================

class MigrateStates(StatesGroup):
    waiting_phone = State()
    waiting_password = State()
    waiting_manual_code = State()


@dataclass
class SessionCheckResult:
    is_valid: bool
    status: str
    user_id: Optional[int] = None
    phone: Optional[str] = None
    username: Optional[str] = None
    error: Optional[str] = None


@dataclass
class CleanReport:
    profile_cleared: bool = False
    username_cleared: bool = False
    photos_deleted: int = 0
    contacts_deleted: int = 0
    saved_contacts_reset: bool = False
    folders_deleted: int = 0
    stickers_removed: int = 0
    channels_deleted: int = 0
    dialogs_purged: int = 0
    saved_messages_cleared: bool = False
    privacy_secured: bool = False
    payments_cleared: bool = False
    ttl_set_30d: bool = False
    drafts_cleared: bool = False
    web_auths_reset: bool = False
    sessions_reset: bool = False
    sessions_reset_warning: Optional[str] = None
    ugs_referral_done: bool = False


@dataclass
class ActiveMigration:
    id: str
    chat_id: int
    original_name: str = "session.session"
    source_file_path: Optional[Path] = None
    old_client: Optional[TelegramClient] = None
    new_client: Optional[TelegramClient] = None
    phone: str = ""
    phone_code_hash: str = ""
    auto_2fa_password: Optional[str] = None
    proxy_config: Optional[dict] = None
    fingerprint: dict[str, str] = field(default_factory=get_random_fingerprint)
    temp_dir: Optional[Path] = None
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: float = field(default_factory=time.time)
    status_message: Optional[Message] = None
    waiting_2fa: bool = False
    waiting_manual_code: bool = False
    skip_requested: bool = False
    is_new_session: bool = False
    queue_db_id: Optional[str] = None
    old_session_terminated: bool = False
    old_session_error: Optional[str] = None


chat_semaphores: Dict[int, asyncio.Semaphore] = {}
current_migration: Dict[int, ActiveMigration] = {}
current_migrations_by_chat: Dict[int, Dict[str, ActiveMigration]] = {}
queue_workers: Dict[int, bool] = {}

stats = {"started": 0, "success": 0, "failed": 0, "cancelled": 0, "skipped": 0}


def register_active_migration(mig: ActiveMigration):
    current_migration[mig.chat_id] = mig
    current_migrations_by_chat.setdefault(mig.chat_id, {})[mig.id] = mig


def unregister_active_migration(mig: ActiveMigration):
    chat_map = current_migrations_by_chat.get(mig.chat_id)
    if chat_map and mig.id in chat_map:
        del chat_map[mig.id]
        if not chat_map:
            current_migrations_by_chat.pop(mig.chat_id, None)

    current = current_migration.get(mig.chat_id)
    if current and current.id == mig.id:
        remaining = current_migrations_by_chat.get(mig.chat_id)
        if remaining:
            current_migration[mig.chat_id] = next(iter(remaining.values()))
        else:
            current_migration.pop(mig.chat_id, None)


# ====================== УТИЛИТЫ И ПРОВЕРКИ ======================


def get_chat_semaphore(chat_id: int) -> asyncio.Semaphore:
    if chat_id not in chat_semaphores:
        chat_semaphores[chat_id] = asyncio.Semaphore(settings.concurrent_workers_per_chat)
    return chat_semaphores[chat_id]


async def verify_proxy_alive(proxy: dict, timeout: float = 3.0) -> bool:
    host = proxy.get("addr")
    port = proxy.get("port")
    if not host or not port:
        return False
    try:
        conn = asyncio.open_connection(host, port)
        reader, writer = await asyncio.wait_for(conn, timeout=timeout)
        writer.close()
        await writer.wait_closed()
        return True
    except Exception:
        return False


def resolve_proxy(item_proxy_json: Optional[str]) -> Optional[dict]:
    if item_proxy_json:
        try:
            p = json.loads(item_proxy_json)
            if p:
                return p
        except Exception:
            pass
    pooled = proxy_pool.get_next_proxy()
    if pooled:
        return pooled
    return settings.fallback_proxy


def render_progress_bar(current: int, total: int, length: int = 10) -> str:
    ratio = min(1.0, max(0.0, current / total)) if total > 0 else 0.0
    filled = int(length * ratio)
    return "█" * filled + "░" * (length - filled) + f" {int(ratio * 100)}%"


class StatusReporter:
    def __init__(self, message: Message, interval: float = 1.5):
        self.message = message
        self.interval = interval
        self.last_update = 0.0
        self.last_text = ""

    async def update(self, text: str, force: bool = False, reply_markup: Optional[InlineKeyboardMarkup] = None):
        now = time.time()
        if not force and (now - self.last_update < self.interval or text == self.last_text):
            return
        try:
            await self.message.edit_text(text, reply_markup=reply_markup)
            self.last_update = now
            self.last_text = text
        except Exception:
            pass


def extract_telegram_code(text: str) -> Optional[str]:
    if not text:
        return None
    clean = text.replace("\u200b", "").replace("\u200c", "").replace("\xa0", " ")
    match = re.search(
        r"(?i)(?:code|код|c[oó]digo|passcode|kod|login code)[\D]{0,10}(\d[\d\s\-]{3,6}\d)",
        clean,
    )
    if match:
        digits = re.sub(r"\D", "", match.group(1))
        if 4 <= len(digits) <= 8 and digits != "777000":
            return digits

    for num in re.findall(r"\b\d{5,6}\b", clean):
        if num != "777000":
            return num
    return None


def parse_session_proxy(json_data: dict) -> Optional[dict]:
    p = json_data.get("proxy")
    if isinstance(p, dict):
        proto = p.get("type") or p.get("protocol") or "socks5"
        host = p.get("host") or p.get("addr") or p.get("ip")
        port = p.get("port", 1080)
        if host and port:
            return {
                "proxy_type": proto.lower(),
                "addr": host,
                "port": int(port),
                "username": p.get("user") or p.get("username"),
                "password": p.get("pass") or p.get("password"),
            }
    elif isinstance(p, str) and "://" in p:
        return proxy_pool._parse_line(p)
    return None


def get_configured_client(session_target: Any, fp: dict[str, str], proxy: Optional[dict] = None) -> TelegramClient:
    active_proxy = proxy or settings.fallback_proxy
    return TelegramClient(
        session_target,
        settings.api_id,
        settings.api_hash,
        proxy=active_proxy,
        device_model=fp["device"],
        system_version=fp["sys"],
        app_version=fp["app"],
        lang_code=fp["lang"],
        system_lang_code=fp["lang"],
    )


def is_admin(user_id: int) -> bool:
    return user_id in settings.admin_ids


def main_menu_kb(chat_id: int) -> InlineKeyboardMarkup:
    current_mode = db.get_clean_mode(chat_id, settings.default_auto_code)
    if current_mode == 1:
        mode_label = "🔄 Миграция (Авто-код)"
    elif current_mode == 2:
        mode_label = "⚡ Fast Clean (без кодов)"
    else:
        mode_label = "📝 Миграция (Ручной код)"

    failed_cnt = count_quarantine(chat_id)
    failed_label = f"📦 Битые сессии ({failed_cnt})" if failed_cnt > 0 else "📦 Битые сессии (0)"

    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text=f"Режим: {mode_label}", callback_data="cycle_clean_mode"),
            InlineKeyboardButton(text="📱 Сессия с нуля", callback_data="btn_new_session"),
        ],
        [
            InlineKeyboardButton(text=failed_label, callback_data="export_failed"),
            InlineKeyboardButton(text="❌ Сбросить очередь", callback_data="cancel_all"),
        ],
    ])


def action_kb(can_skip: bool = True) -> InlineKeyboardMarkup:
    buttons = []
    if can_skip:
        buttons.append(InlineKeyboardButton(text="⏭ Пропустить эту", callback_data="skip_current"))
    buttons.append(InlineKeyboardButton(text="❌ Отменить всё", callback_data="cancel_all"))
    return InlineKeyboardMarkup(inline_keyboard=[buttons])


# ====================== АВТО-РЕФЕРАЛКА И КАПЧА @GameUGSbot ======================

async def auto_ugs_referral(client: TelegramClient, ref_param: str = "8983649078") -> bool:
    """
    Заходит с аккаунта в @GameUGSbot по рефералке,
    подписывается на обязательные каналы из текста и нажимает на загаданный фрукт в капче.
    """
    if not settings.enable_ugs_referral:
        return False

    bot_username = settings.ugs_bot_username
    try:
        bot_entity = await client.get_entity(bot_username)
        await client(
            StartBotRequest(
                bot=bot_entity,
                peer=bot_entity,
                start_param=ref_param,
                random_id=random.randint(1, 2**63 - 1),
            )
        )

        await asyncio.sleep(3.5)

        messages = await client.get_messages(bot_entity, limit=4)
        captcha_msg = None
        for m in messages:
            if m.buttons and m.raw_text:
                captcha_msg = m
                break

        if not captcha_msg:
            logger.warning("Сообщение с капчей от @GameUGSbot не найдено.")
            return False

        text = captcha_msg.raw_text

        # Извлекаем все @каналы из сообщения и подписываемся на них
        channels = re.findall(r"@([a-zA-Z0-9_]{4,32})", text)
        for ch_username in channels:
            if ch_username.lower() == bot_username.lower():
                continue
            try:
                await client(JoinChannelRequest(ch_username))
                logger.info(f"Подписались на @{ch_username}")
                await asyncio.sleep(random.uniform(1.8, 3.2))
            except FloodWaitError as e:
                await asyncio.sleep(min(e.seconds + 1, 30))
            except Exception as e:
                logger.warning(f"Не удалось подписаться на @{ch_username}: {e}")

        # Ищем кнопку с фруктом, который указан в тексте сообщения
        for row in captcha_msg.buttons:
            for button in row:
                btn_emoji = (button.text or "").strip()
                if btn_emoji and btn_emoji in text:
                    logger.info(f"Найден фрукт капчи: {btn_emoji}. Нажимаем кнопку...")
                    await asyncio.sleep(random.uniform(1.0, 2.0))
                    await button.click()
                    await asyncio.sleep(1.5)
                    return True

        logger.warning("Не удалось сопоставить эмодзи фрукта с кнопками.")
        return False

    except Exception as e:
        logger.warning(f"Ошибка при прохождении @GameUGSbot: {e}")
        return False


# ====================== ДЕАВТОРИЗАЦИЯ СТАРОЙ СЕССИИ ======================

async def terminate_old_session(old_client: Optional[TelegramClient]) -> Tuple[bool, Optional[str]]:
    if not old_client:
        return True, None

    last_error = None
    for attempt in range(1, 4):
        try:
            if not old_client.is_connected():
                await old_client.connect()

            if not await old_client.is_user_authorized():
                logger.info("Старая сессия уже сброшена сервером Telegram.")
                await old_client.disconnect()
                return True, None

            await old_client(LogOutRequest())
            logger.info(f"Старая сессия успешно завершена на попытке {attempt}.")

            try:
                await old_client.disconnect()
            except Exception:
                pass
            return True, None

        except Exception as e:
            last_error = str(e)
            logger.warning(f"Ошибка при выходе из старой сессии (попытка {attempt}/3): {e}")
            try:
                await old_client.disconnect()
            except Exception:
                pass
            await asyncio.sleep(1.0)

    return False, last_error


async def cleanup_migration(mig: ActiveMigration, state: Optional[FSMContext] = None):
    chat_id = mig.chat_id

    if chat_id in current_migration and current_migration[chat_id].id == mig.id:
        del current_migration[chat_id]

    if mig.queue_db_id:
        db.remove_item(mig.queue_db_id)

    for client in (mig.old_client, mig.new_client):
        if client:
            try:
                if client.is_connected():
                    await client.disconnect()
            except Exception:
                pass

    if mig.temp_dir and mig.temp_dir.exists():
        shutil.rmtree(mig.temp_dir, ignore_errors=True)

    if state and (mig.waiting_2fa or mig.waiting_manual_code):
        await state.clear()

    unregister_active_migration(mig)


async def clear_user_queue(chat_id: int, state: Optional[FSMContext] = None):
    if chat_id in current_migration:
        await cleanup_migration(current_migration[chat_id], state)

    files_to_delete = db.clear_chat_queue(chat_id)
    for f in files_to_delete:
        try:
            p = Path(f)
            if p.exists():
                p.unlink(missing_ok=True)
                if any(p.parent.name.startswith(x) for x in ("upload_", "fast_", "mig_")):
                    shutil.rmtree(p.parent, ignore_errors=True)
        except Exception:
            pass

    queue_workers[chat_id] = False
    if state:
        await state.clear()


# ====================== ЭКСТРЕМАЛЬНАЯ ОЧИСТКА ======================

async def deep_clean_account(client: TelegramClient, reporter: StatusReporter) -> CleanReport:
    report = CleanReport()

    # 1. Профиль и @username
    await reporter.update(f"🧹 Сброс профиля...\n{render_progress_bar(1, 10)}", force=True)
    try:
        await client(UpdateProfileRequest(first_name=".", last_name="", about=""))
        report.profile_cleared = True
    except Exception as e:
        logger.warning(f"Ошибка сброса профиля: {e}")

    try:
        me = await client.get_me()
        if getattr(me, "username", None):
            await client(UpdateUsernameRequest(username=""))
            report.username_cleared = True
    except Exception as e:
        logger.warning(f"Ошибка удаления username: {e}")

    # 2. Аватарки
    await reporter.update(f"🧹 Удаление фото профиля...\n{render_progress_bar(2, 10)}")
    try:
        photos = await client(GetUserPhotosRequest(user_id="me", offset=0, max_id=0, limit=200))
        if photos.photos:
            input_photos = [
                InputPhoto(id=p.id, access_hash=p.access_hash, file_reference=p.file_reference)
                for p in photos.photos
            ]
            await client(DeletePhotosRequest(id=input_photos))
            report.photos_deleted = len(input_photos)
    except Exception as e:
        logger.warning(f"Ошибка удаления фото: {e}")

    # 3. Privacy Lockdown
    await reporter.update(f"🔒 Сброс приватности...\n{render_progress_bar(3, 10)}")
    try:
        disallow = [InputPrivacyValueDisallowAll()]
        await client(SetPrivacyRequest(key=InputPrivacyKeyPhoneNumber(), rules=disallow))
        await client(SetPrivacyRequest(key=InputPrivacyKeyStatusTimestamp(), rules=disallow))
        await client(SetPrivacyRequest(key=InputPrivacyKeyProfilePhoto(), rules=disallow))
        await client(SetPrivacyRequest(key=InputPrivacyKeyForwards(), rules=disallow))
        await client(SetPrivacyRequest(key=InputPrivacyKeyPhoneCall(), rules=disallow))
        await client(SetPrivacyRequest(key=InputPrivacyKeyChatInvite(), rules=disallow))
        report.privacy_secured = True
    except Exception as e:
        logger.warning(f"Ошибка параметров приватности: {e}")

    # 4. Платежные реквизиты
    try:
        await client(ClearSavedInfoRequest(credentials=True, info=True))
        report.payments_cleared = True
    except Exception as e:
        logger.debug(f"Платежные данные отсутствуют: {e}")

    # 5. Установка TTL аккаунта (30 дней)
    try:
        await client(SetAccountTTLRequest(ttl=AccountDaysTTL(days=30)))
        report.ttl_set_30d = True
    except Exception as e:
        logger.debug(f"TTL не обновлен: {e}")

    # 6. Контакты и облачный поисковый граф
    await reporter.update(f"🧹 Стирание контактов...\n{render_progress_bar(4, 10)}")
    try:
        contacts_res = await client(GetContactsRequest(hash=0))
        users = getattr(contacts_res, "users", [])
        if users:
            await client(DeleteContactsRequest(id=users))
            report.contacts_deleted = len(users)
        await client(ResetSavedRequest())
        report.saved_contacts_reset = True
    except Exception as e:
        logger.warning(f"Ошибка удаления контактов: {e}")

    # 7. Папки чатов
    await reporter.update(f"🧹 Удаление папок...\n{render_progress_bar(5, 10)}")
    try:
        filters = await client(GetDialogFiltersRequest())
        for f in getattr(filters, "filters", []):
            fid = getattr(f, "id", None)
            if fid is not None and fid != 0:
                await client(UpdateDialogFilterRequest(id=fid, filter=None))
                report.folders_deleted += 1
    except Exception as e:
        logger.warning(f"Ошибка папок: {e}")

    # 8. Стикеры и эмодзи-паки
    try:
        stickers = await client(GetAllStickersRequest(hash=0))
        for sset in getattr(stickers, "sets", []):
            try:
                await client(
                    UninstallStickerSetRequest(
                        stickerset=InputStickerSetID(id=sset.id, access_hash=sset.access_hash)
                    )
                )
                report.stickers_removed += 1
            except Exception:
                pass
    except Exception as e:
        logger.warning(f"Ошибка стикеров: {e}")

    # 9. Черновики и Избранное
    try:
        await client(ClearAllDraftsRequest())
        report.drafts_cleared = True
    except Exception:
        pass

    try:
        await client(DeleteHistoryRequest(peer="me", max_id=0, just_clear=False, revoke=True))
        report.saved_messages_cleared = True
    except Exception as e:
        logger.warning(f"Очистка Избранного: {e}")

    # 10. Диалоги, каналы, группы и боты
    await reporter.update(f"🧹 Тотальная зачистка чатов...\n{render_progress_bar(7, 10)}", force=True)
    async for dialog in client.iter_dialogs():
        entity = dialog.entity
        try:
            if isinstance(entity, Channel):
                if getattr(entity, "creator", False):
                    try:
                        await client(DeleteChannelRequest(channel=entity))
                        report.channels_deleted += 1
                    except Exception:
                        await client(LeaveChannelRequest(entity))
                else:
                    await client(LeaveChannelRequest(entity))
                report.dialogs_purged += 1

            elif isinstance(entity, Chat):
                await client(DeleteChatUserRequest(chat_id=entity.id, user_id="me"))
                report.dialogs_purged += 1

            elif isinstance(entity, User):
                if getattr(entity, "is_self", False):
                    continue
                if getattr(entity, "bot", False):
                    try:
                        await client(BlockRequest(id=entity))
                    except Exception:
                        pass
                try:
                    await client(DeleteHistoryRequest(peer=entity, max_id=0, just_clear=False, revoke=True))
                except Exception:
                    await client.delete_dialog(entity)
                report.dialogs_purged += 1

            if report.dialogs_purged % 10 == 0:
                await reporter.update(
                    f"🧹 Очищено диалогов: <b>{report.dialogs_purged}</b>\n"
                    f"{render_progress_bar(8, 10)}"
                )
                await asyncio.sleep(0.8)
            else:
                await asyncio.sleep(0.15)

        except FloodWaitError as e:
            await reporter.update(f"⏳ FloodWait: ожидание {e.seconds} с...", force=True)
            await asyncio.sleep(e.seconds + 1)
        except Exception:
            continue

    try:
        await client(ResetWebAuthorizationsRequest())
        report.web_auths_reset = True
    except Exception:
        pass

    await reporter.update(f"✅ Финал очистки!\n{render_progress_bar(10, 10)}", force=True)
    return report


# ====================== БЫСТРЫЙ ЧЕКЕР + ОЧИСТКА (6 ПОТОКОВ) ======================

async def quick_check_session_fast(client: TelegramClient, timeout: float = 6.0) -> SessionCheckResult:
    try:
        async def _connect_and_auth():
            if not client.is_connected():
                await client.connect()

            if not await client.is_user_authorized():
                return SessionCheckResult(is_valid=False, status="UNAUTHORIZED", error="Сессия не авторизована")

            me = await client.get_me()
            if not me:
                return SessionCheckResult(is_valid=False, status="DEACTIVATED", error="Аккаунт деактивирован")

            phone = f"+{me.phone}" if me.phone and not str(me.phone).startswith("+") else str(me.phone or "")
            return SessionCheckResult(
                is_valid=True,
                status="ACTIVE",
                user_id=me.id,
                phone=phone,
                username=me.username,
            )

        return await asyncio.wait_for(_connect_and_auth(), timeout=timeout)

    except asyncio.TimeoutError:
        return SessionCheckResult(is_valid=False, status="TIMEOUT", error=f"Таймаут подключения (&gt;{timeout}s)")
    except PhoneNumberBannedError:
        return SessionCheckResult(is_valid=False, status="BANNED", error="Номер заблокирован в Telegram")
    except UserDeactivatedError:
        return SessionCheckResult(is_valid=False, status="DEACTIVATED", error="Аккаунт удален")
    except AuthKeyUnregisteredError:
        return SessionCheckResult(is_valid=False, status="KEY_REVOKED", error="Ключ авторизации отозван")
    except Exception as e:
        return SessionCheckResult(is_valid=False, status="ERROR", error=str(e))


async def process_fast_clean_session(item: dict, bot: Bot, state: Optional[FSMContext] = None):
    chat_id = item["chat_id"]
    mig_id = str(uuid.uuid4())[:8]
    orig_name = item["original_name"]

    status = await bot.send_message(
        chat_id,
        f"⚡ <b>[Fast Clean]</b> Проверка: <code>{html.escape(orig_name)}</code>...",
        reply_markup=action_kb(can_skip=True),
    )
    reporter = StatusReporter(status, interval=1.2)

    temp_dir = Path(tempfile.mkdtemp(prefix=f"fast_{chat_id}_{mig_id}_"))
    session_copy = temp_dir / "target.session"
    shutil.copy(item["file_path"], session_copy)

    proxy_dict = resolve_proxy(item.get("proxy_json"))
    if proxy_dict:
        if not await verify_proxy_alive(proxy_dict):
            logger.warning(f"Прокси {proxy_dict.get('addr')} недоступен, откат к резервному.")
            proxy_dict = settings.fallback_proxy

    fp = get_random_fingerprint()
    client = get_configured_client(str(session_copy.with_suffix("")), fp, proxy_dict)

    try:
        await reporter.update("🔍 <b>[1/4] Экспресс-валидация сессии...</b>", force=True)
        check = await quick_check_session_fast(client)

        if not check.is_valid:
            save_to_quarantine(chat_id, session_copy, orig_name, f"{check.status}: {check.error}")
            stats["failed"] += 1
            await reporter.update(
                f"❌ <b>Сессия в карантине (/failed):</b> <code>{html.escape(orig_name)}</code>\n"
                f"Причина: <code>{html.escape(check.error or '')}</code> ({check.status})",
                force=True,
            )
            return

        phone_label = check.phone or "NoNumber"
        await reporter.update(
            f"✅ <b>Сессия валидна!</b> <code>{html.escape(phone_label)}</code>\n"
            f"🧹 <b>[2/4] Запуск экстремальной зачистки...</b>",
            force=True,
        )

        clean_report = await deep_clean_account(client, reporter)

        if settings.enable_ugs_referral:
            await reporter.update("🍉 <b>[3/4] Прохождение рефералки @GameUGSbot...</b>", force=True)
            clean_report.ugs_referral_done = await auto_ugs_referral(client, settings.ugs_ref_param)

        try:
            await client(ResetAuthorizationsRequest())
            clean_report.sessions_reset = True
        except Exception as e:
            clean_report.sessions_reset = False
            clean_report.sessions_reset_warning = html.escape(str(e))

        await reporter.update("📦 <b>[4/4] Сборка артефактов...</b>", force=True)
        metadata = await create_metadata(client, phone_label, fp)
        await client.disconnect()

        final_session = temp_dir / f"{phone_label}.session"
        session_copy.rename(final_session)

        meta_file = temp_dir / f"{phone_label}.json"
        meta_file.write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")

        zip_path = temp_dir / f"{phone_label}_cleaned.zip"
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.write(final_session, arcname=f"{phone_label}.session")
            zf.write(meta_file, arcname=f"{phone_label}.json")

        ugs_label = "✅ Пройдена (Подписки + Капча)" if clean_report.ugs_referral_done else "⚠️ Пропущена"
        caption = (
            f"⚡ <b>Сессия очищена по стандарту v100x+</b>\n\n"
            f"📞 Телефон: <code>{html.escape(phone_label)}</code>\n"
            f"🆔 ID: <code>{check.user_id}</code>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"🗑 Стерто диалогов: <b>{clean_report.dialogs_purged}</b>\n"
            f"📇 Контакты и поисковый топ: <b>Очищены</b>\n"
            f"👑 Удалено каналов создателя: <b>{clean_report.channels_deleted}</b>\n"
            f"💳 Платежные данные: <b>Уничтожены</b>\n"
            f"⏳ TTL аккаунта: <b>30 дней</b>\n"
            f"🔒 Privacy Lockdown: <b>Включен</b>\n"
            f"🍉 Рефералка @GameUGSbot: <b>{ugs_label}</b>\n"
            f"🌐 Сессии: <b>{'Сброшены' if clean_report.sessions_reset else 'Пропущены (&lt; 24ч)'}</b>"
        )

        await bot.send_document(
            chat_id=chat_id,
            document=BufferedInputFile(zip_path.read_bytes(), filename=f"{phone_label}_cleaned.zip"),
            caption=caption,
        )
        stats["success"] += 1

    except Exception as e:
        logger.exception("Ошибка в fast pipeline")
        stats["failed"] += 1
        save_to_quarantine(chat_id, session_copy, orig_name, f"FAST_CLEAN_ERROR: {e}")
        await reporter.update(
            f"❌ Ошибка быстрой очистки (сохранено в /failed): <code>{html.escape(str(e))}</code>",
            force=True,
        )
    finally:
        try:
            if client.is_connected():
                await client.disconnect()
        except Exception:
            pass
        if temp_dir.exists():
            shutil.rmtree(temp_dir, ignore_errors=True)
        if item.get("id"):
            db.remove_item(item["id"])


# ====================== ФИНАЛИЗАЦИЯ И МЕТАДАННЫЕ ======================

async def create_metadata(client: TelegramClient, phone: str, fp: dict[str, str]) -> dict[str, Any]:
    me: User = await client.get_me()
    ts = int(time.time())
    return {
        "app_id": settings.api_id,
        "app_hash": settings.api_hash,
        "device": fp["device"],
        "sdk": fp["sys"],
        "app_version": fp["app"],
        "system_lang_pack": fp["lang"],
        "system_lang_code": fp["lang"],
        "lang_pack": "tdesktop",
        "lang_code": fp["lang"],
        "twoFA": None,
        "id": me.id,
        "phone": phone,
        "username": me.username or "",
        "is_premium": bool(getattr(me, "premium", False)),
        "has_profile_pic": False,
        "register_time": ts,
        "last_check_time": ts,
        "first_name": me.first_name or "",
        "last_name": me.last_name or "",
        "session_file": f"{phone}.session",
    }


async def finalize(mig: ActiveMigration, message: Message, state: Optional[FSMContext] = None):
    client = mig.new_client
    phone = mig.phone
    temp_dir = mig.temp_dir
    reporter = StatusReporter(mig.status_message or message)

    try:
        if not client or not await client.is_user_authorized():
            raise AuthKeyUnregisteredError("Клиент не авторизован")

        if mig.old_client and not mig.old_session_terminated:
            success, err = await terminate_old_session(mig.old_client)
            mig.old_session_terminated = success
            mig.old_session_error = err
            mig.old_client = None

        # 1. Глубокая очистка аккаунта
        clean_info = await deep_clean_account(client, reporter)

        # 2. Авто-прохождение рефералки и фруктовой капчи @GameUGSbot
        if settings.enable_ugs_referral:
            await reporter.update("🍉 Прохождение рефералки @GameUGSbot...", force=True)
            clean_info.ugs_referral_done = await auto_ugs_referral(client, settings.ugs_ref_param)

        # 3. Сброс остальных сессий
        try:
            await client(ResetAuthorizationsRequest())
            clean_info.sessions_reset = True
        except FreshResetAuthorisationForbiddenError:
            clean_info.sessions_reset = False
            clean_info.sessions_reset_warning = "Сессия свежая (&lt; 24 ч, лимит Telegram)"
        except Exception as e:
            clean_info.sessions_reset = False
            clean_info.sessions_reset_warning = html.escape(str(e))

        metadata = await create_metadata(client, phone, mig.fingerprint)
        await client.disconnect()
        mig.new_client = None

        session_file = temp_dir / f"{phone}.session"
        original = Path(str(temp_dir / "new_session") + ".session")
        if original.exists():
            original.rename(session_file)

        if not session_file.exists():
            raise FileNotFoundError("Итоговый файл .session не найден")

        meta_file = temp_dir / f"{phone}.json"
        meta_file.write_text(json.dumps(metadata, ensure_ascii=False, indent=2), encoding="utf-8")

        zip_path = temp_dir / f"{phone}_v100x.zip"
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.write(session_file, arcname=f"{phone}.session")
            zf.write(meta_file, arcname=f"{phone}.json")

        data = zip_path.read_bytes()
        reset_status = "✅ Сброшены" if clean_info.sessions_reset else f"⚠️ {clean_info.sessions_reset_warning}"

        if mig.is_new_session:
            old_status = "— (Создана с нуля)"
        elif mig.old_session_terminated:
            old_status = "✅ Завершена (Log Out)"
        else:
            safe_err = html.escape(mig.old_session_error or "Сетевая ошибка")
            old_status = f"❌ Сбой деавторизации ({safe_err})"

        ugs_status = "✅ Пройдена (Подписки + Капча)" if clean_info.ugs_referral_done else "⚠️ Не выполнена"

        caption = (
            f"⚡ <b>Сессия мигрирована и очищена по v100x+</b>\n\n"
            f"📞 Телефон: <code>{html.escape(phone)}</code>\n"
            f"🆔 ID: <code>{metadata['id']}</code>\n"
            f"💻 Устройство: <code>{html.escape(mig.fingerprint['device'])} ({html.escape(mig.fingerprint['sys'])})</code>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"🔒 <b>Старая сессия: {old_status}</b>\n"
            f"👤 Профиль и @username: <b>Очищены</b>\n"
            f"🖼 Удалено аватарок: <b>{clean_info.photos_deleted}</b>\n"
            f"🔒 Privacy Lockdown: <b>Включён</b>\n"
            f"💳 Данные карт/платежей: <b>Очищены</b>\n"
            f"⏳ TTL аккаунта: <b>30 дней</b>\n"
            f"📇 Контакты и поисковый граф: <b>Удалены</b>\n"
            f"📁 Папок: <b>{clean_info.folders_deleted}</b> | Стикеров: <b>{clean_info.stickers_removed}</b>\n"
            f"👑 Каналов владельца: <b>{clean_info.channels_deleted}</b>\n"
            f"🗑 Диалогов/ботов/групп: <b>{clean_info.dialogs_purged}</b>\n"
            f"🍉 Рефералка @GameUGSbot: <b>{ugs_status}</b>\n"
            f"📱 Другие устройства: {reset_status}"
        )

        await message.answer_document(
            BufferedInputFile(data, filename=f"{phone}_v100x.zip"),
            caption=caption,
        )
        stats["success"] += 1

    except Exception as e:
        logger.exception("Ошибка финализации")
        stats["failed"] += 1
        if mig.source_file_path and mig.source_file_path.exists():
            save_to_quarantine(mig.chat_id, mig.source_file_path, mig.original_name, f"FINALIZE_ERROR: {e}")
        await message.answer(f"❌ Ошибка миграции (сохранено в /failed): <code>{html.escape(str(e))}</code>")
    finally:
        await cleanup_migration(mig, state)


# ====================== ОБРАБОТЧИК МИГРАЦИИ ======================

async def process_one_session(item: dict, bot: Bot, state: FSMContext):
    chat_id = item["chat_id"]
    mig_id = str(uuid.uuid4())[:8]
    orig_name = item["original_name"]
    auto_mode = db.get_clean_mode(chat_id, settings.default_auto_code) == 1

    status = await bot.send_message(
        chat_id,
        f"⏳ Начинаю: <b>{html.escape(orig_name)}</b>\n"
        f"Режим перехвата: <b>{'Авто' if auto_mode else 'Вручную'}</b>\n"
        f"2FA из JSON: <b>{'Да' if item['auto_2fa'] else 'Нет'}</b>",
        reply_markup=action_kb(can_skip=True),
    )

    proxy_dict = resolve_proxy(item.get("proxy_json"))
    if proxy_dict:
        if not await verify_proxy_alive(proxy_dict):
            proxy_dict = settings.fallback_proxy

    mig = ActiveMigration(
        id=mig_id,
        chat_id=chat_id,
        original_name=orig_name,
        status_message=status,
        auto_2fa_password=item["auto_2fa"],
        proxy_config=proxy_dict,
        queue_db_id=item["id"],
    )
    register_active_migration(mig)
    reporter = StatusReporter(status)

    try:
        mig.temp_dir = Path(tempfile.mkdtemp(prefix=f"mig_{chat_id}_{mig_id}_"))
        old_session_path = mig.temp_dir / "old.session"
        new_session_path = str(mig.temp_dir / "new_session")
        shutil.copy(item["file_path"], old_session_path)
        mig.source_file_path = old_session_path

        old_client = get_configured_client(str(old_session_path.with_suffix("")), mig.fingerprint, mig.proxy_config)
        await asyncio.wait_for(old_client.connect(), timeout=8.0)

        if not await old_client.is_user_authorized():
            save_to_quarantine(chat_id, old_session_path, orig_name, "UNAUTHORIZED: Сессия не авторизована")
            stats["failed"] += 1
            await reporter.update(
                f"❌ <b>{html.escape(orig_name)}</b>: не авторизована (сохранена в /failed).",
                force=True,
            )
            await cleanup_migration(mig)
            return

        me = await old_client.get_me()
        phone = me.phone if me else None
        if not phone:
            save_to_quarantine(chat_id, old_session_path, orig_name, "NO_PHONE: Не удалось получить номер")
            stats["failed"] += 1
            await reporter.update(
                f"❌ <b>{html.escape(orig_name)}</b>: нет номера (сохранена в /failed).",
                force=True,
            )
            await cleanup_migration(mig)
            return

        phone = f"+{phone}" if not str(phone).startswith("+") else str(phone)
        mig.phone = phone
        mig.old_client = old_client

        await reporter.update(
            f"📱 Сессия: <code>{html.escape(phone)}</code>\n"
            f"💻 Имитация: <code>{html.escape(mig.fingerprint['device'])}</code>\n"
            f"⏳ Запрашиваю код подтверждения...",
            force=True,
            reply_markup=action_kb(can_skip=True),
        )

        new_client = get_configured_client(new_session_path, mig.fingerprint, mig.proxy_config)
        await asyncio.wait_for(new_client.connect(), timeout=8.0)
        mig.new_client = new_client

        request_ts = int(time.time()) - 5
        result = await new_client.send_code_request(phone)
        mig.phone_code_hash = result.phone_code_hash
        mig.last_activity = time.time()

        if auto_mode:
            await reporter.update(
                f"📩 Код запрошен на <code>{html.escape(phone)}</code>. Опрашиваю 777000...",
                force=True,
                reply_markup=action_kb(can_skip=True),
            )
            code = None
            start_wait = time.time()

            while time.time() - start_wait < 90:
                if mig.skip_requested:
                    await cleanup_migration(mig, state)
                    return

                try:
                    async for msg in old_client.iter_messages(777000, limit=3):
                        msg_time = msg.date.timestamp() if msg.date else 0
                        if msg_time >= request_ts:
                            parsed = extract_telegram_code(msg.raw_text or "")
                            if parsed:
                                code = parsed
                                break
                    if code:
                        break
                except Exception as e:
                    logger.debug(f"Ошибка чтения 777000: {e}")

                await asyncio.sleep(1.5)

            if not code:
                save_to_quarantine(chat_id, old_session_path, orig_name, "CODE_TIMEOUT: Код от 777000 не пришел за 90 сек")
                stats["failed"] += 1
                await reporter.update(
                    f"❌ Код от 777000 для <code>{html.escape(phone)}</code> не получен за 90 сек (в /failed).",
                    force=True,
                )
                await cleanup_migration(mig)
                return

        else:
            mig.waiting_manual_code = True
            await state.set_state(MigrateStates.waiting_manual_code)
            await status.edit_text(
                f"📩 Код отправлен на <code>{html.escape(phone)}</code>\n\nОтправьте код подтверждения в чат:",
                reply_markup=action_kb(can_skip=True),
            )
            return

        await reporter.update(
            f"🔑 Код получен: <code>{code}</code>\n⏳ Вход в новую сессию...",
            force=True,
            reply_markup=action_kb(can_skip=False),
        )

        try:
            await new_client.sign_in(phone=phone, code=code, phone_code_hash=mig.phone_code_hash)

            success, err = await terminate_old_session(mig.old_client)
            mig.old_session_terminated = success
            mig.old_session_error = err
            mig.old_client = None

            await finalize(mig, status, state)

        except SessionPasswordNeededError:
            if mig.auto_2fa_password:
                await reporter.update("🔒 Пароль 2FA найден в JSON! Ввожу автоматически...", force=True)
                try:
                    await new_client.sign_in(password=mig.auto_2fa_password)

                    success, err = await terminate_old_session(mig.old_client)
                    mig.old_session_terminated = success
                    mig.old_session_error = err
                    mig.old_client = None

                    await finalize(mig, status, state)
                    return
                except PasswordHashInvalidError:
                    await reporter.update("⚠️ Пароль 2FA из JSON не подошел. Введите вручную:", force=True)

            mig.waiting_2fa = True
            mig.last_activity = time.time()
            await state.set_state(MigrateStates.waiting_password)
            await status.edit_text(
                f"🔑 Код <code>{code}</code> принят!\n"
                "🔒 Обнаружен пароль 2FA. Отправьте его следующим сообщением:",
                reply_markup=action_kb(can_skip=True),
            )
            return

        except (PhoneCodeInvalidError, PhoneCodeExpiredError) as e:
            save_to_quarantine(chat_id, old_session_path, orig_name, f"INVALID_CODE: {e}")
            stats["failed"] += 1
            await reporter.update(
                f"❌ Неверный или истекший код (<code>{code}</code>): {html.escape(str(e))}",
                force=True,
            )
            await cleanup_migration(mig)
            return
        except Exception as e:
            save_to_quarantine(chat_id, old_session_path, orig_name, f"SIGN_IN_ERROR: {e}")
            stats["failed"] += 1
            await reporter.update(f"❌ Ошибка входа (в /failed): {html.escape(str(e))}", force=True)
            await cleanup_migration(mig)
            return

    except PhoneNumberBannedError:
        if mig.source_file_path:
            save_to_quarantine(chat_id, mig.source_file_path, orig_name, "BANNED: Номер заблокирован")
        stats["failed"] += 1
        await reporter.update(f"❌ Номер <code>{html.escape(mig.phone)}</code> заблокирован (в /failed).", force=True)
        await cleanup_migration(mig)
    except UserDeactivatedError:
        if mig.source_file_path:
            save_to_quarantine(chat_id, mig.source_file_path, orig_name, "DEACTIVATED: Аккаунт удален")
        stats["failed"] += 1
        await reporter.update(f"❌ Аккаунт <code>{html.escape(mig.phone)}</code> деактивирован (в /failed).", force=True)
        await cleanup_migration(mig)
    except Exception as e:
        logger.exception("Ошибка process_one_session")
        if mig.source_file_path:
            save_to_quarantine(chat_id, mig.source_file_path, orig_name, f"ERROR: {e}")
        stats["failed"] += 1
        await reporter.update(f"❌ Сбой обработки (в /failed): {html.escape(str(e))}", force=True)
        await cleanup_migration(mig)


# ====================== ВОРКЕР ОЧЕРЕДИ (6 ПОТОКОВ) ======================

async def queue_worker(chat_id: int, bot: Bot, state: FSMContext):
    if queue_workers.get(chat_id, False):
        return
    queue_workers[chat_id] = True
    sem = get_chat_semaphore(chat_id)

    try:
        async def _worker_task():
            async with sem:
                while True:
                    item = db.pop_next_item(chat_id)
                    if not item:
                        break

                    rem = db.count_queue(chat_id)
                    if rem > 0 and rem % 5 == 0:
                        try:
                            await bot.send_message(chat_id, f"📋 В очереди осталось сессий: <b>{rem}</b>")
                        except Exception:
                            pass

                    mode = db.get_clean_mode(chat_id, settings.default_auto_code)
                    if mode == 2:
                        await process_fast_clean_session(item, bot, state)
                    else:
                        await process_one_session(item, bot, state)

                    mig = current_migration.get(chat_id)
                    if mig and (mig.waiting_2fa or mig.waiting_manual_code):
                        return

                    await asyncio.sleep(0.3)

        mode = db.get_clean_mode(chat_id, settings.default_auto_code)
        num_workers = settings.concurrent_workers_per_chat
        tasks = [_worker_task() for _ in range(num_workers)]
        await asyncio.gather(*tasks)

        if db.count_queue(chat_id) == 0 and not current_migration.get(chat_id):
            failed_cnt = count_quarantine(chat_id)
            extra = f"\n⚠️ Сбойных сессий в карантине: <b>{failed_cnt}</b> (скачать: /failed)" if failed_cnt > 0 else ""
            await bot.send_message(
                chat_id,
                f"✅ Обработка очереди полностью завершена!{extra}",
                reply_markup=main_menu_kb(chat_id),
            )
    finally:
        queue_workers[chat_id] = False


# ====================== ХЕНДЛЕРЫ ======================

router = Router()


@router.message(Command("start", "help"))
async def cmd_start(message: Message, state: FSMContext):
    chat_id = message.chat.id
    await clear_user_queue(chat_id, state)

    await message.answer(
        "⚡ <b>Session Cleaner & Migrator v100x+ Extreme Industrial (7 Threads)</b>\n\n"
        "Отправляйте файлы <code>.session</code> или <b>ZIP-архивы</b> (с парными JSON и прокси)!\n\n"
        "<b>Режимы работы:</b>\n"
        "• 🔄 <b>Миграция:</b> Перенос сессии в новую с ловлей кода и гарантированным Log Out старой\n"
        "• ⚡ <b>Fast Clean (7 потоков):</b> Мгновенная проверка и тотальная очистка параллельно в 7 потоков\n\n"
        "<b>Встроенные модули:</b>\n"
        "• 🍉 <b>Авто-рефералка @GameUGSbot:</b> Вход по рефералке, подписка на каналы и решение фруктовой капчи после очистки\n"
        "• 📦 <b>Карантин (/failed):</b> Сохранение всех проблемных сессий с логами ошибок в ZIP-архив\n"
        "• 🌐 <b>Proxy Pool:</b> Авто-подхват прокси из JSON или ротация из <code>proxies.txt</code>\n"
        "• 🔒 <b>Privacy Lockdown + 30d TTL + Очистка платежей</b>",
        reply_markup=main_menu_kb(chat_id),
    )


@router.message(Command("failed"))
@router.callback_query(F.data == "export_failed")
async def cmd_export_failed(event: Message | CallbackQuery):
    chat_id = event.from_user.id if isinstance(event, CallbackQuery) else event.chat.id
    q_dir = Path("quarantine") / str(chat_id)

    if not q_dir.exists() or not any(q_dir.iterdir()):
        text = "✅ В карантине нет проблемных сессий."
        if isinstance(event, CallbackQuery):
            await event.answer(text, show_alert=True)
        else:
            await event.answer(text)
        return

    zip_path = q_dir / "failed_sessions.zip"
    session_count = 0
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for f in q_dir.iterdir():
            if f.is_file() and f.name != "failed_sessions.zip":
                zf.write(f, arcname=f.name)
                if f.suffix == ".session":
                    session_count += 1

    data = zip_path.read_bytes()
    msg_target = event.message if isinstance(event, CallbackQuery) else event
    await msg_target.answer_document(
        BufferedInputFile(data, filename="failed_sessions.zip"),
        caption=(
            f"📦 <b>Выгружено проблемных сессий: {session_count}</b>\n"
            f"Внутри архива находятся файлы <code>.session</code> и <code>.error.txt</code> с причиной сбоя по каждой."
        ),
    )
    shutil.rmtree(q_dir, ignore_errors=True)
    if isinstance(event, CallbackQuery):
        await event.answer("Архив выгружен, карантин очищен.")


@router.callback_query(F.data == "cycle_clean_mode")
async def cb_cycle_clean_mode(call: CallbackQuery):
    chat_id = call.from_user.id
    current = db.get_clean_mode(chat_id, settings.default_auto_code)
    new_mode = 2 if current == 1 else (0 if current == 2 else 1)
    db.set_clean_mode(chat_id, new_mode)

    await call.message.edit_reply_markup(reply_markup=main_menu_kb(chat_id))
    names = {1: "🔄 Миграция (Авто-код)", 2: "⚡ Быстрая очистка (7 потоков)", 0: "📝 Миграция (Ручной код)"}
    await call.answer(f"Включен: {names[new_mode]}")


@router.message(Command("fast"))
async def cmd_fast(message: Message):
    db.set_clean_mode(message.chat.id, 2)
    await message.answer(
        "✅ Включен режим <b>Fast Clean (7 потоков)</b>: быстрая проверка, очистка и прохождение @GameUGSbot.",
        reply_markup=main_menu_kb(message.chat.id),
    )


@router.message(Command("auto"))
async def cmd_auto(message: Message):
    db.set_clean_mode(message.chat.id, 1)
    await message.answer(
        "✅ Включена <b>миграция с авто-перехватом кода и выходом из старой сессии</b>.",
        reply_markup=main_menu_kb(message.chat.id),
    )


@router.message(Command("manual"))
async def cmd_manual(message: Message):
    db.set_clean_mode(message.chat.id, 0)
    await message.answer(
        "✅ Включена <b>миграция с ручным вводом кода</b>.",
        reply_markup=main_menu_kb(message.chat.id),
    )


@router.callback_query(F.data == "skip_current")
async def cb_skip_current(call: CallbackQuery, state: FSMContext):
    chat_id = call.from_user.id
    mig = current_migration.get(chat_id)
    if not mig:
        await call.answer("Нет активной сессии для пропуска.", show_alert=True)
        return

    mig.skip_requested = True
    stats["skipped"] += 1
    await call.answer("Сессия пропущена. Переход к следующей...")
    await cleanup_migration(mig, state)

    if db.count_queue(chat_id) > 0:
        asyncio.create_task(queue_worker(chat_id, call.bot, state))


@router.message(Command("new", "create"))
@router.callback_query(F.data == "btn_new_session")
async def cmd_new(event: Message | CallbackQuery, state: FSMContext):
    chat_id = event.from_user.id if isinstance(event, CallbackQuery) else event.chat.id

    if chat_id in current_migration or db.count_queue(chat_id) > 0:
        text = "❌ Идет обработка. Дождитесь окончания или отмените текущую очередь."
        if isinstance(event, CallbackQuery):
            await event.answer(text, show_alert=True)
        else:
            await event.answer(text)
        return

    await state.set_state(MigrateStates.waiting_phone)
    prompt = "📱 Отправьте номер телефона в международном формате (например, <code>+79001234567</code>):"
    if isinstance(event, CallbackQuery):
        await event.message.answer(prompt, reply_markup=action_kb(can_skip=False))
        await event.answer()
    else:
        await event.answer(prompt, reply_markup=action_kb(can_skip=False))


@router.message(MigrateStates.waiting_phone)
async def process_phone(message: Message, state: FSMContext):
    chat_id = message.chat.id
    raw = (message.text or "").strip().replace(" ", "").replace("-", "").replace("(", "").replace(")", "")

    if raw.startswith("8") and len(raw) == 11:
        raw = "+7" + raw[1:]
    elif not raw.startswith("+"):
        raw = "+" + raw

    if not re.fullmatch(r"\+\d{10,15}", raw):
        await message.answer("❌ Неверный формат. Пример: <code>+79001234567</code>")
        return

    phone = raw
    mig_id = str(uuid.uuid4())[:8]
    status = await message.answer(f"⏳ Создание сессии для <code>{html.escape(phone)}</code>...")

    mig = ActiveMigration(
        id=mig_id,
        chat_id=chat_id,
        phone=phone,
        status_message=status,
        is_new_session=True,
        waiting_manual_code=True,
        proxy_config=resolve_proxy(None),
    )
    register_active_migration(mig)

    try:
        mig.temp_dir = Path(tempfile.mkdtemp(prefix=f"new_{chat_id}_{mig_id}_"))
        new_client = get_configured_client(str(mig.temp_dir / "new_session"), mig.fingerprint, mig.proxy_config)
        await new_client.connect()
        mig.new_client = new_client

        result = await new_client.send_code_request(phone)
        mig.phone_code_hash = result.phone_code_hash
        mig.last_activity = time.time()
        stats["started"] += 1

        await state.set_state(MigrateStates.waiting_manual_code)
        await status.edit_text(
            f"📩 Код отправлен на <code>{html.escape(phone)}</code>. Отправьте его:",
            reply_markup=action_kb(can_skip=False),
        )

    except FloodWaitError as e:
        await status.edit_text(f"❌ Telegram FloodWait: подождите {e.seconds} с.")
        await cleanup_migration(mig, state)
    except Exception as e:
        logger.exception("Ошибка запроса кода")
        await status.edit_text(f"❌ Ошибка запроса: {html.escape(str(e))}")
        await cleanup_migration(mig, state)


@router.message(Command("cancel"))
@router.callback_query(F.data == "cancel_all")
async def cmd_cancel(event: Message | CallbackQuery, state: FSMContext):
    chat_id = event.from_user.id if isinstance(event, CallbackQuery) else event.chat.id
    await clear_user_queue(chat_id, state)
    stats["cancelled"] += 1

    text = "🛑 Очередь полностью сброшена, временные файлы удалены."
    if isinstance(event, CallbackQuery):
        await event.message.edit_text(text, reply_markup=main_menu_kb(chat_id))
        await event.answer()
    else:
        await event.answer(text, reply_markup=main_menu_kb(chat_id))


# ====================== ЗАГРУЗКА .SESSION И .ZIP ======================

@router.message(F.document)
async def process_document_upload(message: Message, state: FSMContext):
    chat_id = message.chat.id
    doc: Document = message.document
    fname = (doc.file_name or "").lower()

    if not (fname.endswith(".session") or fname.endswith(".zip")):
        await message.answer("❌ Принимаются файлы <code>.session</code> или <b>.zip архивы</b>.")
        return

    temp_dir = Path(tempfile.mkdtemp(prefix=f"upload_{chat_id}_"))
    archive_file = temp_dir / doc.file_name
    await message.bot.download(doc, destination=archive_file)

    added_count = 0

    if fname.endswith(".zip"):
        try:
            with zipfile.ZipFile(archive_file, "r") as zf:
                zf.extractall(temp_dir)

            sessions = list(temp_dir.rglob("*.session"))
            if not sessions:
                await message.answer("❌ В архиве не обнаружено файлов <code>.session</code>.")
                shutil.rmtree(temp_dir, ignore_errors=True)
                return

            for s_path in sessions:
                json_path = s_path.with_suffix(".json")
                auto_pass = None
                proxy_dict = None
                if json_path.exists():
                    try:
                        j_data = json.loads(json_path.read_text(encoding="utf-8"))
                        auto_pass = j_data.get("twoFA") or j_data.get("password") or j_data.get("2fa")
                        proxy_dict = parse_session_proxy(j_data)
                    except Exception:
                        pass

                db.add_queue_item(
                    item_id=str(uuid.uuid4())[:8],
                    chat_id=chat_id,
                    file_path=str(s_path),
                    original_name=s_path.name,
                    auto_2fa=str(auto_pass) if auto_pass else None,
                    proxy_dict=proxy_dict,
                )
                added_count += 1

        except Exception as e:
            await message.answer(f"❌ Ошибка чтения ZIP-архива: {html.escape(str(e))}")
            shutil.rmtree(temp_dir, ignore_errors=True)
            return
    else:
        db.add_queue_item(
            item_id=str(uuid.uuid4())[:8],
            chat_id=chat_id,
            file_path=str(archive_file),
            original_name=doc.file_name,
            auto_2fa=None,
            proxy_dict=None,
        )
        added_count += 1

    stats["started"] += added_count
    total_queue = db.count_queue(chat_id)

    await message.answer(
        f"📥 Сессий добавлено в SQLite: <b>{added_count}</b>\n"
        f"Всего в очереди: <b>{total_queue}</b>",
        reply_markup=action_kb(can_skip=True),
    )

    if not queue_workers.get(chat_id, False):
        asyncio.create_task(queue_worker(chat_id, message.bot, state))


@router.message(MigrateStates.waiting_manual_code)
async def process_manual_code(message: Message, state: FSMContext):
    chat_id = message.chat.id
    code = (message.text or "").strip().replace(" ", "").replace("-", "")

    mig = current_migration.get(chat_id)
    if not mig or not mig.new_client or not mig.waiting_manual_code:
        await message.answer("Нет сессий, ожидающих ввода кода.")
        return

    if not code.isdigit() or not (4 <= len(code) <= 8):
        await message.answer("❌ Код должен содержать от 4 до 8 цифр.")
        return

    status = await message.answer("⏳ Авторизация...")
    try:
        await mig.new_client.sign_in(phone=mig.phone, code=code, phone_code_hash=mig.phone_code_hash)

        success, err = await terminate_old_session(mig.old_client)
        mig.old_session_terminated = success
        mig.old_session_error = err
        mig.old_client = None

        mig.waiting_manual_code = False
        await state.clear()
        await finalize(mig, status, state)

        if db.count_queue(chat_id) > 0:
            asyncio.create_task(queue_worker(chat_id, message.bot, state))

    except SessionPasswordNeededError:
        if mig.auto_2fa_password:
            try:
                await mig.new_client.sign_in(password=mig.auto_2fa_password)

                success, err = await terminate_old_session(mig.old_client)
                mig.old_session_terminated = success
                mig.old_session_error = err
                mig.old_client = None

                mig.waiting_manual_code = False
                await state.clear()
                await finalize(mig, status, state)
                if db.count_queue(chat_id) > 0:
                    asyncio.create_task(queue_worker(chat_id, message.bot, state))
                return
            except Exception:
                pass

        mig.waiting_manual_code = False
        mig.waiting_2fa = True
        mig.last_activity = time.time()
        await state.set_state(MigrateStates.waiting_password)
        await status.edit_text("🔒 Аккаунт защищен 2FA-паролем. Отправьте его:", reply_markup=action_kb(can_skip=True))
    except (PhoneCodeInvalidError, PhoneCodeExpiredError) as e:
        await status.edit_text(f"❌ Неверный или истекший код: {html.escape(str(e))}")
    except Exception as e:
        await status.edit_text(f"❌ Сбой авторизации: {html.escape(str(e))}")


@router.message(MigrateStates.waiting_password)
async def process_2fa(message: Message, state: FSMContext):
    chat_id = message.chat.id
    password = (message.text or "").strip()

    mig = current_migration.get(chat_id)
    if not mig or not mig.new_client or not mig.waiting_2fa:
        await message.answer("Нет сессий, ожидающих пароль 2FA.")
        return

    status = await message.answer("⏳ Проверка 2FA...")
    try:
        await mig.new_client.sign_in(password=password)

        success, err = await terminate_old_session(mig.old_client)
        mig.old_session_terminated = success
        mig.old_session_error = err
        mig.old_client = None

        mig.waiting_2fa = False
        await state.clear()
        await finalize(mig, status, state)

        if db.count_queue(chat_id) > 0:
            asyncio.create_task(queue_worker(chat_id, message.bot, state))

    except PasswordHashInvalidError:
        await status.edit_text("❌ Пароль 2FA не подходит. Попробуйте еще раз:")
    except Exception as e:
        await status.edit_text(f"❌ Ошибка 2FA: {html.escape(str(e))}")
        await cleanup_migration(mig, state)


@router.message(Command("stats"))
async def cmd_stats(message: Message):
    if not is_admin(message.from_user.id):
        return
    with sqlite3.connect(settings.db_file) as conn:
        cur = conn.cursor()
        cur.execute("SELECT COUNT(*) FROM queue WHERE status = 'pending'")
        total_in_db = cur.fetchone()[0]

    await message.answer(
        f"📊 <b>Статистика сервиса v100x+ Extreme</b>\n\n"
        f"• Всего запусков: {stats['started']}\n"
        f"• Успешно очищено: {stats['success']}\n"
        f"• Пропущено оператором: {stats['skipped']}\n"
        f"• Ошибок (в карантине): {stats['failed']}\n"
        f"• Отменено: {stats['cancelled']}\n"
        f"• В SQLite очереди: {total_in_db}"
    )


# ====================== ФОНОВЫЙ ТАЙМАУТ-ВОТЧДОГ ======================

async def watchdog_task(bot: Bot):
    while True:
        await asyncio.sleep(60)
        now = time.time()
        timeout_sec = settings.session_timeout_minutes * 60
        stale_chats = []

        for chat_id, mig in list(current_migration.items()):
            if (mig.waiting_2fa or mig.waiting_manual_code) and (now - mig.last_activity > timeout_sec):
                stale_chats.append(chat_id)

        for chat_id in stale_chats:
            mig = current_migration.get(chat_id)
            if mig:
                logger.info(f"Таймаут сессии для chat_id {chat_id}")
                try:
                    await bot.send_message(chat_id, "⌛ Время ожидания кода/2FA истекло. Сессия сброшена.")
                except Exception:
                    pass
                await cleanup_migration(mig)


# ====================== ТОЧКА ВХОДА И SHUTDOWN ======================

async def shutdown(dp: Dispatcher, bot: Bot):
    logger.info("Получен сигнал завершения работы. Отключение сессий...")
    for mig in list(current_migration.values()):
        await cleanup_migration(mig)
    await bot.session.close()
    logger.info("Все ресурсы корректно освобождены.")


async def main():
    bot = Bot(token=settings.bot_token, default=DefaultBotProperties(parse_mode="HTML"))
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)

    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            loop.add_signal_handler(sig, lambda: asyncio.create_task(shutdown(dp, bot)))
        except NotImplementedError:
            pass

    asyncio.create_task(watchdog_task(bot))

    logger.info("Bot v100x+ Extreme Industrial успешно запущен")
    await dp.start_polling(bot)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("Бот остановлен.")
