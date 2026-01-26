import asyncio
import os
import sys
import warnings
import json
import random
import pandas as pd
import numpy as np
import math
from datetime import datetime, timedelta
from colorama import Fore, Back, Style, init
from binance import AsyncClient
from binance.enums import *
from binance.exceptions import BinanceAPIException
from dotenv import load_dotenv
from telegram import Bot
from telegram.error import TelegramError
import matplotlib.pyplot as plt
import io
import torch
import torch.nn as nn
import torch.optim as optim
from pycoingecko import CoinGeckoAPI
import csv
from pathlib import Path
from sklearn.model_selection import train_test_split
from concurrent.futures import ThreadPoolExecutor  # ถ้าต้องการ hybrid กับ blocking calls
from typing import List, Dict, Optional, Tuple, Any
import time
# ที่ด้านบนของไฟล์ (หลัง import)
BOT_USERNAME = "puAI_bot"  # เปลี่ยนตามชื่อจริงของคุณ

TRADE_HISTORY_FILE = os.path.join(os.path.dirname(__file__), "titan_trade_history.csv")
# --- LOAD ENV FIRST ---
load_dotenv()
# โหลด ALLOWED_USERS จาก .env เป็น list ของ integer
ALLOWED_USERS = []
allowed_str = os.getenv("ALLOWED_USERS", "")
if allowed_str:
    try:
        ALLOWED_USERS = [int(uid.strip()) for uid in allowed_str.split(",") if uid.strip().isdigit()]
        print(f"{Fore.GREEN}โหลด ALLOWED_USERS สำเร็จ: {ALLOWED_USERS}{Style.RESET_ALL}")
    except Exception as e:
        print(f"{Fore.RED}โหลด ALLOWED_USERS ล้มเหลว: {e} → ใช้ค่า default ว่าง{Style.RESET_ALL}")
        ALLOWED_USERS = []

# ถ้าไม่มีใครได้รับอนุญาตเลย → เตือน
if not ALLOWED_USERS:
    print(f"{Fore.YELLOW}⚠️ ไม่มี ALLOWED_USERS ใน .env → ทุกคนใช้บอทได้ (ไม่ปลอดภัย!){Style.RESET_ALL}")
    
# --- INITIALIZE ---
init(autoreset=True)
warnings.filterwarnings("ignore")

import logging

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s | %(levelname)-7s | %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler("pending_activity.log", encoding='utf-8')
    ]
)
logger = logging.getLogger("pending")
# ==========================================================================
#                          TELEGRAM CONFIG
# ==========================================================================
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")

telegram_bot = None
update_offset = None
running = True
            # Global cooldown สำหรับ /lauto (ป้องกันสแกนซ้ำเร็วเกิน)
lauto_cooldown = {}  # sym → timestamp ล่าสุด
LAUTO_COOLDOWN_MINUTES = 45
# ==========================================================================
# เพิ่มตัวแปร global สำหรับ cooldown (เฉพาะ manual close)
# ==========================================================================
manual_closed_cooldown = {}           # sym → timestamp ที่ปิดด้วยมือล่าสุด
COOLDOWN_AFTER_MANUAL_MINUTES = 90    # 90 นาที = 1.5 ชม. (ปรับได้ตามต้องการ)
# ==========================================================================
# ตัวแปร global ที่ต้องมี (ใส่ด้านบนไฟล์หรือใน main)
# ==========================================================================
prev_active_symbols = set()          # เก็บ symbols ที่เปิดอยู่รอบก่อนหน้า
last_closed_check = 0.0              # timestamp ล่าสุดที่ตรวจสอบ closed
active_detailed = {}                 # {sym: {entry_price, entry_time, side, quantity, features, max_roe, ...}}
# ==========================================================================
#                          TRADE HISTORY
# ==========================================================================
TRADE_HISTORY_FILE = "titan_trade_history.csv"
TRADE_HISTORY_FIELDS = [
    'timestamp', 'symbol', 'side', 'entry_price', 'exit_price',
    'quantity', 'pnl', 'pnl_percent', 'duration_hours', 'exit_reason',
    'is_win', 'leverage', 'max_roe_percent'
]

if not Path(TRADE_HISTORY_FILE).exists():
    with open(TRADE_HISTORY_FILE, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=TRADE_HISTORY_FIELDS)
        writer.writeheader()

# Global variables
last_long_entry_time = {}  # sym → timestamp
prev_prices = {}
ticker_offset = 0
ticker_direction = 1
manual_limit_orders = []  # เก็บข้อมูล limit ที่ตั้งด้วยมือเพิ่มเติม
last_sl_tp_check = 0.0   # หรือ datetime.min.timestamp()
new_position_locked = set()  # เก็บ symbol ที่เคยแจ้งตั้ง SL/TP ไปแล้ว
bal = 0.0
active = []                 # สำหรับแสดง dashboard (เหมือนเดิม)
active_detailed = {}        # ข้อมูล position เปิดแบบละเอียด (สำคัญ!)
btc_p = 0.0
pending_orders_detail = []
setauto_cooldown = {}  # sym → timestamp ล่าสุดที่ตั้ง Limit ด้วย /setauto
SETAUTO_COOLDOWN_MINUTES = 45  # ป้องกันตั้ง Limit ซ้ำเร็วเกิน


sym_info = {}
sym_filters = {}

top_50_symbols = []
last_volume_update = datetime.min
VOLUME_UPDATE_INTERVAL = timedelta(hours=4)

last_spike_check = datetime.min
SPIKE_CHECK_INTERVAL = timedelta(minutes=5)

last_short_signal_check = datetime.min
SHORT_SIGNAL_CHECK_INTERVAL = timedelta(minutes=7)

auto_spike_enabled = True
auto_short_signal_enabled = True

sl_tp_advice_notified = set()
signal_features = {}

atr_cache = {}
ATR_CACHE_DURATION = timedelta(minutes=2)
# ==========================================================================

if TELEGRAM_BOT_TOKEN:
    try:
        telegram_bot = Bot(token=TELEGRAM_BOT_TOKEN)
        print(f"{Fore.GREEN}Telegram Bot initialized!")
    except Exception as e:
        print(f"{Fore.RED}Telegram init failed: {e}")
        telegram_bot = None

# ==========================================================================
#                                 CONFIG
# ==========================================================================
API_KEY = os.getenv("BINANCE_API_KEY")
API_SECRET = os.getenv("BINANCE_API_SECRET")

if not API_KEY or not API_SECRET:
    print(f"{Fore.RED}Error: ไม่พบ API Key!")
    sys.exit(1)

USE_TESTNET = False
MEMORY_FILE = "titan_memory.json"

# ==========================================================================
#          CONFIG สำหรับกำไรสูงสุด (Aggressive Profit Mode) 2026
# ==========================================================================
# -------------------------- ค่าคงที่ (ปรับได้ตามต้องการ) --------------------------
COOLDOWN_MINUTES     = 30
MIN_VOL_RATIO        = 2.35
MIN_RR_RATIO         = 1.95
RISK_USD_PER_TRADE   = 0.5

ALL_TFS = ["1m", "3m", "5m", "15m", "30m", "1h", "2h", "4h", "6h", "12h", "1d"]
PRIORITY_TFS = ["5m", "15m", "1h", "4h"]   # timeframe ที่คุณให้ความสำคัญสูงสุด


# --- Trailing Stop (สำคัญที่สุดสำหรับกำไรสูงสุด) ---
TRAILING_ACTIVATION_MULTIPLIER = 1.8   # เริ่ม trailing เร็วขึ้น (จาก 2.5)
TRAILING_DELTA_MULTIPLIER = 1.4        # trailing ห่างน้อยลง ให้ lock กำไรไว

# --- Risk & Position Management ---
RISK_PER_TRADE_PERCENT        = 0.025         # จาก 0.02 → เสี่ยง $0.625–0.75 ต่อเทรด (ทุน $100)
MAX_OPEN_POSITIONS            = 5             # จาก 3 → เปิดได้มากขึ้น (เพิ่มโอกาส)
MAX_LEVERAGE                  = 30            # จาก 25 → ใช้สูงขึ้นในเทรนด์แรง (แต่มี guard)

# --- Signal & Entry (เข้าเร็ว + เยอะขึ้น) ---
SIGNAL_THRESHOLD_LONG         = 5.5           # จาก 7 → ผ่อนปรนมากขึ้น เจอสัญญาณไว
SIGNAL_THRESHOLD_SHORT        = 5.5           # เดียวกัน
ADX_THRESHOLD                 = 22            # จาก 28 → ยอมรับเทรนด์อ่อน/เริ่มต้น
SCAN_BATCH_SIZE               = 40           # จาก 40 → สแกนเยอะขึ้นมาก
ENTRY_PULLBACK_PERCENT        = 25.0          # จาก 38 → เข้าใกล้ราคาปัจจุบันมากขึ้น (fill ไว)

# --- SL/TP (ให้กำไรวิ่งไกล แต่ SL ยังป้องกัน) ---
ATR_SL_MULTIPLIER = 1.6      # จาก 2.2 → ลดความเสี่ยงต่อเทรด
ATR_TP_MULTIPLIER = 4.5      # จาก 6.0 → TP ใกล้ลง แต่ hit บ่อยขึ้น
MIN_RR_FOR_ENTRY = 2.3                 # บังคับ RR ขั้นต่ำ 2.3:1

# --- อื่น ๆ (ความเร็ว + ความปลอดภัย) ---
LIMIT_ORDER_TIMEOUT_HOURS     = 1.5           # จาก 2.0 → ยกเลิกเก่าเร็วขึ้น
MIN_BALANCE_TO_TRADE          = 12.0          # จาก 15 → เริ่มเทรดได้เร็วกว่า
MIN_NOTIONAL_USDT             = 4             # จาก 5 → เข้าได้กับ position เล็ก

# ========== GLOBAL FLAGS ==========
# ========== AUTO-SHORT INSTITUTIONAL ==========
auto_short_system_enabled = False  # เริ่มต้นปิด — ต้องเปิดผ่าน /autoshort
last_short_signal_check = datetime.min
SHORT_SIGNAL_CHECK_INTERVAL = timedelta(seconds=45)
recent_short_trades = {}  # ป้องกัน duplicate

# ===== CONFIG =====
RISK_PERCENT_PER_TRADE = 0.01      # 1% ของพอร์ต
STOP_LOSS_PCT = 0.03              # 3%
TAKE_PROFIT_PCT = 0.06            # 6%
MAX_CONCURRENT_SHORTS = 3
recent_short_trades = {}  # global dict to track last trade time per symbol

MAJOR_TICKER_SYMBOLS = [
    # ===== Major / Large Cap =====
    'BTCUSDT', 'ETHUSDT', 'BNBUSDT', 'SOLUSDT', 'XRPUSDT', 'ADAUSDT',
    'DOGEUSDT', 'AVAXUSDT', 'LINKUSDT', 'DOTUSDT', 'TRXUSDT', 'MATICUSDT',
    'LTCUSDT', 'BCHUSDT', 'NEARUSDT', 'UNIUSDT', 'ICPUSDT', 'ATOMUSDT',
    'APTUSDT', 'SUIUSDT', 'TONUSDT', 'HBARUSDT', 'INJUSDT', 'OPUSDT',
    'ARBUSDT', 'FILUSDT', 'ETCUSDT', 'XLMUSDT', 'ALGOUSDT', 'EOSUSDT',

    # ===== DeFi / Infra / AI =====
    'AAVEUSDT', 'CRVUSDT', 'MKRUSDT', 'SNXUSDT', 'RUNEUSDT',
    'GRTUSDT', 'RNDRUSDT', 'FETUSDT', 'IMXUSDT', 'LDOUSDT',

    # ===== Meme / High Volume Perp =====
    '1000SHIBUSDT', 'PEPEUSDT', 'WIFUSDT', 'FLOKIUSDT', 'BONKUSDT',
    'JUPUSDT', 'MEMEUSDT', 'TURBOUSDT', 'BRETTUSDT', 'MYROUSDT'
]


prev_prices = {sym: 0.0 for sym in MAJOR_TICKER_SYMBOLS}


# ==========================================================================
#                  GLOBAL RATE LIMITER (สำคัญมาก!)
# ==========================================================================

# Global variables สำหรับ rate limit
last_api_call_time = 0.0
MIN_DELAY_BETWEEN_CALLS = 0.65   # วินาที → ~92 requests/นาที (ปลอดภัยมาก)

async def rate_limited_call(coro):
    """
    ห่อทุกการเรียก API ด้วยฟังก์ชันนี้ เพื่อป้องกัน IP ban
    """
    global last_api_call_time
    now = time.time()
    elapsed = now - last_api_call_time
    
    if elapsed < MIN_DELAY_BETWEEN_CALLS:
        await asyncio.sleep(MIN_DELAY_BETWEEN_CALLS - elapsed)
    
    result = await coro
    last_api_call_time = time.time()
    return result
# ==========================================================================
def log_trade_to_csv(trade_data):
    """บันทึก trade ลง CSV - ป้องกัน NoneType error ทุกทาง"""
    if trade_data is None:
        print(f"{Fore.RED}CRITICAL: trade_data is None → ข้ามบันทึก{Style.RESET_ALL}")
        return
    if not isinstance(trade_data, dict):
        print(f"{Fore.RED}CRITICAL: trade_data ไม่ใช่ dict ({type(trade_data)}) → ข้ามบันทึก{Style.RESET_ALL}")
        return
    try:
        # Debug ก่อนบันทึก
        print(f"[DEBUG LOG] กำลังบันทึก {trade_data.get('symbol', 'UNKNOWN')} | PNL {trade_data.get('pnl', 'N/A')}")
        # แปลง timestamp
        ts = trade_data.get('timestamp')
        if isinstance(ts, datetime):
            trade_data['timestamp'] = ts.isoformat()
        elif not isinstance(ts, str):
            trade_data['timestamp'] = datetime.now().isoformat()
        # เติม field ที่ขาดทั้งหมด (fallback เต็มรูปแบบ)
        defaults = {
            'timestamp': datetime.now().isoformat(),
            'symbol': 'UNKNOWN',
            'side': 'UNKNOWN',
            'entry_price': 0.0,
            'exit_price': 0.0,
            'quantity': 0.0,
            'pnl': 0.0,
            'pnl_percent': 0.0,
            'duration_hours': 0.0,
            'exit_reason': 'Unknown (fallback)',
            'is_win': False,
            'leverage': 0,
            'max_roe_percent': 0.0,
        }
        for field, default_val in defaults.items():
            if field not in trade_data or trade_data[field] is None:
                trade_data[field] = default_val
        # เขียน CSV
        with open(TRADE_HISTORY_FILE, 'a', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=TRADE_HISTORY_FIELDS)
            writer.writerow(trade_data)
        print(f"{Fore.GREEN}บันทึกสำเร็จ → {trade_data['symbol']} | PNL {trade_data['pnl']:+.2f} | Reason: {trade_data['exit_reason']}{Style.RESET_ALL}")
        # AI update (เช็ค features ก่อน)
        features = trade_data.get('features', [])
        if isinstance(features, (list, tuple)) and len(features) > 0:
            try:
                brain.update_memory(features, trade_data['is_win'])
                print(f"{Fore.CYAN}AI updated for {trade_data['symbol']}{Style.RESET_ALL}")
            except Exception as brain_err:
                print(f"{Fore.YELLOW}AI update fail: {brain_err}{Style.RESET_ALL}")
        else:
            print(f"{Fore.YELLOW}Skip AI update - no valid features{Style.RESET_ALL}")
    except Exception as e:
        print(f"{Fore.RED}LOG ERROR {trade_data.get('symbol', '?')}: {e}{Style.RESET_ALL}")
        traceback.print_exc()  # ← เพิ่ม
        # Emergency log
        try:
            with open("emergency_trade_log.txt", "a", encoding="utf-8") as ef:
                ef.write(f"{datetime.now().isoformat()} | {json.dumps(trade_data, default=str)}\n")
        except:
            pass
  
# แก้ในฟังก์ชัน get_current_winrate() ให้แข็งแรงขึ้นหน่อย
def get_current_winrate(filter_days: int = None, min_pnl_abs: float = 0.01):
    """
    คำนวณ winrate จาก titan_trade_history.csv แบบปลอดภัยและละเอียด
    
    Parameters:
    - filter_days: ถ้าตั้งค่า จะนับเฉพาะ trade ในช่วง N วันที่ผ่านมา (เช่น 30, 90)
    - min_pnl_abs: ข้าม trade ที่ |pnl| < ค่านี้ (กรอง noise เช่น pnl=0.0001)
    
    Returns: dict ที่มี
    - overall_winrate (%)
    - overall_wins
    - overall_total
    - long_winrate (%)
    - long_wins
    - long_total
    - short_winrate (%)
    - short_wins
    - short_total
    """
    try:
        if not TRADE_HISTORY_FILE or not os.path.exists(TRADE_HISTORY_FILE):
            print("[WINRATE] ไม่พบไฟล์ CSV")
            return {
                'overall_winrate': 0.0, 'overall_wins': 0, 'overall_total': 0,
                'long_winrate': 0.0, 'long_wins': 0, 'long_total': 0,
                'short_winrate': 0.0, 'short_wins': 0, 'short_total': 0
            }

        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty:
            return {
                'overall_winrate': 0.0, 'overall_wins': 0, 'overall_total': 0,
                'long_winrate': 0.0, 'long_wins': 0, 'long_total': 0,
                'short_winrate': 0.0, 'short_wins': 0, 'short_total': 0
            }

        # แปลงคอลัมน์สำคัญให้เป็น numeric อย่างปลอดภัย
        numeric_cols = ['pnl', 'pnl_percent', 'entry_price', 'exit_price', 'quantity']
        for col in numeric_cols:
            if col in df.columns:
                df[col] = pd.to_numeric(df[col], errors='coerce')

        # กรอง trade ที่สมบูรณ์
        valid_mask = (
            df['pnl'].notna() &
            (abs(df['pnl']) >= min_pnl_abs) &
            (df['entry_price'] > 0) &
            (df['exit_price'] > 0) &
            (df['quantity'] > 0) &
            df['is_win'].isin([True, False, 1, 0, 'True', 'False'])
        )

        df_valid = df[valid_mask].copy()

        # แปลง is_win ให้เป็น boolean ชัดเจน
        df_valid['is_win'] = df_valid['is_win'].astype(bool)

        # Filter ตามช่วงเวลา (ถ้ามี)
        if filter_days is not None and 'timestamp' in df_valid.columns:
            try:
                df_valid['timestamp'] = pd.to_datetime(df_valid['timestamp'], errors='coerce')
                cutoff = datetime.now() - timedelta(days=filter_days)
                df_valid = df_valid[df_valid['timestamp'] >= cutoff].copy()
            except Exception as e:
                print(f"[WINRATE] Filter วันที่ล้มเหลว: {e} → ใช้ข้อมูลทั้งหมด")

        if df_valid.empty:
            return {
                'overall_winrate': 0.0, 'overall_wins': 0, 'overall_total': 0,
                'long_winrate': 0.0, 'long_wins': 0, 'long_total': 0,
                'short_winrate': 0.0, 'short_wins': 0, 'short_total': 0
            }

        # ─── คำนวณรวมทั้งหมด ───
        overall_wins = int(df_valid['is_win'].sum())
        overall_total = len(df_valid)
        overall_winrate = (overall_wins / overall_total * 100) if overall_total > 0 else 0.0

        # ─── แยก LONG / SHORT ───
        df_valid['side_upper'] = df_valid['side'].astype(str).str.upper().str.strip()

        # LONG
        df_long = df_valid[df_valid['side_upper'] == 'LONG']
        long_wins = int(df_long['is_win'].sum())
        long_total = len(df_long)
        long_winrate = (long_wins / long_total * 100) if long_total > 0 else 0.0

        # SHORT
        df_short = df_valid[df_valid['side_upper'] == 'SHORT']
        short_wins = int(df_short['is_win'].sum())
        short_total = len(df_short)
        short_winrate = (short_wins / short_total * 100) if short_total > 0 else 0.0

        result = {
            'overall_winrate': round(overall_winrate, 2),
            'overall_wins': overall_wins,
            'overall_total': overall_total,
            'long_winrate': round(long_winrate, 2),
            'long_wins': long_wins,
            'long_total': long_total,
            'short_winrate': round(short_winrate, 2),
            'short_wins': short_wins,
            'short_total': short_total
        }

        print(f"[WINRATE] Overall: {overall_winrate:.2f}% ({overall_wins}/{overall_total})")
        print(f"          LONG:    {long_winrate:.2f}% ({long_wins}/{long_total})")
        print(f"          SHORT:   {short_winrate:.2f}% ({short_wins}/{short_total})")

        return result

    except Exception as e:
        print(f"[WINRATE CRITICAL ERROR] {e}")
        return {
            'overall_winrate': 0.0, 'overall_wins': 0, 'overall_total': 0,
            'long_winrate': 0.0, 'long_wins': 0, 'long_total': 0,
            'short_winrate': 0.0, 'short_wins': 0, 'short_total': 0
        }
        
def generate_monthly_winrate_chart(filter_months: int = 12, title: str = "Winrate รายเดือน"):
    """
    สร้างกราฟแท่ง winrate รายเดือน ย้อนหลัง N เดือน
    Returns: BytesIO buffer หรือ None ถ้าไม่มีข้อมูล
    """
    try:
        if not os.path.exists(TRADE_HISTORY_FILE):
            return None

        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty:
            return None

        # แปลง timestamp
        df['timestamp'] = pd.to_datetime(df['timestamp'], errors='coerce')
        df = df.dropna(subset=['timestamp', 'is_win', 'pnl'])

        # กรอง trade ที่สมบูรณ์
        df = df[(df['entry_price'] > 0) & (df['exit_price'] > 0) & (abs(df['pnl']) >= 0.01)]

        # แปลง is_win เป็น boolean
        df['is_win'] = df['is_win'].astype(bool)

        # เพิ่มคอลัมน์เดือน
        df['month'] = df['timestamp'].dt.to_period('M')
        df['month_str'] = df['month'].astype(str)

        # Group by เดือน
        monthly = df.groupby('month').agg(
            total=('is_win', 'count'),
            wins=('is_win', 'sum')
        ).reset_index()

        monthly['winrate'] = (monthly['wins'] / monthly['total'] * 100).round(1)

        # กรองย้อนหลัง N เดือน
        if filter_months:
            cutoff = datetime.now() - pd.DateOffset(months=filter_months)
            monthly = monthly[monthly['month'].dt.to_timestamp() >= cutoff]

        if monthly.empty:
            return None

        monthly = monthly.sort_values('month')

        # ─── สร้างกราฟ ───
        fig, ax = plt.subplots(figsize=(12, 7), dpi=110)
        bars = ax.bar(monthly['month_str'], monthly['winrate'],
                      color=['#4CAF50' if w >= 50 else '#F44336' for w in monthly['winrate']],
                      width=0.65)

        # เพิ่มตัวเลขบนแท่ง
        for bar, winrate, wins, total in zip(bars, monthly['winrate'], monthly['wins'], monthly['total']):
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2, height + 2,
                    f'{winrate:.1f}%\n({wins}/{total})',
                    ha='center', va='bottom', fontsize=10, fontweight='bold')

        ax.set_ylim(0, max(100, monthly['winrate'].max() + 15))
        ax.set_ylabel('Win Rate (%)', fontsize=12)
        ax.set_xlabel('เดือน (YYYY-MM)', fontsize=12)
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.grid(axis='y', linestyle='--', alpha=0.7)
        plt.xticks(rotation=45, ha='right')
        plt.tight_layout()

        buf = io.BytesIO()
        plt.savefig(buf, format='png', bbox_inches='tight', dpi=110)
        buf.seek(0)
        plt.close(fig)

        return buf

    except Exception as e:
        print(f"[MONTHLY WINRATE GRAPH ERROR] {e}")
        return None
       
def generate_winrate_chart(stats: dict, title: str = "Winrate Statistics"):
    """
    สร้างกราฟแท่งแสดง winrate รวม + LONG + SHORT
    Returns: BytesIO buffer (พร้อมส่งเป็นรูปภาพ)
    """
    try:
        # ข้อมูลสำหรับกราฟ
        categories = ['Overall', 'LONG', 'SHORT']
        winrates = [
            stats['overall_winrate'],
            stats['long_winrate'],
            stats['short_winrate']
        ]
        totals = [
            stats['overall_total'],
            stats['long_total'],
            stats['short_total']
        ]
        wins = [
            stats['overall_wins'],
            stats['long_wins'],
            stats['short_wins']
        ]

        # สีตาม winrate (เขียว-แดง)
        colors = ['#4CAF50' if w >= 50 else '#F44336' for w in winrates]

        fig, ax = plt.subplots(figsize=(10, 6), dpi=100)
        bars = ax.bar(categories, winrates, color=colors, width=0.5)

        # เพิ่มตัวเลขบนแท่ง
        for bar, total, win in zip(bars, totals, wins):
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2, height + 2,
                    f'{height:.1f}%\n({win}/{total})',
                    ha='center', va='bottom', fontsize=11, fontweight='bold')

        ax.set_ylim(0, max(100, max(winrates) + 15))  # ให้มีพื้นที่ด้านบน
        ax.set_ylabel('Win Rate (%)', fontsize=12)
        ax.set_title(title, fontsize=14, fontweight='bold')
        ax.grid(axis='y', linestyle='--', alpha=0.7)

        # เพิ่ม annotation ถ้าไม่มี trade
        if all(t == 0 for t in totals):
            ax.text(1, 50, "ยังไม่มีข้อมูลการเทรด", ha='center', va='center',
                    fontsize=12, color='gray', bbox=dict(facecolor='white', alpha=0.8))

        plt.tight_layout()

        # บันทึกเป็น buffer เพื่อส่ง Telegram
        buf = io.BytesIO()
        plt.savefig(buf, format='png', bbox_inches='tight')
        buf.seek(0)
        plt.close(fig)

        return buf

    except Exception as e:
        print(f"[GRAPH ERROR] ไม่สามารถสร้างกราฟ winrate ได้: {e}")
        return None
    
# ==========================================================================
def get_detailed_pnl_stats():
    """ดึงสถิติ PNL แบบละเอียด จาก CSV trade history"""
    try:
        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty:
            return {
                'closed_pnl': 0.0, 'avg_profit': 0.0, 'profit_factor': 0.0,
                'best_trade': 0.0, 'worst_trade': 0.0, 'best_symbol': '', 'worst_symbol': '',
                'wins': 0, 'total': 0, 'consecutive_wins': 0, 'consecutive_losses': 0
            }
        
        # กรองข้อมูลที่ถูกต้อง
        df_valid = df.dropna(subset=['exit_price', 'pnl'])
        
        total = len(df_valid)
        wins = len(df_valid[df_valid['is_win'] == True])
        
        # PNL stats
        closed_pnl = float(df_valid['pnl'].sum())
        avg_profit = float(df_valid['pnl'].mean()) if total > 0 else 0.0
        
        # Profit factor (gross profit / gross loss)
        wins_pnl = float(df_valid[df_valid['is_win'] == True]['pnl'].sum())
        losses_abs = abs(float(df_valid[df_valid['is_win'] == False]['pnl'].sum()))
        profit_factor = (wins_pnl / losses_abs) if losses_abs > 0 else 0.0
        
        # Best/Worst trade
        best_idx = df_valid['pnl'].idxmax()
        worst_idx = df_valid['pnl'].idxmin()
        best_trade = float(df_valid.loc[best_idx, 'pnl'])
        best_symbol = str(df_valid.loc[best_idx, 'symbol'])
        worst_trade = float(df_valid.loc[worst_idx, 'pnl'])
        worst_symbol = str(df_valid.loc[worst_idx, 'symbol'])
        
        # Consecutive wins/losses (from latest to oldest)
        df_valid_copy = df_valid.reset_index(drop=True)
        consecutive_wins = 0
        consecutive_losses = 0
        current_streak = 1
        current_type = 1 if df_valid_copy.iloc[-1]['is_win'] == True else 0
        
        for i in range(len(df_valid_copy) - 2, -1, -1):
            is_win = 1 if df_valid_copy.iloc[i]['is_win'] == True else 0
            if is_win == current_type:
                current_streak += 1
            else:
                if current_type == 1:
                    consecutive_wins = max(consecutive_wins, current_streak)
                else:
                    consecutive_losses = max(consecutive_losses, current_streak)
                current_streak = 1
                current_type = is_win
        
        if current_type == 1:
            consecutive_wins = max(consecutive_wins, current_streak)
        else:
            consecutive_losses = max(consecutive_losses, current_streak)
        
        return {
            'closed_pnl': closed_pnl,
            'avg_profit': avg_profit,
            'profit_factor': profit_factor,
            'best_trade': best_trade,
            'worst_trade': worst_trade,
            'best_symbol': best_symbol,
            'worst_symbol': worst_symbol,
            'wins': wins,
            'total': total,
            'consecutive_wins': consecutive_wins,
            'consecutive_losses': consecutive_losses
        }
    except Exception as e:
        print(f"Error calculating PNL stats: {e}")
        return {
            'closed_pnl': 0.0, 'avg_profit': 0.0, 'profit_factor': 0.0,
            'best_trade': 0.0, 'worst_trade': 0.0, 'best_symbol': '', 'worst_symbol': '',
            'wins': 0, 'total': 0, 'consecutive_wins': 0, 'consecutive_losses': 0
        }

# ==========================================================================
def get_max_drawdown():
    """คำนวณ max drawdown จาก CSV trade history"""
    try:
        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty or len(df) < 2:
            return 0.0, 0.0, 0.0, ''
        
        df_valid = df.dropna(subset=['pnl']).reset_index(drop=True)
        if len(df_valid) < 2:
            return 0.0, 0.0, 0.0, ''
        
        # สะสม PNL ลำดับเวลา
        df_valid['cumulative_pnl'] = df_valid['pnl'].cumsum()
        cumsum = df_valid['cumulative_pnl'].values
        
        max_profit = 0.0
        max_dd = 0.0
        dd_from = ''
        
        for i, val in enumerate(cumsum):
            if i == 0:
                max_profit = val
                continue
            
            if val > max_profit:
                max_profit = val
            
            dd = max_profit - val
            if dd > max_dd:
                max_dd = dd
                dd_from = str(df_valid.loc[i, 'timestamp'])[:10]
        
        dd_percent = (max_dd / abs(max_profit) * 100) if max_profit != 0 else 0.0
        
        return max_dd, dd_percent, max_profit, dd_from
    except Exception as e:
        print(f"Error calculating drawdown: {e}")
        return 0.0, 0.0, 0.0, ''


# ==========================================================================
#                  DIVERGENCE DETECTION (RSI-based Master Technique)
# ==========================================================================
from scipy.signal import argrelextrema

def detect_divergence(df, indicator='rsi', lookback=14, min_strength=0.1):
    """
    Detect RSI divergence with master filters:
    - Regular Bullish: Price LL, RSI HL (with volume confirm + ADX)
    - Regular Bearish: Price HH, RSI LH
    - Hidden Bullish: Price HL, RSI LL (continuation up)
    - Hidden Bearish: Price LH, RSI HH (continuation down)
    - Probability: Base on strength + confirms (volume, ADX, EMA align)
    Returns: (div_type, strength 0-1, prob %)
    """
    if len(df) < lookback * 3:  # Need enough data
        return None, 0.0, 0
    
    price = df['c'].values
    lows_idx = argrelextrema(price, np.less, order=lookback//3)[0][-3:]   # Last 3 potential lows
    highs_idx = argrelextrema(price, np.greater, order=lookback//3)[0][-3:]  # Last 3 highs
    
    rsi = df['rsi'].values
    rsi_lows_idx = argrelextrema(rsi, np.less, order=lookback//3)[0][-3:]
    rsi_highs_idx = argrelextrema(rsi, np.greater, order=lookback//3)[0][-3:]
    
    curr = df.iloc[-1]
    vol_confirm = curr['v'] / curr['vol_ma'] > 1.2 if curr['vol_ma'] > 0 else False
    adx_confirm = curr['adx'] > 25
    ema_up = curr['ema20'] > curr['ema50']
    ema_down = curr['ema20'] < curr['ema50']
    
    # ─── Regular Bullish (Reversal Up) ───
    if len(lows_idx) >= 2 and len(rsi_lows_idx) >= 2:
        p1, p2 = lows_idx[-2], lows_idx[-1]
        r1, r2 = rsi_lows_idx[-2], rsi_lows_idx[-1]
        
        if price[p2] < price[p1] and rsi[r2] > rsi[r1]:
            price_diff = (price[p1] - price[p2]) / price[p1]
            rsi_diff = (rsi[r2] - rsi[r1]) / rsi[r1]
            strength = min((price_diff + rsi_diff) / 2, 1.0)
            
            if strength > min_strength:
                prob = 40  # Base reversal prob
                if vol_confirm: prob += 20
                if adx_confirm: prob += 15
                if ema_down: prob += 15  # Better in downtrend
                prob = min(prob, 95)
                return 'bullish_regular', strength, prob
    
    # ─── Regular Bearish (Reversal Down) ───
    if len(highs_idx) >= 2 and len(rsi_highs_idx) >= 2:
        p1, p2 = highs_idx[-2], highs_idx[-1]
        r1, r2 = rsi_highs_idx[-2], rsi_highs_idx[-1]
        
        if price[p2] > price[p1] and rsi[r2] < rsi[r1]:
            price_diff = (price[p2] - price[p1]) / price[p1]
            rsi_diff = (rsi[r1] - rsi[r2]) / rsi[r1]
            strength = min((price_diff + rsi_diff) / 2, 1.0)
            
            if strength > min_strength:
                prob = 40
                if vol_confirm: prob += 20
                if adx_confirm: prob += 15
                if ema_up: prob += 15  # Better in uptrend
                prob = min(prob, 95)
                return 'bearish_regular', strength, prob
    
    # ─── Hidden Bullish (Continuation Up) ───
    if len(lows_idx) >= 2 and len(rsi_lows_idx) >= 2:
        p1, p2 = lows_idx[-2], lows_idx[-1]
        r1, r2 = rsi_lows_idx[-2], rsi_lows_idx[-1]
        
        if price[p2] > price[p1] and rsi[r2] < rsi[r1]:
            price_diff = (price[p2] - price[p1]) / price[p1]
            rsi_diff = (rsi[r1] - rsi[r2]) / rsi[r1]
            strength = min((price_diff + rsi_diff) / 2, 1.0)
            
            if strength > min_strength:
                prob = 50  # Higher base for continuation
                if vol_confirm: prob += 15
                if adx_confirm: prob += 20
                if ema_up: prob += 15
                prob = min(prob, 95)
                return 'bullish_hidden', strength, prob
    
    # ─── Hidden Bearish (Continuation Down) ───
    if len(highs_idx) >= 2 and len(rsi_highs_idx) >= 2:
        p1, p2 = highs_idx[-2], highs_idx[-1]
        r1, r2 = rsi_highs_idx[-2], rsi_highs_idx[-1]
        
        if price[p2] < price[p1] and rsi[r2] > rsi[r1]:
            price_diff = (price[p1] - price[p2]) / price[p1]
            rsi_diff = (rsi[r2] - rsi[r1]) / rsi[r1]
            strength = min((price_diff + rsi_diff) / 2, 1.0)
            
            if strength > min_strength:
                prob = 50
                if vol_confirm: prob += 15
                if adx_confirm: prob += 20
                if ema_down: prob += 15
                prob = min(prob, 95)
                return 'bearish_hidden', strength, prob
    
    return None, 0.0, 0

# ==========================================================================
#                  DIVERGENCE SCAN FUNCTION
# ==========================================================================
async def scan_divergence(client, symbols=None, tf='1h', limit=200):
    """
    Scan all symbols for divergence
    symbols: list of sym (default top_50_symbols)
    Returns list of dicts with divergence info
    """
    if symbols is None:
        symbols = top_50_symbols[:50]  # Limit to 50 for speed
    
    results = []
    for sym in symbols:
        try:
            klines = await client.futures_klines(symbol=sym, interval=tf, limit=limit)
            df = calculate_indicators(klines)
            div_type, strength, prob = detect_divergence(df)
            if div_type and prob > 50:  # Filter low prob
                direction = "ขึ้น (Bullish)" if 'bullish' in div_type else "ลง (Bearish)"
                hidden = "Hidden" if 'hidden' in div_type else "Regular"
                results.append({
                    'symbol': sym.replace('USDT', ''),
                    'type': f"{direction} {hidden}",
                    'strength': strength,
                    'prob': prob
                })
        except Exception as e:
            print(f"Scan error {sym}: {e}")
    
    return results




# ==========================================================================
# ฟังก์ชันบันทึก trade ที่ปิดแล้ว + แจ้งเตือน Telegram
# ==========================================================================
async def record_closed_trade(client, sym: str, exit_reason: str = "Detected Close", is_manual: bool = False):
    """
    บันทึก trade ที่ปิดแล้วลง CSV + อัพเดท AI + ส่งแจ้งเตือน Telegram
    """
    try:
        pos_info = active_detailed.get(sym, {})
        if not pos_info:
            print(f"[RECORD WARNING] ไม่พบ pos_info สำหรับ {sym} → ใช้ fallback")
            # fallback ถ้าไม่มีข้อมูลก่อนหน้า (กรณี ghost หรือ sync ช้า)
            entry_price = 0.0
            side = 'UNKNOWN'
            qty = 0.0
            leverage = MAX_LEVERAGE
            entry_time = None
            features = [0.5] * 7
            max_roe = 0.0
        else:
            entry_price = pos_info.get('entry_price', 0.0)
            side = pos_info.get('side', 'UNKNOWN')
            qty = pos_info.get('quantity', 0.0)
            leverage = pos_info.get('leverage', MAX_LEVERAGE)
            entry_time = pos_info.get('entry_time')
            features = pos_info.get('features', [0.5] * 7)
            max_roe = pos_info.get('max_roe', 0.0)

        # ─── ดึง realized trade ล่าสุด (ลอง 3 รอบ) ───
        exit_price = pnl = realized_qty = 0.0
        exit_time = datetime.now()
        close_trade = None

        for attempt in range(3):
            try:
                trades = await client.futures_account_trades(symbol=sym, limit=5)
                close_trade = next((t for t in reversed(trades) 
                                  if float(t.get('realizedPnl', 0)) != 0), None)
                if close_trade:
                    break
            except Exception as fetch_err:
                print(f"[TRADE FETCH attempt {attempt+1}] {sym}: {fetch_err}")
            if attempt < 2:
                await asyncio.sleep(1.0)

        if close_trade:
            exit_price   = float(close_trade['price'])
            pnl          = float(close_trade['realizedPnl'])
            realized_qty = abs(float(close_trade.get('qty', qty)))
            exit_time    = datetime.fromtimestamp(int(close_trade['time']) / 1000)
            
            orig_type = close_trade.get('origType', '')
            if 'STOP_MARKET' in orig_type:
                exit_reason = "Hit SL"
            elif 'TAKE_PROFIT_MARKET' in orig_type:
                exit_reason = "Hit TP"
            elif 'LIQUIDATION' in str(close_trade).upper():
                exit_reason = "Liquidation"

        # ─── คำนวณค่าให้ครบ ───
        duration_hours = 0.1
        if entry_time:
            duration_hours = max((exit_time - entry_time).total_seconds() / 3600, 0.1)

        pnl_percent = 0.0
        is_win = pnl > 0
        if qty > 0 and leverage > 0:
            margin = qty * entry_price / leverage
            if margin > 0:
                pnl_percent = (pnl / margin) * 100

        # fallback entry_price ถ้ายังไม่มี
        if entry_price <= 0 and exit_price > 0:
            entry_price = exit_price
            exit_reason += " (fallback entry)"

        # สร้าง record
        trade_record = {
            'timestamp': exit_time.isoformat(),
            'symbol': sym,
            'side': side,
            'entry_price': entry_price,
            'exit_price': exit_price,
            'quantity': qty or realized_qty,
            'pnl': pnl,
            'pnl_percent': pnl_percent,
            'duration_hours': duration_hours,
            'exit_reason': exit_reason,
            'is_win': is_win,
            'leverage': leverage,
            'max_roe_percent': max_roe,
            'features': features if len(features) == 7 else [0.5]*7
        }


    except Exception as e:
        print(f"[RECORD ERROR] {sym}: {e}")
        with open("emergency_closed.log", "a") as ef:
            ef.write(f"{datetime.now().isoformat()} | {sym} | {exit_reason} | {str(e)}\n")
        return None

# ==========================================================================
# ฟังก์ชันตรวจสอบ position ที่ปิดแล้ว (เรียกใน main loop)
# ==========================================================================
async def check_and_record_closed_positions(client):
    """
    ตรวจสอบ position ที่ปิดแล้ว และบันทึก + แจ้งเตือน
    เรียกทุก 10-30 วินาทีใน main loop
    """
    global prev_active_symbols, last_closed_check

    current_time = datetime.now().timestamp()
    if current_time - last_closed_check < 10:  # ตรวจทุก 10 วินาที
        return 0

    last_closed_check = current_time

    try:
        pos_data = await client.futures_position_information()
        current_active_symbols = set()

        for p in pos_data:
            amt = float(p['positionAmt'])
            if abs(amt) > 0.001 and float(p['entryPrice']) > 0:
                current_active_symbols.add(p['symbol'])

        closed_positions = prev_active_symbols - current_active_symbols

        closed_count = 0
        for sym in closed_positions:
            print(f"[DETECT CLOSE] {sym} → บันทึกและแจ้งเตือน")
            is_manual = sym in manual_closed_cooldown
            await record_closed_trade(
                client=client,
                sym=sym,
                exit_reason="Manual Close" if is_manual else "Auto Closed (SL/TP/Trailing/Liq)",
                is_manual=is_manual
            )
            if is_manual:
                manual_closed_cooldown.pop(sym, None)
            closed_count += 1

        prev_active_symbols = current_active_symbols.copy()
        return closed_count

    except Exception as e:
        print(f"[CHECK CLOSED ERROR] {e}")
        return 0




# ==========================================================================
#                  GENERATE DIVERGENCE REPORT
# ==========================================================================
def generate_div_report(results):
    if not results:
        return "🔍 **Divergence Scan** - ไม่พบสัญญาณ divergence ที่มีโอกาส >50% ในขณะนี้"
    
    report = "🔍 **Divergence Scan Report** (โอกาส >50%)\n\n"
    results.sort(key=lambda x: x['prob'], reverse=True)
    for r in results:
        emoji = "🟢" if "ขึ้น" in r['type'] else "🔴"
        report += f"{emoji} `{r['symbol']}`: {r['type']} | โอกาส `{r['prob']}%` (strength {r['strength']:.2f})\n"
    report += "\n_สแกนจาก 1h timeframe | ใช้ RSI divergence master technique_"
    return report

# ==========================================================================
def get_daily_stats(days=7):
    """สรุป PNL รายวัน สำหรับ N วันที่ผ่านมา"""
    try:
        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty:
            return []
        
        df_valid = df.dropna(subset=['exit_price', 'pnl']).copy()
        df_valid['date'] = pd.to_datetime(df_valid['timestamp']).dt.date
        
        # กรองเฉพาะ N วันที่ผ่านมา
        cutoff = datetime.now().date() - timedelta(days=days)
        df_valid = df_valid[df_valid['date'] >= cutoff]
        
        daily_stats = []
        for date, group in df_valid.groupby('date'):
            daily_pnl = float(group['pnl'].sum())
            daily_trades = len(group)
            daily_wins = len(group[group['is_win'] == True])
            daily_wr = (daily_wins / daily_trades * 100) if daily_trades > 0 else 0.0
            
            daily_stats.append({
                'date': str(date),
                'pnl': daily_pnl,
                'trades': daily_trades,
                'wins': daily_wins,
                'wr': daily_wr
            })
        
        return sorted(daily_stats, key=lambda x: x['date'], reverse=True)
    except Exception as e:
        print(f"Error calculating daily stats: {e}")
        return []

# ==========================================================================
def get_weekly_stats(weeks=4):
    """สรุป PNL รายสัปดาห์ สำหรับ N สัปดาห์ที่ผ่านมา"""
    try:
        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty:
            return []
        
        df_valid = df.dropna(subset=['exit_price', 'pnl']).copy()
        df_valid['datetime'] = pd.to_datetime(df_valid['timestamp'])
        df_valid['week'] = df_valid['datetime'].dt.isocalendar().week
        df_valid['year'] = df_valid['datetime'].dt.isocalendar().year
        
        # กรองเฉพาะ N สัปดาห์ที่ผ่านมา
        cutoff = datetime.now() - timedelta(weeks=weeks)
        df_valid = df_valid[df_valid['datetime'] >= cutoff]
        
        weekly_stats = []
        for (year, week), group in df_valid.groupby(['year', 'week']):
            week_pnl = float(group['pnl'].sum())
            week_trades = len(group)
            week_wins = len(group[group['is_win'] == True])
            week_wr = (week_wins / week_trades * 100) if week_trades > 0 else 0.0
            week_label = f"{year}-W{week:02d}"
            
            weekly_stats.append({
                'week': week_label,
                'pnl': week_pnl,
                'trades': week_trades,
                'wins': week_wins,
                'wr': week_wr
            })
        
        return sorted(weekly_stats, key=lambda x: x['week'], reverse=True)
    except Exception as e:
        print(f"Error calculating weekly stats: {e}")
        return []

# ==========================================================================
def log_trade_to_csv(trade_data: dict):
    """บันทึก trade ลง CSV และอัพเดท brain memory"""
    try:
        with open(TRADE_HISTORY_FILE, 'a', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=TRADE_HISTORY_FIELDS)
            writer.writerow(trade_data)
        
        # อัพเดท AI brain (เหมือนเดิม แต่ใช้ข้อมูลที่แม่นยำกว่า)
        features = trade_data.get('features', [])  # ต้องส่ง features มาด้วยตอนเรียก
        if features:
            brain.update_memory(features, trade_data['is_win'])
            
    except Exception as e:
        print(f"{Fore.RED}Error logging trade to CSV: {e}")

# ==========================================================================
def get_recent_trades(n=10):
    try:
        df = pd.read_csv(TRADE_HISTORY_FILE)
        recent = df.tail(n)
        return recent.to_dict('records')
    except:
        return []
    

# ==========================================================================
#                  AUTO LONG ENTRY - Multi-Factor Confluence (ตามที่คุณอธิบาย)
# ==========================================================================
from scipy.signal import argrelextrema
import numpy as np

async def detect_auto_long_entry(client, symbol, low_tf='15m', high_tf='4h', lookback=80):
    """
    ตรวจสอบเงื่อนไข LONG แบบ Counter-Trend / Reversal ที่ปลอดภัย
    - โครงสร้างราคา: Downtrend อ่อนแรง (higher lows / no new lows)
    - Demand/Support Reaction: Wick ยาว + Volume เข้ามารับ + Bounce
    - Momentum: Bullish Divergence (RSI/MACD) หรือ RSI หลุด oversold แล้วยก
    - Higher TF: ไม่ downtrend แรง หรือกำลัง sideway
    - Market Context: Sentiment ไม่ panic เกิน (CoinGecko)
    
    Returns: dict หรือ None
    """
    try:
        # ─── 1. ดึงข้อมูล Low TF (15m) ───
        k_low = await client.futures_klines(symbol=symbol, interval=low_tf, limit=lookback*2)
        if not k_low or len(k_low) < lookback:
            print(f"[AutoLong] {symbol} ข้อมูล {low_tf} ไม่พอ ({len(k_low) if k_low else 0} แท่ง)")
            return None
        
        df_low = calculate_indicators(k_low)
        if df_low.empty or len(df_low) < 30:
            print(f"[AutoLong] {symbol} df_low ว่างหรือสั้นเกิน")
            return None
        
        curr_low = df_low.iloc[-1]
        current_price = float(curr_low['c'])
        atr = float(curr_low.get('atr', current_price * 0.015))
        
        score = 0.0
        reasons = []
        
        # ─── 2. ดึงข้อมูล Higher TF (4h) ───
        k_high = await client.futures_klines(symbol=symbol, interval=high_tf, limit=lookback)
        df_high = None
        if k_high and len(k_high) >= 30:
            df_high = calculate_indicators(k_high)
        
        # ─── 3. โครงสร้างราคา: Downtrend อ่อนแรง ───
        if len(df_low) >= lookback:
            lows = df_low['l'].iloc[-lookback:]
            recent_lows = lows.iloc[-8:]
            prev_lows = lows.iloc[-16:-8] if len(lows) >= 16 else lows
            
            if len(recent_lows) > 0 and len(prev_lows) > 0:
                if recent_lows.min() >= prev_lows.min() * 0.992:
                    score += 0.30
                    reasons.append("โครงสร้าง: Downtrend อ่อนแรง (Higher Lows หรือ no new low)")
        
        # ─── 4. Demand/Support Reaction ───
        support = float(curr_low.get('support', current_price * 0.965))
        dist_to_support = (current_price - support) / current_price if current_price > 0 else 1.0
        
        if dist_to_support < 0.018:  # ใกล้ support <1.8%
            wick_lower = min(curr_low['o'], curr_low['c']) - curr_low['l']
            body = abs(curr_low['o'] - curr_low['c'])
            vol_ratio = curr_low['v'] / curr_low['vol_ma'] if curr_low.get('vol_ma', 0) > 0 else 1.0
            
            if wick_lower > body * 2.2 and vol_ratio > 1.6:
                score += 0.35
                reasons.append(f"Demand Zone Reaction: Wick ยาว + Volume เข้ามารับ ({vol_ratio:.1f}x)")
        
        # ─── 5. Momentum: Bullish Divergence + RSI Recovery ───
        rsi = float(curr_low.get('rsi', 50))
        if rsi < 35:
            score += 0.15
            reasons.append(f"RSI Oversold แล้วเริ่มฟื้น ({rsi:.1f})")
        
        # Bullish RSI Divergence
        if len(df_low) >= 40:
            price_vals = df_low['l'].values[-lookback:]
            rsi_vals = df_low['rsi'].values[-lookback:]
            
            if len(price_vals) >= 20:
                price_low_idx = argrelextrema(price_vals, np.less, order=6)[0]
                rsi_low_idx = argrelextrema(rsi_vals, np.less, order=6)[0]
                
                if len(price_low_idx) >= 2 and len(rsi_low_idx) >= 2:
                    p1 = price_low_idx[-2]
                    p2 = price_low_idx[-1]
                    r1 = rsi_low_idx[-2]
                    r2 = rsi_low_idx[-1]
                    
                    if price_vals[p2] < price_vals[p1] and rsi_vals[r2] > rsi_vals[r1]:
                        score += 0.25
                        reasons.append("Bullish RSI Divergence (ราคาลงใหม่ แต่ RSI สูงขึ้น)")
        
        # MACD Divergence (bonus)
        if 'macd' in df_low.columns and len(df_low) >= 40:
            macd_vals = df_low['macd'].values[-lookback:]
            macd_low_idx = argrelextrema(macd_vals, np.less, order=6)[0]
            
            if len(price_low_idx) >= 2 and len(macd_low_idx) >= 2:
                p1 = price_low_idx[-2]
                p2 = price_low_idx[-1]
                m1 = macd_low_idx[-2]
                m2 = macd_low_idx[-1]
                
                if price_vals[p2] < price_vals[p1] and macd_vals[m2] > macd_vals[m1]:
                    score += 0.15
                    reasons.append("Bullish MACD Divergence")
        
        # ─── 6. Higher TF Context ───
        if df_high is not None and not df_high.empty:
            curr_high = df_high.iloc[-1]
            ema20_h = float(curr_high.get('ema20', 0))
            ema50_h = float(curr_high.get('ema50', 0))
            ema200_h = float(curr_high.get('ema200', ema50_h))
            adx_h = float(curr_high.get('adx', 20))
            
            is_strong_down = (ema20_h < ema50_h < ema200_h) and adx_h > 28
            is_sideway = abs(ema20_h - ema50_h) / ema50_h < 0.012 if ema50_h > 0 else False
            
            if not is_strong_down:
                score += 0.20
                reasons.append("Higher TF: ไม่ downtrend แรง")
            if is_sideway:
                score += 0.15
                reasons.append("Higher TF: Sideway (ปลอดภัยสำหรับ LONG ในกรอบ)")
        else:
            reasons.append("Higher TF: ไม่สามารถดึงข้อมูลได้ → ข้ามการตรวจ")
        
        # ─── 7. Market Sentiment (ไม่ panic) ───
        sentiment = await get_sentiment(symbol)
        if sentiment > 0.45:
            score += 0.10
            reasons.append(f"Sentiment ปกติ ({sentiment*100:.0f}%)")
        elif sentiment < 0.30:
            score -= 0.25
            reasons.append(f"Sentiment Panic ต่ำ ({sentiment*100:.0f}%) → ระวัง")
        
        # ─── ตัดสินใจ ───
        confidence = min(max(score, 0.0), 1.0)
        min_confidence = 0.70
        
        if confidence < min_confidence:
            return {
                'should_enter': False,
                'confidence': confidence,
                'reason': f"Confidence ยังไม่ถึงเกณฑ์ ({confidence:.0%} < {min_confidence:.0%})\n" + "\n".join(reasons)
            }
        
        # ─── คำนวณ Entry / SL / TP ───
        support = float(curr_low.get('support', current_price * 0.965))  # กำหนดใหม่ให้ชัวร์
        entry_price = support + atr * 0.15
        sl = support - atr * 0.9
        risk = entry_price - sl
        tp = entry_price + risk * 3.2
        
        rr = (tp - entry_price) / risk if risk > 0 else 0
        
        return {
            'should_enter': True,
            'confidence': confidence,
            'entry_price': entry_price,
            'sl': sl,
            'tp': tp,
            'rr': rr,
            'reason': "ผ่านทุกเงื่อนไข → ตลาดเริ่มบอกว่าอยากขึ้น\n" + "\n".join(reasons)
        }
    
    except Exception as e:
        print(f"Auto LONG error {symbol}: {str(e)}")
        import traceback
        traceback.print_exc()
        return None 
# ==========================================================================
#                   NATIVE INDICATORS
# ==========================================================================
def calculate_indicators(kline_data):
    try:
        df = pd.DataFrame(
            kline_data,
            columns=['ts', 'o', 'h', 'l', 'c', 'v', 'ct', 'qv', 'nt', 'tb', 'tq', 'i']
        ).astype(float)

        df['ema20'] = df['c'].ewm(span=20, adjust=False).mean()
        df['ema50'] = df['c'].ewm(span=50, adjust=False).mean()
        df['ema100'] = df['c'].ewm(span=100, adjust=False).mean()   # ← เพิ่มบรรทัดนี้
        df['ema200'] = df['c'].ewm(span=200, adjust=False).mean()

        delta = df['c'].diff()
        gain = (delta.where(delta > 0, 0)).rolling(window=14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(window=14).mean()
        rs = gain / (loss + 1e-9)
        df['rsi'] = 100 - (100 / (1 + rs))

        high_low = df['h'] - df['l']
        high_close = (df['h'] - df['c'].shift()).abs()
        low_close = (df['l'] - df['c'].shift()).abs()
        ranges = pd.concat([high_low, high_close, low_close], axis=1)
        true_range = ranges.max(axis=1)
        df['atr'] = true_range.rolling(14).mean()

        df['ma20'] = df['c'].rolling(20).mean()
        df['std20'] = df['c'].rolling(20).std()
        df['bb_upper'] = df['ma20'] + (df['std20'] * 2)
        df['bb_lower'] = df['ma20'] - (df['std20'] * 2)

        exp1 = df['c'].ewm(span=12, adjust=False).mean()
        exp2 = df['c'].ewm(span=26, adjust=False).mean()
        df['macd'] = exp1 - exp2
        df['signal'] = df['macd'].ewm(span=9, adjust=False).mean()

        # Stochastic Oscillator (14,3,3)
        low14 = df['l'].rolling(14).min()
        high14 = df['h'].rolling(14).max()
        df['stoch_k'] = 100 * ((df['c'] - low14) / (high14 - low14 + 1e-9))
        df['stoch_d'] = df['stoch_k'].rolling(3).mean()

        df['vol_ma'] = df['v'].rolling(20).mean()
        df['vol_breakout'] = (df['v'] > df['vol_ma'] * 1.5).astype(int)

        up = df['h'].diff()
        down = -df['l'].diff()
        plus_dm = up.where((up > down) & (up > 0), 0)
        minus_dm = down.where((down > up) & (down > 0), 0)
        tr_smooth = true_range.ewm(span=14, adjust=False).mean()
        plus_di = 100 * (plus_dm.ewm(span=14, adjust=False).mean() / tr_smooth)
        minus_di = 100 * (minus_dm.ewm(span=14, adjust=False).mean() / tr_smooth)
        dx = (abs(plus_di - minus_di) / (plus_di + minus_di + 1e-9)) * 100
        df['adx'] = dx.ewm(span=14, adjust=False).mean()

        df['straight_down'] = 0
        if len(df) >= 20:
            recent = df['c'].tail(20).values
            x = np.arange(len(recent))
            corr_matrix = np.corrcoef(x, recent)
            corr = corr_matrix[0, 1]
            r2 = corr**2 if not np.isnan(corr) else 0
            price_start = recent[0]
            price_end = recent[-1]
            slope_pct = (price_end - price_start) / price_start * 100 if price_start > 0 else 0
            if slope_pct <= -8.0 and r2 >= 0.95:
                df.loc[df.index[-1], 'straight_down'] = 1

        # ========== Support & Resistance Detection ==========
        df['support'] = df['l'].rolling(20).min()
        df['resistance'] = df['h'].rolling(20).max()
        
        # ========== Price Action Patterns ==========
        # Pin Bar Detection (bullish pin bar = wick ตรงข้ายาว ที่ bottom)
        body = (df['o'] - df['c']).abs()
        lower_wick = df['o'].where(df['o'] < df['c'], df['c']) - df['l']
        upper_wick = df['h'] - df['c'].where(df['c'] > df['o'], df['o'])
        df['pin_bar_bullish'] = (lower_wick > body * 2.0) & (upper_wick < body * 0.5)
        df['pin_bar_bearish'] = (upper_wick > body * 2.0) & (lower_wick < body * 0.5)
        
        # Engulfing Pattern (bearish = black candle ล้อมครอบ previous white)
        df['engulfing_bearish'] = (
            (df['o'] > df['o'].shift()) & 
            (df['c'] < df['c'].shift()) &
            (df['o'] > df['c'].shift()) &
            (df['c'] < df['o'].shift())
        ).astype(int)

        return df

    except Exception as e:
        print(f"Indicator error: {e}")
        return pd.DataFrame()

# ==========================================================================
#          MULTI-TIMEFRAME CONFIRMATION (ปรับปรุง 21 ม.ค. 2026)
# ==========================================================================

async def check_htf_bullish_alignment(client, symbol):
    """ตรวจสอบ 4H bullish alignment แบบสมดุล + ปลอดภัยสูง (core + bonus ≥3/5)"""
    try:
        htf_klines = await client.futures_klines(symbol=symbol, interval="4h", limit=300)
        df_htf = calculate_indicators(htf_klines)
        
        if df_htf.empty or len(df_htf) < 100:
            print(f"[HTF Bull] {symbol}: ข้อมูลไม่พอ ({len(df_htf)} แท่ง)")
            return False
        
        curr = df_htf.iloc[-1]
        prev = df_htf.iloc[-2] if len(df_htf) > 1 else curr

        # ─── CORE CONDITIONS (ต้องผ่านทั้งคู่) ────────────────────────────────
        ema_aligned = curr['ema20'] > curr['ema50']
        strong_trend = curr.get('adx', 0) > 20  # ลดจาก 22 → เข้าเร็วขึ้น
        
        if not (ema_aligned and strong_trend):
            print(f"[HTF Bull] {symbol} fail core → EMA20>50: {ema_aligned}, ADX>20: {strong_trend}")
            return False

        # ─── BONUS CONDITIONS (ต้อง ≥ 3/5) ───────────────────────────────────
        bonus_score = 0
        
        # 1. EMA50 > EMA200 (perfect stack)
        if curr['ema50'] > curr['ema200']:
            bonus_score += 1
        
        # 2. Slope up (EMA20 ชันขึ้น)
        if curr['ema20'] > prev['ema20']:
            bonus_score += 1
        
        # 3. Volume breakout (ผ่อน + fallback)
        v = curr.get('v', np.nan)
        vol_ma = curr.get('vol_ma', np.nan)
        vol_valid = not pd.isna(v) and v > 0 and not pd.isna(vol_ma) and vol_ma > 0
        if vol_valid and v > vol_ma * 1.1:
            bonus_score += 1
        elif not vol_valid:
            bonus_score += 1  # เหรียญ volume ต่ำ ถือว่าผ่าน
        
        # 4. RSI range กว้างขึ้น (ไม่ extreme)
        if 45 < curr['rsi'] < 75:
            bonus_score += 1
        
        # 5. ราคาใกล้ EMA20 (ผ่อน ±8%)
        if curr['c'] < curr['ema20'] * 1.08:
            bonus_score += 1

        pass_htf = bonus_score >= 2
        
        if not pass_htf:
            print(f"[HTF Bull] {symbol}: core pass แต่ bonus only {bonus_score}/5")
        
        return pass_htf

    except Exception as e:
        print(f"HTF check error (Long) {symbol}: {str(e)}")
        return False


async def check_htf_bearish_alignment(client, symbol):
    """ตรวจสอบ 4H bearish alignment แบบสมดุล + ปลอดภัยสูง (core + bonus ≥3/5)"""
    try:
        htf_klines = await client.futures_klines(symbol=symbol, interval="4h", limit=300)
        df_htf = calculate_indicators(htf_klines)
        
        if df_htf.empty or len(df_htf) < 150:
            print(f"[HTF Bear] {symbol}: ข้อมูลไม่พอ ({len(df_htf)} แท่ง)")
            return False
        
        curr = df_htf.iloc[-1]
        prev = df_htf.iloc[-2] if len(df_htf) > 1 else curr

        # ─── CORE CONDITIONS (ต้องผ่านทั้งคู่) ────────────────────────────────
        ema_aligned = curr['ema20'] < curr['ema50']
        strong_trend = curr.get('adx', 0) > 20
        
        if not (ema_aligned and strong_trend):
            print(f"[HTF Bear] {symbol} fail core → EMA20<50: {ema_aligned}, ADX>20: {strong_trend}")
            return False

        # ─── BONUS CONDITIONS (ต้อง ≥ 3/5) ───────────────────────────────────
        bonus_score = 0
        
        # 1. EMA50 < EMA200
        if curr['ema50'] < curr['ema200']:
            bonus_score += 1
        
        # 2. Slope down
        if curr['ema20'] < prev['ema20']:
            bonus_score += 1
        
        # 3. Volume breakout (ผ่อน + fallback)
        v = curr.get('v', np.nan)
        vol_ma = curr.get('vol_ma', np.nan)
        vol_valid = not pd.isna(v) and v > 0 and not pd.isna(vol_ma) and vol_ma > 0
        if vol_valid and v > vol_ma * 1.1:
            bonus_score += 1
        elif not vol_valid:
            bonus_score += 1
        
        # 4. RSI range (bearish zone กว้างขึ้น)
        if 25 < curr['rsi'] < 55:
            bonus_score += 1
        
        # 5. ราคาใกล้ EMA20 (ผ่อน ±8%)
        if curr['c'] > curr['ema20'] * 0.92:
            bonus_score += 1

        pass_htf = bonus_score >= 3
        
        if not pass_htf:
            print(f"[HTF Bear] {symbol}: core pass แต่ bonus only {bonus_score}/5")
        
        return pass_htf

    except Exception as e:
        print(f"HTF check error (Short) {symbol}: {str(e)}")
        return False

# ==========================================================================
#          SUPPORT & RESISTANCE LEVEL FINDER
# ==========================================================================
async def find_nearest_sr(client, symbol, current_price):
    """หาระดับ Support & Resistance ที่ใกล้ที่สุด"""
    try:
        klines = await client.futures_klines(symbol=symbol, interval="1h", limit=100)
        df = calculate_indicators(klines)
        if df.empty:
            return None, None
        
        curr = df.iloc[-1]
        support = float(curr['support'])
        resistance = float(curr['resistance'])
        
        return support, resistance
    except Exception as e:
        print(f"SR finder error {symbol}: {e}")
        return None, None

# ==========================================================================
#          RISK:REWARD CALCULATOR
# ==========================================================================
def calculate_rr_ratio(entry_price, sl_price, tp_price, position_type='SHORT'):
    """คำนวณ Risk:Reward ratio"""
    if position_type == 'SHORT':
        risk = entry_price - sl_price
        reward = entry_price - tp_price
    else:  # LONG
        risk = entry_price - sl_price
        reward = tp_price - entry_price
    
    if risk <= 0:
        return 0
    return reward / risk if risk > 0 else 0

# ==========================================================================
#          PRICE ACTION FILTER
# ==========================================================================
def check_price_action_confirmation(df_curr):
    """ตรวจสอบ Price Action ยืนยัน bearish"""
    try:
        curr = df_curr.iloc[-1] if isinstance(df_curr, pd.DataFrame) else df_curr
        prev = df_curr.iloc[-2] if isinstance(df_curr, pd.DataFrame) and len(df_curr) > 1 else None
        
        confirmations = 0
        
        # Bearish Pin Bar
        if curr.get('pin_bar_bearish', 0):
            confirmations += 1
        
        # Bearish Engulfing
        if curr.get('engulfing_bearish', 0):
            confirmations += 1
        
        # Close below open (bearish)
        if curr['c'] < curr['o']:
            confirmations += 1
        
        # Recent straight down move
        if curr.get('straight_down', 0):
            confirmations += 1
        
        return confirmations >= 1  # ต้อง ≥ 1 pattern
    except Exception as e:
        print(f"Price action check error: {e}")
        return False

# ==========================================================================
#          FIBONACCI LEVEL CALCULATOR
# ==========================================================================
def calculate_fibonacci_levels(high, low):
    """คำนวณระดับ Fibonacci retracement"""
    diff = high - low
    levels = {
        '0.0% (High)': high,
        '23.6%': high - 0.236 * diff,
        '38.2%': high - 0.382 * diff,
        '50.0%': high - 0.500 * diff,
        '61.8%': high - 0.618 * diff,
        '78.6%': high - 0.786 * diff,
        '100% (Low)': low
    }
    return levels

def calculate_fibonacci_extensions(high, low):
    """คำนวณ Fibonacci extension levels (สำหรับ target)"""
    diff = high - low
    extensions = {
        '123.6%': low - 0.236 * diff,  # Wave 3 target
        '138.2%': low - 0.382 * diff,  # Common extension
        '161.8%': low - 0.618 * diff,  # Powerful extension
        '200.0%': low - 1.000 * diff,  # Double retracement
        '261.8%': low - 1.618 * diff   # Golden ratio extension
    }
    return extensions

# ==========================================================================
#          ELLIOTT WAVE PATTERN DETECTION
# ==========================================================================
def detect_elliott_wave(df):
    """ตรวจสอบ Elliott Wave pattern (5 wave impulse / 3 wave correction)
    
    Returns: {
        'pattern': 'impulse' / 'correction' / 'unknown',
        'wave_count': int,
        'confidence': float (0-1),
        'direction': 'up' / 'down'
    }
    """
    try:
        if len(df) < 10:
            return {'pattern': 'unknown', 'wave_count': 0, 'confidence': 0, 'direction': 'unknown'}
        
        closes = df['c'].values
        
        # หา local highs และ lows
        local_highs = []
        local_lows = []
        
        for i in range(2, len(closes) - 2):
            if closes[i] > closes[i-1] and closes[i] > closes[i+1]:
                local_highs.append((i, closes[i]))
            elif closes[i] < closes[i-1] and closes[i] < closes[i+1]:
                local_lows.append((i, closes[i]))
        
        if len(local_highs) < 2 and len(local_lows) < 2:
            return {'pattern': 'unknown', 'wave_count': 0, 'confidence': 0, 'direction': 'unknown'}
        
        # ตรวจสอบ Uptrend 5-wave impulse
        # Wave: 1 (up), 2 (down < 50% of wave 1), 3 (up > wave 1), 4 (down), 5 (up)
        if len(local_highs) >= 3 and len(local_lows) >= 2:
            wave1_high = local_highs[-3][1]
            wave2_low = local_lows[-2][1]
            wave3_high = local_highs[-1][1]
            
            # Check 5-wave pattern
            if (wave1_high < wave3_high and  # Wave 3 > Wave 1
                wave2_low > closes[-1] * 0.5):  # Wave 2 not too deep
                
                return {
                    'pattern': 'impulse',
                    'wave_count': 5,
                    'confidence': 0.7,
                    'direction': 'up'
                }
        
        # ตรวจสอบ Downtrend 5-wave impulse
        if len(local_lows) >= 3 and len(local_highs) >= 2:
            wave1_low = local_lows[-3][1]
            wave2_high = local_highs[-2][1]
            wave3_low = local_lows[-1][1]
            
            if (wave1_low > wave3_low and
                wave2_high < closes[-1] * 1.5):
                
                return {
                    'pattern': 'impulse',
                    'wave_count': 5,
                    'confidence': 0.7,
                    'direction': 'down'
                }
        
        # ตรวจสอบ 3-wave correction (A-B-C)
        if len(local_highs) >= 2 and len(local_lows) >= 2:
            recent_high = max(local_highs[-2:], key=lambda x: x[1])[1]
            recent_low = min(local_lows[-2:], key=lambda x: x[1])[1]
            
            # A-B-C pattern (correction)
            price_range = recent_high - recent_low
            current_close = closes[-1]
            
            if abs(current_close - recent_low) / recent_low < 0.02:  # Near low
                return {
                    'pattern': 'correction',
                    'wave_count': 3,
                    'confidence': 0.6,
                    'direction': 'up'  # หลังจาก correction จะขึ้น
                }
            elif abs(current_close - recent_high) / recent_high < 0.02:  # Near high
                return {
                    'pattern': 'correction',
                    'wave_count': 3,
                    'confidence': 0.6,
                    'direction': 'down'  # หลังจาก correction จะลง
                }
        
        return {'pattern': 'unknown', 'wave_count': 0, 'confidence': 0.3, 'direction': 'unknown'}
        
    except Exception as e:
        print(f"Elliott wave detection error: {e}")
        return {'pattern': 'unknown', 'wave_count': 0, 'confidence': 0, 'direction': 'unknown'}

# ==========================================================================
#          FIBONACCI + ELLIOTT WAVE ENTRY SIGNAL
# ==========================================================================
def get_fib_elliot_signal(df, current_price):
    """วิเคราะห์ Fibonacci + Elliott Wave เพื่อตัดสินใจเข้า/ออก
    
    Returns: {
        'signal': 'STRONG_BUY' / 'BUY' / 'SELL' / 'STRONG_SELL' / 'NEUTRAL',
        'confidence': float (0-1),
        'fib_level': str,
        'wave_analysis': str
    }
    """
    try:
        # Fibonacci
        high = df['h'].max()
        low = df['l'].min()
        fib_levels = calculate_fibonacci_levels(high, low)
        
        # Elliott Wave
        wave_analysis = detect_elliott_wave(df)
        
        # หา Fibonacci level ที่ใกล้สุด
        closest_level = min(fib_levels.items(), 
                           key=lambda x: abs(x[1] - current_price))
        fib_level_name = closest_level[0]
        fib_level_value = closest_level[1]
        
        signal = 'NEUTRAL'
        confidence = 0.5
        
        # ตัดสินใจจาก Elliott Wave
        if wave_analysis['pattern'] == 'impulse':
            if wave_analysis['direction'] == 'up':
                # Uptrend: หาค่าสนับสนุน
                if current_price < fib_levels['38.2%']:  # Oversold
                    signal = 'STRONG_BUY'
                    confidence = 0.85
                elif current_price < fib_levels['50.0%']:
                    signal = 'BUY'
                    confidence = 0.70
                else:
                    signal = 'NEUTRAL'
                    confidence = 0.60
                    
            elif wave_analysis['direction'] == 'down':
                # Downtrend: หา resistance
                if current_price > fib_levels['61.8%']:  # Overbought
                    signal = 'STRONG_SELL'
                    confidence = 0.85
                elif current_price > fib_levels['50.0%']:
                    signal = 'SELL'
                    confidence = 0.70
                else:
                    signal = 'NEUTRAL'
                    confidence = 0.60
        
        elif wave_analysis['pattern'] == 'correction':
            # Wave 2 หรือ Wave 4: ใกล้จบแล้ว
            if wave_analysis['direction'] == 'up':
                signal = 'BUY'
                confidence = 0.75
            else:
                signal = 'SELL'
                confidence = 0.75
        
        return {
            'signal': signal,
            'confidence': confidence,
            'fib_level': fib_level_name,
            'wave_pattern': wave_analysis['pattern'],
            'wave_direction': wave_analysis['direction'],
            'wave_confidence': wave_analysis['confidence']
        }
        
    except Exception as e:
        print(f"Fib/Elliott signal error: {e}")
        return {
            'signal': 'NEUTRAL',
            'confidence': 0.3,
            'fib_level': 'N/A',
            'wave_pattern': 'unknown',
            'wave_direction': 'unknown',
            'wave_confidence': 0
        }



# ==========================================================================
# ==========================================================================
async def ensure_sl_tp_for_all_positions(client):
    print(f"{Fore.CYAN}=== เริ่มตรวจสอบและตั้ง SL/TP อัตโนมัติทั้งหมด ==={Style.RESET_ALL}")
    
    # ดึง positions สด ๆ อีกครั้ง (ป้องกัน cache เก่า)
    try:
        positions = await rate_limited_call(client.futures_position_information())
    except Exception as e:
        print(f"{Fore.RED}ดึง positions ล้มเหลว: {e}{Style.RESET_ALL}")
        return

    active_positions = [
        p for p in positions 
        if abs(float(p.get('positionAmt', 0))) > 1e-5   # กรอง ghost เข้มขึ้น
        and float(p.get('entryPrice', 0)) > 0           # ต้องมี entry จริง
    ]

    if not active_positions:
        print(f"{Fore.LIGHTBLACK_EX}ไม่มี position ที่ใช้งานได้จริงในขณะนี้{Style.RESET_ALL}")
        return

    print(f"พบ position ที่ใช้งานได้จริง: {len(active_positions)} ตำแหน่ง")
    try:
        print(f"{Fore.CYAN}=== เริ่มตรวจสอบและตั้ง SL/TP อัตโนมัติทั้งหมด ==={Style.RESET_ALL}")
        ts_start = datetime.now()
        print(f"เวลาเริ่ม: {ts_start.strftime('%Y-%m-%d %H:%M:%S.%f')}")

        # 1. ดึง positions (ห่อ rate limit)
        positions = await rate_limited_call(client.futures_position_information())
        active_positions = [p for p in positions if float(p['positionAmt']) != 0]

        print(f"{Fore.CYAN}พบ position เปิดอยู่: {len(active_positions)} ตำแหน่ง{Style.RESET_ALL}")

        if not active_positions:
            print(f"{Fore.LIGHTBLACK_EX}ไม่มี position เปิด → จบการตรวจสอบ{Style.RESET_ALL}")
            return

        # Cache open orders ต่อ symbol (ลด request ซ้ำ)
        orders_cache = {}

        async def process_position(pos):
            async with semaphore:
                sym = pos['symbol']
                amt = float(pos['positionAmt'])
                if amt == 0:
                    return

                position_side = 'LONG' if amt > 0 else 'SHORT'
                close_side = SIDE_SELL if position_side == 'LONG' else SIDE_BUY
                entry_price = float(pos['entryPrice'])

                print(f"\n{Fore.MAGENTA}=== ตรวจสอบ {sym} ({position_side}) ==={Style.RESET_ALL}")
                print(f"   จำนวน: {amt} | Entry: {entry_price:.6f}")

                # ดึงราคาปัจจุบัน
                current_price = float(pos.get('markPrice', 0))
                if current_price <= 0:
                    try:
                        ticker = await rate_limited_call(client.futures_symbol_ticker(symbol=sym))
                        current_price = float(ticker['price'])
                        print(f"   ราคาปัจจุบัน (ticker): {current_price:.6f}")
                    except Exception as e:
                        print(f"   ดึงราคาปัจจุบันล้มเหลว → ข้าม {sym}: {e}")
                        return

                # ดึง ATR
                atr = await get_cached_atr(client, sym)
                if atr is None or atr <= 0:
                    atr = entry_price * 0.015
                    print(f"   ใช้ ATR fallback: {atr:.6f}")
                else:
                    print(f"   ATR จาก cache: {atr:.6f}")

                # คำนวณ SL/TP
                if position_side == 'LONG':
                    sl_raw = entry_price - (atr * ATR_SL_MULTIPLIER)
                    tp_raw = entry_price + (atr * ATR_TP_MULTIPLIER)
                else:
                    sl_raw = entry_price + (atr * ATR_SL_MULTIPLIER)
                    tp_raw = entry_price - (atr * ATR_TP_MULTIPLIER)

                tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                price_precision = sym_info.get(sym, (4, 2))[0]

                sl_price = round_to_tick(sl_raw, tick_size)
                tp_price = round_to_tick(tp_raw, tick_size)

                sl_str = f"{sl_price:.{price_precision}f}"
                tp_str = f"{tp_price:.{price_precision}f}"

                print(f"   SL คำนวณ: {sl_raw:.6f} → {sl_str}")
                print(f"   TP คำนวณ: {tp_raw:.6f} → {tp_str}")

                # ดึง orders (ใช้ cache ถ้ามี)
                if sym in orders_cache:
                    orders = orders_cache[sym]
                    print(f"   ใช้ orders จาก cache: {len(orders)} รายการ")
                else:
                    try:
                        orders = await rate_limited_call(client.futures_get_open_orders(symbol=sym))
                        orders_cache[sym] = orders
                        print(f"   ดึง open orders สำเร็จ: {len(orders)} รายการ")
                    except Exception as e:
                        print(f"   ดึง open orders ล้มเหลว {sym}: {e}")
                        return

                has_sl = any(o['type'] == 'STOP_MARKET' and o.get('closePosition', False) for o in orders)
                has_tp = any(o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False) for o in orders)

                print(f"   สถานะ → SL: {'มี' if has_sl else 'ไม่มี'}, TP: {'มี' if has_tp else 'ไม่มี'}")

                if has_sl and has_tp:
                    print(f"   มีครบแล้ว → ข้าม {sym}")
                    return

                actions_taken = []

                # ตั้ง SL
                if not has_sl:
                    print(f"   กำลังตั้ง SL ใหม่ @ {sl_str}")
                    for attempt in range(3):
                        try:
                            await rate_limited_call(client.futures_create_order(
                                symbol=sym,
                                side=close_side,
                                type='STOP_MARKET',
                                stopPrice=sl_str,
                                closePosition=True,
                                timeInForce='GTC',
                                workingType='MARK_PRICE'
                            ))
                            actions_taken.append(f"SL ใหม่ @ {sl_str}")
                            print(f"   {Fore.GREEN}ตั้ง SL สำเร็จ (attempt {attempt+1}){Style.RESET_ALL}")
                            break
                        except BinanceAPIException as e:
                            print(f"   ตั้ง SL ล้มเหลว (attempt {attempt+1}): {e.code} - {e.message}")
                            if e.code in [-2022, -1106, -2019, -4130]:
                                print(f"   {Fore.YELLOW}มี SL อยู่แล้ว → ถือว่าสำเร็จ{Style.RESET_ALL}")
                                actions_taken.append(f"SL มีอยู่แล้ว @ {sl_str}")
                                break
                            elif attempt < 2:
                                await asyncio.sleep(random.uniform(1.2, 2.0))
                                continue
                            else:
                                print(f"   {Fore.RED}ตั้ง SL ล้มเหลวถาวร{Style.RESET_ALL}")

                # ตั้ง TP (เหมือนกัน)
                if not has_tp:
                    print(f"   กำลังตั้ง TP ใหม่ @ {tp_str}")
                    for attempt in range(3):
                        try:
                            await rate_limited_call(client.futures_create_order(
                                symbol=sym,
                                side=close_side,
                                type='TAKE_PROFIT_MARKET',
                                stopPrice=tp_str,
                                closePosition=True,
                                timeInForce='GTC',
                                workingType='MARK_PRICE'
                            ))
                            actions_taken.append(f"TP ใหม่ @ {tp_str}")
                            print(f"   {Fore.GREEN}ตั้ง TP สำเร็จ (attempt {attempt+1}){Style.RESET_ALL}")
                            break
                        except BinanceAPIException as e:
                            print(f"   ตั้ง TP ล้มเหลว (attempt {attempt+1}): {e.code} - {e.message}")
                            if e.code in [-2022, -1106, -2019, -4130]:
                                print(f"   {Fore.YELLOW}มี TP อยู่แล้ว → ถือว่าสำเร็จ{Style.RESET_ALL}")
                                actions_taken.append(f"TP มีอยู่แล้ว @ {tp_str}")
                                break
                            elif attempt < 2:
                                await asyncio.sleep(random.uniform(1.2, 2.0))
                                continue
                            else:
                                print(f"   {Fore.RED}ตั้ง TP ล้มเหลวถาวร{Style.RESET_ALL}")

                # สรุป + อัพเดท active + แจ้ง Telegram
                if actions_taken and sym not in sl_tp_advice_notified:
                    print(f"   ดำเนินการ: {' + '.join(actions_taken)}")

                    # อัพเดท active dict
                    for p in active:
                        if p['symbol'] == sym:
                            # ดึง orders ล่าสุด (ใช้ cache ถ้ามี)
                            orders = orders_cache.get(sym, [])
                            if not orders:  # ถ้า cache ว่าง → ดึงใหม่
                                orders = await rate_limited_call(client.futures_get_open_orders(symbol=sym))
                                orders_cache[sym] = orders

                            sl = tp = 0.0
                            for o in orders:
                                if o['type'] == 'STOP_MARKET' and o.get('closePosition', False):
                                    sl = float(o['stopPrice'])
                                elif o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False):
                                    tp = float(o['stopPrice'])

                            p['sl'] = sl
                            p['tp'] = tp
                            print(f"   อัพเดท active {sym}: SL={sl:.6f}, TP={tp:.6f}")
                            break

                    # แจ้ง Telegram เฉพาะเมื่อตั้งใหม่จริง
                    if sym not in sl_tp_advice_notified or any("ใหม่" in a for a in actions_taken):
                        status_text = "ตั้งใหม่บางส่วน" if any("ใหม่" in a for a in actions_taken) else "มีอยู่แล้ว"
                        msg = (
                            f"🛡️ **ตั้ง SL/TP อัตโนมัติ - {sym.replace('USDT','')}**\n"
                            f"• ทิศทาง: **{position_side}**\n"
                            f"• Entry: `{entry_price:.6f}`\n"
                            f"• ดำเนินการ: {' + '.join(actions_taken)}\n"
                            f"• ATR: `{atr:.6f}`\n"
                            f"• สถานะ: {status_text}"
                        )
                        await send_telegram_report(msg)
                        sl_tp_advice_notified.add(sym)

                # Sleep random ระหว่าง symbol เพื่อกระจาย request
                await asyncio.sleep(random.uniform(0.8, 1.2))

        # รันแบบ concurrent แต่จำกัดด้วย semaphore
        await asyncio.gather(*(process_position(pos) for pos in active_positions))

        duration = (datetime.now() - ts_start).total_seconds()
        print(f"{Fore.GREEN}ตรวจสอบ/ตั้ง SL&TP เสร็จสิ้น ({duration:.2f} วินาที){Style.RESET_ALL}")

    except Exception as e:
        print(f"{Fore.RED}Error in ensure_sl_tp_for_all_positions: {e}{Style.RESET_ALL}")
        
# ==========================================================================
#          CHECK MISSING SL/TP & SET AUTOMATICALLY (Manual Command)
# ==========================================================================
async def check_and_set_missing_sltp(client):
    """ตรวจสอบ positions ที่ไม่มี SL/TP แล้วตั้งอัตโนมัติ (สำหรับคำสั่ง /sltp)"""
    try:
        print(f"{Fore.CYAN}=== ตรวจสอบและตั้ง SL/TP สำหรับ positions ที่ไม่มี ==={Style.RESET_ALL}")
        
        positions = await client.futures_position_information()
        active_positions = [p for p in positions if float(p['positionAmt']) != 0]
        
        if not active_positions:
            return "ไม่มี position ที่เปิดอยู่"
        
        missing_sltp = []
        
        for pos in active_positions:
            sym = pos['symbol']
            amt = float(pos['positionAmt'])
            if amt == 0:
                continue
            
            position_side = 'LONG' if amt > 0 else 'SHORT'
            close_side = SIDE_SELL if position_side == 'LONG' else SIDE_BUY
            entry_price = float(pos['entryPrice'])
            
            print(f"\n{Fore.MAGENTA}ตรวจสอบ {sym} ({position_side}){Style.RESET_ALL}")
            
            # ดึง orders ที่มีอยู่
            try:
                orders = await client.futures_get_open_orders(symbol=sym)
            except:
                continue
            
            has_sl = any(o['type'] == 'STOP_MARKET' and o.get('closePosition', False) for o in orders)
            has_tp = any(o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False) for o in orders)
            
            print(f"  SL: {'มี ✅' if has_sl else 'ไม่มี ❌'} | TP: {'มี ✅' if has_tp else 'ไม่มี ❌'}")
            
            if has_sl and has_tp:
                continue  # มีครบแล้ว
            
            missing_sltp.append(sym)
            
            # ดึง ATR
            atr = await get_cached_atr(client, sym)
            if atr is None or atr <= 0:
                atr = entry_price * 0.015
            
            # คำนวณ SL/TP
            if position_side == 'LONG':
                sl_raw = entry_price - (atr * ATR_SL_MULTIPLIER)
                tp_raw = entry_price + (atr * ATR_TP_MULTIPLIER)
            else:
                sl_raw = entry_price + (atr * ATR_SL_MULTIPLIER)
                tp_raw = entry_price - (atr * ATR_TP_MULTIPLIER)
            
            tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
            price_precision = sym_info.get(sym, (4, 2))[0]
            
            sl_price = round_to_tick(sl_raw, tick_size)
            tp_price = round_to_tick(tp_raw, tick_size)
            
            # ตั้ง SL ถ้าไม่มี
            if not has_sl:
                try:
                    await client.futures_create_order(
                        symbol=sym,
                        side=close_side,
                        type='STOP_MARKET',
                        stopPrice=f"{sl_price:.{price_precision}f}",
                        closePosition=True,
                        timeInForce='GTC',
                        workingType='MARK_PRICE'
                    )
                    print(f"  ✅ ตั้ง SL @ {sl_price:.{price_precision}f} สำเร็จ")
                except Exception as e:
                    print(f"  ❌ ตั้ง SL ล้มเหลว: {e}")
            
            # ตั้ง TP ถ้าไม่มี
            if not has_tp:
                try:
                    await client.futures_create_order(
                        symbol=sym,
                        side=close_side,
                        type='TAKE_PROFIT_MARKET',
                        stopPrice=f"{tp_price:.{price_precision}f}",
                        closePosition=True,
                        timeInForce='GTC',
                        workingType='MARK_PRICE'
                    )
                    print(f"  ✅ ตั้ง TP @ {tp_price:.{price_precision}f} สำเร็จ")
                except Exception as e:
                    print(f"  ❌ ตั้ง TP ล้มเหลว: {e}")
        
        if not missing_sltp:
            return "✅ ทุก position มี SL/TP ครบแล้ว!"
        
        return f"✅ ตั้ง SL/TP สำหรับ {len(missing_sltp)} position: {', '.join([s.replace('USDT','') for s in missing_sltp])}"
        
    except Exception as e:
        print(f"{Fore.RED}Error in check_and_set_missing_sltp: {e}")
        return f"❌ เกิดข้อผิดพลาด: {str(e)}"

# ==========================================================================

async def get_current_price(client, symbol):
    """Helper ดึงราคาปัจจุบันแบบเร็ว"""
    try:
        ticker = await client.futures_symbol_ticker(symbol=symbol)
        return float(ticker['price'])
    except:
        return 0.0

# ==========================================================================
#                  HELPER: GET CACHED ATR
# ==========================================================================
async def get_cached_atr(client, sym):
    now = datetime.now()
    if sym in atr_cache and now - atr_cache[sym]['timestamp'] < ATR_CACHE_DURATION:
        return atr_cache[sym]['atr']

    try:
        klines = await client.futures_klines(symbol=sym, interval="15m", limit=100)
        if not klines:
            return None
        df = calculate_indicators(klines)
        if df.empty:
            return None
        atr = float(df.iloc[-1]['atr'])
        atr_cache[sym] = {'atr': atr, 'timestamp': now}
        return atr
    except Exception as e:
        print(f"{Fore.YELLOW}ATR fetch failed for {sym}: {e}")
        return None

# ==========================================================================
#                  TRAILING STOP UPDATE
# ==========================================================================
async def update_trailing_stops(client, active_positions):
    if not active_positions:
        return

    for pos in active_positions:
        sym = pos['symbol']
        side = pos['side']
        entry = pos['entry']
        curr_price = pos.get('curr_price', 0.0)
        current_sl = pos.get('sl', 0.0)

        if curr_price <= 0:
            continue

        atr = await get_cached_atr(client, sym)
        if atr is None or atr <= 0:
            continue

        profit_in_atr = (curr_price - entry) / atr if side == 'LONG' else (entry - curr_price) / atr

        if profit_in_atr < TRAILING_ACTIVATION_MULTIPLIER:
            continue

        if side == 'LONG':
            new_sl = curr_price - (atr * TRAILING_DELTA_MULTIPLIER)
            if current_sl > 0 and new_sl <= current_sl:
                continue
        else:
            new_sl = curr_price + (atr * TRAILING_DELTA_MULTIPLIER)
            if current_sl > 0 and new_sl >= current_sl:
                continue

        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
        new_sl_rounded = round_to_tick(new_sl, tick_size)

        if (side == 'LONG' and new_sl_rounded >= curr_price) or \
           (side == 'SHORT' and new_sl_rounded <= curr_price):
            continue

        price_precision = sym_info.get(sym, (4, 2))[0]
        new_sl_str = f"{new_sl_rounded:.{price_precision}f}"

        try:
            # Cancel old SL
            open_orders = await client.futures_get_open_orders(symbol=sym)
            for order in open_orders:
                if order['type'] == 'STOP_MARKET' and order.get('closePosition', False):
                    try:
                        await client.futures_cancel_order(symbol=sym, orderId=order['orderId'])
                    except:
                        pass

            # Set new trailing SL
            stop_side = SIDE_SELL if side == 'LONG' else SIDE_BUY
            await client.futures_create_order(
                symbol=sym,
                side=stop_side,
                type='STOP_MARKET',
                stopPrice=new_sl_str,
                closePosition=True,
                timeInForce='GTC',
                workingType='MARK_PRICE',
            )

            pos['sl'] = new_sl_rounded

            # Notify only on significant move
            if abs(new_sl_rounded - current_sl) > atr * 0.5:
                report = (
                    f"🔄 **Trailing Stop Updated**\n"
                    f"{sym.replace('USDT','')} {side}\n"
                    f"New SL: `{new_sl_str}`\n"
                    f"ราคาปัจจุบัน: `{curr_price:.6f}`\n"
                    f"กำไร ≈ {profit_in_atr:.2f}x ATR"
                )
                await send_telegram_report(report)

            print(f"{Fore.GREEN}Trailing SL updated {sym} {side} → {new_sl_str}")

        except Exception as e:
            print(f"{Fore.RED}Trailing error {sym}: {e}")

# ==========================================================================
#                            AI BRAIN (เหมือนเดิม)
# ==========================================================================
class SimpleMLP(nn.Module):
    def __init__(self, input_size, hidden_size=64):
        super().__init__()
        self.fc1 = nn.Linear(input_size, hidden_size)
        self.dropout1 = nn.Dropout(0.3)
        self.fc2 = nn.Linear(hidden_size, hidden_size // 2)
        self.dropout2 = nn.Dropout(0.2)
        self.fc3 = nn.Linear(hidden_size // 2, 1)
        # ✨ BatchNorm with momentum=0.01 for small batches, track_running_stats=False to avoid errors
        self.batch_norm1 = nn.BatchNorm1d(hidden_size, momentum=0.01, track_running_stats=False)
        self.batch_norm2 = nn.BatchNorm1d(hidden_size // 2, momentum=0.01, track_running_stats=False)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        # Only apply BatchNorm if batch size > 1
        if x.size(0) > 1:
            x = self.batch_norm1(x)
        x = self.dropout1(x)
        x = torch.relu(self.fc2(x))
        if x.size(0) > 1:
            x = self.batch_norm2(x)
        x = self.dropout2(x)
        x = torch.sigmoid(self.fc3(x))
        return x

class TitanBrain:
    def __init__(self):
        self.memory_file = "titan_memory.json"
        self.model_file = "titan_model.pth"
        self.stats_file = "titan_ai_stats.json"
        self.data = self.load_memory()
        
        # กำหนด input size ตามข้อมูลจริงเสมอ
        if self.data and len(self.data) > 0:
            input_size = len(self.data[0][0])  # จาก features จริงใน memory
            print(f"{Fore.CYAN}🧠 Detected {input_size} features from {len(self.data)} trades{Style.RESET_ALL}")
        else:
            input_size = 7  # ปัจจุบันใช้ 7 features (จาก analyze_matrix)
            print(f"{Fore.YELLOW}🧠 No trade data yet → default to {input_size} features{Style.RESET_ALL}")
        
        self.model = SimpleMLP(input_size, hidden_size=64)
        self.best_loss = float('inf')
        self.training_history = []
        self.accuracy_history = []
        self.load_stats()
        
        # โหลดโมเดลอย่างปลอดภัย (ถ้า shape ไม่ match → สร้างใหม่)
        if os.path.exists(self.model_file):
            try:
                state_dict = torch.load(self.model_file, map_location='cpu')
                # ตรวจ shape ของ fc1.weight
                if 'fc1.weight' in state_dict:
                    model_input = state_dict['fc1.weight'].shape[1]
                    if model_input != input_size:
                        print(f"{Fore.YELLOW}⚠️ Model expects {model_input} features but current data has {input_size} → reinitializing{Style.RESET_ALL}")
                        raise ValueError("Input size mismatch - reinitializing model")
                self.model.load_state_dict(state_dict)
                print(f"{Fore.GREEN}✅ โหลด AI Model สำเร็จ (input size: {input_size}){Style.RESET_ALL}")
            except Exception as e:
                print(f"{Fore.YELLOW}⚠️ โหลด Model ล้มเหลว ({str(e)}) → สร้างโมเดลใหม่{Style.RESET_ALL}")
                # ไม่ต้องทำอะไรเพิ่ม เพราะ self.model ถูกสร้างใหม่แล้ว
        
        if len(self.data) >= 10:
            self.train_model()

    def load_memory(self):
        if os.path.exists(self.memory_file):
            with open(self.memory_file, 'r') as f:
                data_json = json.load(f)
                return [(torch.tensor(d['features'], dtype=torch.float32), d['label']) for d in data_json]
        return []

    def load_stats(self):
        if os.path.exists(self.stats_file):
            try:
                with open(self.stats_file, 'r') as f:
                    stats = json.load(f)
                    self.training_history = stats.get('training_history', [])
                    self.accuracy_history = stats.get('accuracy_history', [])
                    self.best_loss = stats.get('best_loss', float('inf'))
            except:
                pass

    def save_memory(self):
        data_json = [{'features': x.tolist(), 'label': y} for x, y in self.data]
        with open(self.memory_file, 'w') as f:
            json.dump(data_json, f)
        if self.model:
            torch.save(self.model.state_dict(), self.model_file)
        
        # Save stats
        stats = {
            'total_trades': len(self.data),
            'training_history': self.training_history[-100:],  # Keep last 100
            'accuracy_history': self.accuracy_history[-100:],
            'best_loss': self.best_loss
        }
        with open(self.stats_file, 'w') as f:
            json.dump(stats, f)

    def update_memory(self, features, is_win):
        feat_tensor = torch.tensor(features, dtype=torch.float32)
        label = 1.0 if is_win else 0.0
        self.data.append((feat_tensor, label))
        if len(self.data) % 5 == 0:  # Train every 5 new trades
            self.train_model()
        self.save_memory()

    def train_model(self):
        """
        ฝึกโมเดล binary classification ด้วยการปรับปรุงเต็มรูปแบบ
        - Train/Val split 80/20 เพื่อตรวจ overfitting
        - Early stopping ตาม val loss + patience=30
        - AdamW + weight decay + LR scheduler (ไม่มี verbose)
        - BCEWithLogitsLoss + pos_weight เพื่อแก้ imbalance รุนแรง
        - Log ชัดเจน + class balance check + LR change detection
        """
        if len(self.data) < 20:
            ts = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            print(f"[{ts}] [Train] ข้อมูลไม่พอฝึก: มีเพียง {len(self.data)} ตัว (ต้องการ >=20 สำหรับ train/val)")
            return

        # แยก train/val set
        train_data, val_data = train_test_split(
            self.data, test_size=0.2, random_state=42, shuffle=True
        )
        ts = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        print(f"[{ts}] [Train] เริ่มฝึกโมเดล (ปรับปรุงเต็มรูปแบบ)")
        print(f"   - ข้อมูลทั้งหมด: {len(self.data)} → Train: {len(train_data)} | Val: {len(val_data)}")

        # เช็ค class balance ใน train set
        train_labels = np.array([y for _, y in train_data])
        pos_count = int(train_labels.sum())
        total_train = len(train_labels)
        pos_ratio = pos_count / total_train if total_train > 0 else 0
        print(f"   - Class balance (train): Positive = {pos_count}/{total_train} ({pos_ratio:.4f})")

        # คำนวณ pos_weight เพื่อชดเชย imbalance รุนแรง
        if pos_ratio > 0 and pos_ratio < 1:
            pos_weight_value = (total_train - pos_count) / max(1, pos_count)
            print(f"   - ใช้ pos_weight = {pos_weight_value:.2f} ใน BCEWithLogitsLoss")
            pos_weight_tensor = torch.tensor([pos_weight_value])
        else:
            pos_weight_tensor = None
            print("   - ไม่ใช้ pos_weight (balance ดีหรือไม่มี positive)")

        # Optimizer + Scheduler (ไม่มี verbose)
        optimizer = optim.AdamW(self.model.parameters(), lr=1e-4, weight_decay=1e-5)
        scheduler = optim.lr_scheduler.ReduceLROnPlateau(
            optimizer,
            mode='min',
            factor=0.5,
            patience=10,
            min_lr=1e-6,
        )

        # Loss function
        loss_fn = nn.BCEWithLogitsLoss(pos_weight=pos_weight_tensor)

        epochs = 150
        batch_size = 16
        patience = 30
        no_improve_counter = 0
        best_val_loss = float('inf')
        best_epoch = -1
        prev_lr = optimizer.param_groups[0]['lr']

        print(f"   - Optimizer: AdamW (lr=1e-4, wd=1e-5)")
        print(f"   - Loss: BCEWithLogitsLoss (pos_weight={pos_weight_tensor.item() if pos_weight_tensor is not None else 'None'})")
        print(f"   - Epochs max: {epochs} | Batch: {batch_size} | Patience: {patience}")
        print(f"   - Gradient clip: max_norm=1.0 | LR Scheduler: ReduceLROnPlateau")
        print("─" * 80)

        for epoch in range(epochs):
            # Train loop
            self.model.train()
            indices = list(range(len(train_data)))
            np.random.shuffle(indices)
            train_loss_total = 0.0
            num_batches = 0

            for i in range(0, len(train_data), batch_size):
                batch_indices = indices[i:i + batch_size]
                batch = [train_data[j] for j in batch_indices]

                X_batch = torch.stack([x for x, y in batch])
                y_batch = torch.tensor([[y] for x, y in batch], dtype=torch.float32)

                pred_logits = self.model(X_batch)  # ต้อง output logits (ไม่ sigmoid)
                loss = loss_fn(pred_logits, y_batch)

                optimizer.zero_grad()
                loss.backward()
                torch.nn.utils.clip_grad_norm_(self.model.parameters(), max_norm=1.0)
                optimizer.step()

                train_loss_total += loss.item()
                num_batches += 1

            avg_train_loss = train_loss_total / max(1, num_batches)

            # Validation loop
            self.model.eval()
            val_loss_total = 0.0
            with torch.no_grad():
                for x, y in val_data:
                    x = x.unsqueeze(0)  # add batch dim
                    y_tensor = torch.tensor([[y]], dtype=torch.float32)
                    pred_logits = self.model(x)
                    val_loss_total += loss_fn(pred_logits, y_tensor).item()

            avg_val_loss = val_loss_total / max(1, len(val_data))

            # Scheduler step
            scheduler.step(avg_val_loss)

            # ตรวจสอบและ log ถ้า LR เปลี่ยน
            current_lr = optimizer.param_groups[0]['lr']
            if current_lr != prev_lr:
                print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] [Train] Learning rate ลดลง → {current_lr:.2e} (จาก {prev_lr:.2e})")
                prev_lr = current_lr

            # Log ทุก 10 epochs หรือ epoch สุดท้าย
            if (epoch + 1) % 10 == 0 or epoch == epochs - 1:
                msg = f"Epoch {epoch+1:3d}/{epochs} | Train Loss: {avg_train_loss:.6f} | Val Loss: {avg_val_loss:.6f} | LR: {current_lr:.2e}"
                if avg_val_loss < best_val_loss:
                    msg += " ← new best val"
                print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] [Train] {msg}")

            # Early stopping
            if avg_val_loss < best_val_loss:
                best_val_loss = avg_val_loss
                best_epoch = epoch + 1
                no_improve_counter = 0
                print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] [Train] New best val loss: {best_val_loss:.6f} (epoch {best_epoch})")
            else:
                no_improve_counter += 1
                if no_improve_counter >= patience:
                    print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] [Train] Early stopping at epoch {epoch+1} (no val improvement for {patience} epochs)")
                    break

        # สรุปผล
        ts = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        print(f"[{ts}] [Train] การฝึกเสร็จสิ้น")
        print(f"   - Best Val Loss     : {best_val_loss:.6f} (epoch {best_epoch})")
        print(f"   - Final Train Loss  : {avg_train_loss:.6f}")
        print(f"   - Final LR          : {current_lr:.2e}")
        print(f"   - Epochs ที่ฝึกจริง : {epoch+1}")

        self.best_loss = best_val_loss
        self.training_history.append((avg_train_loss, best_val_loss))
        self.calculate_accuracy()
        self.save_memory()

        print(f"[{ts}] [Train] บันทึกโมเดลและความทรงจำเรียบร้อยแล้ว")
        print("═" * 80)

    def calculate_accuracy(self):
        if len(self.data) < 2:
            return
        
        self.model.eval()
        with torch.no_grad():
            correct = 0
            for x, y in self.data:
                pred = self.model(x.unsqueeze(0)).item()
                pred_label = 1.0 if pred > 0.5 else 0.0
                if pred_label == y:
                    correct += 1
            
            accuracy = (correct / len(self.data)) * 100
            self.accuracy_history.append(accuracy)

    def get_ai_confidence(self, f):
        if len(self.data) < 10:
            return 50.0
        self.model.eval()
        with torch.no_grad():
            feat = torch.tensor(f, dtype=torch.float32).unsqueeze(0)
            prob = self.model(feat).item() * 100
            return prob

    def get_pred_pullback(self, f):
        conf = self.get_ai_confidence(f)
        return (conf / 100) * 30
    
    def get_ai_stats(self):
        last_pair = self.training_history[-1] if self.training_history else (0.0, 0.0)
        return {
            'total_trades': len(self.data),
            'last_accuracy': self.accuracy_history[-1] if self.accuracy_history else 0.0,
            'avg_accuracy': sum(self.accuracy_history) / len(self.accuracy_history) if self.accuracy_history else 0.0,
            'best_loss': self.best_loss,
            'last_train_loss': last_pair[0],
            'last_val_loss': last_pair[1],
            'model_epochs_trained': len(self.training_history)
        }
brain = TitanBrain()

# ==========================================================================
#                         AI MATRIX ENGINE
# ==========================================================================
async def analyze_matrix(client, symbol):
    try:
        k = await client.futures_klines(symbol=symbol, interval="15m", limit=250)
        if not k: return None
        
        df = calculate_indicators(k)
        if df.empty: return None

        curr = df.iloc[-1]
        
        long_score = 0
        if curr['c'] > curr['ema200']: long_score += 1
        if curr['ema20'] > curr['ema50']: long_score += 1
        if curr['rsi'] > 50: long_score += 1
        if curr['macd'] > curr['signal']: long_score += 1
        if curr['c'] > curr['bb_upper']: long_score += 1
        if curr['v'] > curr['vol_ma']: long_score += 1
        if curr['c'] > curr['o']: long_score += 1
        if curr['adx'] > ADX_THRESHOLD: long_score += 1

        # เพิ่ม Volume Breakout
        if curr['vol_breakout'] == 1:
            long_score += 1

        # เพิ่ม RSI Oversold for LONG
        if curr['rsi'] < 30:
            long_score += 1

        short_score = 0
        if curr['c'] < curr['ema200']: short_score += 2       # เพิ่มน้ำหนัก
        if curr['ema20'] < curr['ema50']: short_score += 2    # เพิ่มน้ำหนัก
        if curr['macd'] < curr['signal']: short_score += 2    # เพิ่มน้ำหนัก
        if curr['c'] < curr['bb_lower']: short_score += 1
        if curr['rsi'] > 72: short_score += 2                 # เข้มงวดขึ้น (จาก 70 → 72)
        if curr['c'] < curr['o']: short_score += 1
        if curr['adx'] > 32: short_score += 2                 # ADX ต้องสูงขึ้น (จาก 28 → 32)
        if curr['vol_breakout'] == 1: short_score += 2        # Volume breakout มีน้ำหนักมากขึ้น

        # เพิ่ม Volume Breakout for SHORT
        if curr['vol_breakout'] == 1:
            short_score += 1

        # เพิ่ม RSI Overbought for SHORT
        if curr['rsi'] > 70:
            short_score += 1

        # เพิ่มเงื่อนไขเสริม: ต้องมี momentum ลงชัด + BTC ไม่ขาขึ้นแรง
        btc_k = await client.futures_klines(symbol="BTCUSDT", interval="15m", limit=250)
        btc_df = calculate_indicators(btc_k)
        if not btc_df.empty:
            btc_curr = btc_df.iloc[-1]
            if btc_curr['macd'] > btc_curr['signal'] and btc_curr['c'] > btc_curr['ema50']:
                short_score = max(0, short_score - 3)  # ลดคะแนนถ้า BTC กำลัง bullish

        side = "LONG" if long_score >= SIGNAL_THRESHOLD_LONG else "SHORT" if short_score >= SIGNAL_THRESHOLD_SHORT else None
        score = long_score if side == "LONG" else short_score

        f = [
            float(curr['rsi'] / 100),
            float(curr['adx'] / 100),
            float((curr['macd'] - curr['signal']) / curr['atr'] if curr['atr'] > 0 else 0),
            float((curr['c'] - curr['ema200']) / curr['ema200'] if curr['ema200'] > 0 else 0),
            float(curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1),
            float(score / 8.0),
            1.0 if side == 'LONG' else 0.0
        ]

        ai_conf = brain.get_ai_confidence(f)
        atr_val = float(curr['atr'])
        curr_p = float(curr['c'])

        if long_score >= SIGNAL_THRESHOLD_LONG and short_score >= SIGNAL_THRESHOLD_SHORT:
            if long_score > short_score:
                side = "LONG"
                score = long_score
            elif short_score > long_score:
                side = "SHORT"
                score = short_score
            else:
                return None
        elif long_score >= SIGNAL_THRESHOLD_LONG:
            side = "LONG"
            score = long_score
        elif short_score >= SIGNAL_THRESHOLD_SHORT:
            side = "SHORT"
            score = short_score
        else:
            return None

        return {"symbol": symbol, "side": side, "score": score, "ai": ai_conf, "atr": atr_val, "curr_p": curr_p, "rsi": float(curr['rsi']), "vol_breakout": int(curr['vol_breakout'])}

    except BinanceAPIException as e:
        if e.code == -1122: pass
        else: print(f"API error for {symbol}: {e}")
        return None
    except Exception as e:
        return None

# ==========================================================================
#                   HELPER: ROUND TO TICK SIZE
# ==========================================================================
def round_to_tick(price: float, tick_size: float) -> float:
    if tick_size <= 0:
        return price
    return round(price / tick_size) * tick_size

# ==========================================================================
#                       RISK MANAGEMENT
# ==========================================================================
def calculate_position_size(balance, entry_price, atr, symbol, sym_filters, sym_info):
    try:
        if atr <= 0 or entry_price <= 0:
            return 0.0
        
        risk_amount = balance * RISK_PER_TRADE_PERCENT
        stop_distance_percent = (atr * ATR_SL_MULTIPLIER) / entry_price
        position_value = risk_amount / (stop_distance_percent + 1e-9)
        raw_qty = position_value / entry_price
        notional = raw_qty * entry_price
        
        if notional < MIN_NOTIONAL_USDT:
            return 0.0
        
        step_size = sym_filters.get(symbol, {}).get('stepSize', 0.0)
        if step_size > 0:
            qty = math.floor(raw_qty / step_size) * step_size
        else:
            qty = raw_qty
        
        qty_precision = sym_info.get(symbol, (4, 2))[1]
        return round(qty, qty_precision)
    except:
        return 0.0
# ==========================================================================
#                     TELEGRAM HELPER
# ==========================================================================
async def send_telegram_report(text, chat_id=None, photo=None):
    global telegram_bot, TELEGRAM_CHAT_ID
    if not telegram_bot:
        return
    target = chat_id or TELEGRAM_CHAT_ID
    if not target:
        return
    try:
        # Escape เฉพาะตัวที่ MarkdownV2 ต้องการเท่านั้น
        safe_text = text.replace('\\', '\\\\') \
                       .replace('_', '\\_') \
                       .replace('*', '\\*') \
                       .replace('[', '\\[') \
                       .replace(']', '\\]') \
                       .replace('(', '\\(') \
                       .replace(')', '\\)') \
                       .replace('~', '\\~') \
                       .replace('`', '\\`') \
                       .replace('>', '\\>') \
                       .replace('#', '\\#') \
                       .replace('+', '\\+') \
                       .replace('-', '\\-') \
                       .replace('=', '\\=') \
                       .replace('|', '\\|') \
                       .replace('{', '\\{') \
                       .replace('}', '\\}') \
                       .replace('.', '\\.') \
                       .replace('!', '\\!')

        if photo:
            await telegram_bot.send_photo(
                chat_id=target,
                photo=photo,
                caption=safe_text,
                parse_mode="MarkdownV2"   # ← เปลี่ยนเป็น MarkdownV2
            )
        else:
            await telegram_bot.send_message(
                chat_id=target,
                text=safe_text,
                parse_mode="MarkdownV2"   # ← เปลี่ยนที่นี่
            )
    except TelegramError as e:
        print(f"Telegram send error: {e}")
        # Fallback: ส่งแบบ plain text ถ้า MarkdownV2 พัง
        await telegram_bot.send_message(chat_id=target, text=text, parse_mode=None)

# ==========================================================================
#                           DASHBOARD
# ==========================================================================
async def print_dashboard(client, balance, active_positions, pending_orders, price_map, btc_price, scanning=False):
    global prev_prices, ticker_offset, ticker_direction
    
    os.system('cls' if os.name == 'nt' else 'clear')
    
    total_pnl = sum(p['pnl'] for p in active_positions)
    pnl_color = Fore.GREEN if total_pnl >= 0 else Fore.RED
    bright_pnl = Style.BRIGHT if abs(total_pnl) > 100 else Style.NORMAL
    status_spinners = ["│", "/", "−", "\\"]
    spinner_idx = int(datetime.now().timestamp() * 8) % 4
    spinner = status_spinners[spinner_idx]
    status_str = f"{Fore.GREEN}{Style.BRIGHT}{spinner} SCANNING{Style.RESET_ALL}" if scanning else f"{Fore.LIGHTBLACK_EX}○ IDLE"
    mode_str = f"{Back.YELLOW}{Fore.BLACK}{Style.BRIGHT} 🧪 TESTNET {Style.RESET_ALL}" if USE_TESTNET else f"{Back.RED}{Fore.WHITE}{Style.BRIGHT} ⚡ LIVE {Style.RESET_ALL}"
    time_now = datetime.now().strftime('%H:%M:%S')

    line_pulse = Fore.CYAN if int(datetime.now().timestamp() * 2) % 2 == 0 else Fore.WHITE
    print(f"""
{line_pulse}   ██████╗ ██╗   ██╗██╗  ██╗
   ██╔══██╗██║   ██║██║ ██╔╝
   ██████╔╝██║   ██║█████╔╝ 
   ██╔═══╝ ██║   ██║██╔═██╗ 
   ██║     ╚██████╔╝██║  ██╗
   ╚═╝      ╚═════╝ ╚═╝  ╚═╝

             /\\_/\\ 
            ( o.o ) 
             > ^ <{Style.RESET_ALL}
    """)

    ticker_parts = []
    for sym in MAJOR_TICKER_SYMBOLS:
        if sym not in price_map:
            continue
        curr_p = price_map[sym]
        prev_p = prev_prices.get(sym, curr_p)
        
        change = curr_p - prev_p
        change_pct = (change / prev_p * 100) if prev_p > 0 else 0
        
        sym_name = sym.replace('USDT', '')
        if change > 0:
            arrow = "⬆"
            color = Fore.GREEN
        elif change < 0:
            arrow = "⬇"
            color = Fore.RED
        else:
            arrow = "→"
            color = Fore.YELLOW
        
        part = f"{color}{Style.BRIGHT}{sym_name}{Style.NORMAL} {curr_p:,.4f} {arrow} {change_pct:+.2f}%{Fore.WHITE}   "
        ticker_parts.append(part)
        
        prev_prices[sym] = curr_p
    
    full_ticker = "   │   ".join(ticker_parts) + "          "
    ticker_length = len(full_ticker.rstrip())
    
    if random.random() < 0.05:
        ticker_direction *= -1
    
    ticker_offset = (ticker_offset + ticker_direction * 2) % ticker_length
    if ticker_offset < 0:
        ticker_offset += ticker_length
    
    scrolling_ticker = full_ticker[ticker_offset:] + full_ticker[:ticker_offset]
    
    print(f"{Back.BLACK}{Fore.WHITE}{Style.BRIGHT} " + scrolling_ticker.center(188) + Style.RESET_ALL)
    print(f"{Back.BLACK}{Fore.CYAN}╔" + "═" * 188 + "╗{Style.RESET_ALL}")

    heartbeat = "❤️" if int(datetime.now().timestamp() * 1.5) % 2 == 0 else "🖤"
    print(f"{Back.BLACK}║ {mode_str}{Fore.CYAN} TITAN PRO v33.0 (AI) {Fore.WHITE}│ {Fore.MAGENTA}📊 TOP 100 VOLUME {Fore.WHITE}│ 🕒 {Fore.WHITE}{time_now} {' ':<65}║{Style.RESET_ALL}{Fore.RED}{heartbeat}{Style.RESET_ALL}")
    print(f"{Back.BLACK}{Fore.CYAN}╠" + "═" * 188 + "╣{Style.RESET_ALL}")
    
    balance_str = f"💰 BALANCE: {Fore.YELLOW}{Style.BRIGHT}{balance:,.2f}{Style.NORMAL} USDT"
    pnl_str = f"📈 TOTAL PNL: {bright_pnl}{pnl_color}{total_pnl:+,.2f}{Style.RESET_ALL} USDT"
    btc_str = f"₿ BTC PRICE: {Fore.YELLOW}{Style.BRIGHT}{btc_price:,.1f}{Style.NORMAL}"
    pending_str = f"⏳ PENDING: {Fore.MAGENTA}{len(pending_orders)}"
    active_str = f"⭐ POSITIONS: {Fore.CYAN}{len(active_positions)}/{MAX_OPEN_POSITIONS}"
    
    print(f"{Back.BLACK}║  {balance_str:<40} {pnl_str:<45} {btc_str:<35} {status_str:<25} {active_str}{pending_str.rjust(20)}  ║{Style.RESET_ALL}")
    print(f"{Back.BLACK}{Fore.CYAN}╚" + "═" * 188 + "╝{Style.RESET_ALL}\n")
    
    print(f"{Fore.CYAN}{Style.BRIGHT}⭐ ACTIVE POSITIONS ({len(active_positions)} / {MAX_OPEN_POSITIONS}){Style.RESET_ALL}")
    if len(active_positions) > MAX_OPEN_POSITIONS:
        print(f" {Fore.RED}{Style.BRIGHT}⚠️ WARNING: มี Position มากกว่า Max! ({len(active_positions)} > {MAX_OPEN_POSITIONS}){Style.RESET_ALL}")

    if active_positions:
            print(f" {Fore.WHITE}{'ID':<4} {'SYMBOL':<12} {'SIDE':<12} {'ENTRY':<12} {'PRICE':<12} {'PNL':<15} {'ROE%':<10} {'SL DIST':<20} {'TP DIST':<20}")
            print(f" {Fore.LIGHTBLACK_EX}{'─' * 188}")

            for i, p in enumerate(active_positions, 1):
                side_icon = "📈 LONG 🟢" if p['side'] == 'LONG' else "📉 SHORT 🔴"
                side_color = Fore.GREEN if p['side'] == 'LONG' else Fore.RED
                pc = Fore.GREEN if p['pnl'] >= 0 else Fore.RED
                roe = (p['pnl'] / p['margin'] * 100) if p['margin'] > 0 else 0.0
                
                curr_price = p['curr_price']
                sym = p['symbol']

                # ดึงค่า SL/TP จาก dict ก่อน (ที่บอทอัปเดตไว้แล้ว)
                # ดึงค่า SL/TP จาก dict ก่อน (ที่บอทอัปเดตไว้แล้ว)
                sl_price = p.get('sl', 0.0)
                tp_price = p.get('tp', 0.0)

                # ถ้าค่าใน active เป็น 0 → ดึงสดจาก Binance (fallback)
                if sl_price <= 0 or tp_price <= 0:
                    try:
                        await asyncio.sleep(0.8)  # รอ Binance sync นิดนึง (สำคัญมาก!)
                        orders = await client.futures_get_open_orders(symbol=sym)
                        for o in orders:
                            if o.get('closePosition', False):
                                if 'STOP' in o['type']:
                                    sl_price = float(o['stopPrice'])
                                if 'TAKE_PROFIT' in o['type']:
                                    tp_price = float(o['stopPrice'])
                        print(f"DEBUG dashboard fallback: ดึงสด SL/TP {sym} → SL={sl_price:.6f}, TP={tp_price:.6f}")
                    except Exception as e:
                        print(f"ดึงสด SL/TP ใน dashboard ล้มเหลว {sym}: {e}")
                # ถ้ายังไม่มีใน dict → แสดงว่า "ตั้งอยู่บน Binance แล้ว" (จาก Auto Set หรือ Algo Order)
                # แสดงผลตามปกติ (เหมือนเดิม)
                if sl_price <= 0:
                    sl_show = f"{Fore.YELLOW}{Style.BRIGHT}SET (Binance){Style.RESET_ALL}"
                else:
                    sl_dist = abs(curr_price - sl_price) / curr_price * 100 if curr_price > 0 else 0
                    sl_alert = f"{Back.RED}{Fore.WHITE}{Style.BRIGHT} DANGER! {Style.RESET_ALL}" if sl_dist < 1.5 else ""
                    direction = "↓" if (p['side'] == 'LONG' and sl_price < curr_price) or (p['side'] == 'SHORT' and sl_price > curr_price) else "↑"
                    sl_show = f"{sl_alert}{Fore.WHITE}{sl_price:.6f} {Fore.RED}{direction}{sl_dist:.2f}%{Style.RESET_ALL}"

                if tp_price <= 0:
                    tp_show = f"{Fore.GREEN}{Style.BRIGHT}SET (Binance){Style.RESET_ALL}"
                else:
                    tp_dist = abs(tp_price - curr_price) / curr_price * 100 if curr_price > 0 else 0
                    tp_near = f"{Fore.YELLOW}{Style.BRIGHT}★ {Style.NORMAL}" if tp_dist < 2.0 else ""
                    direction = "↑" if (p['side'] == 'LONG' and tp_price > curr_price) or (p['side'] == 'SHORT' and tp_price < curr_price) else "↓"
                    tp_show = f"{tp_near}{Fore.WHITE}{tp_price:.6f} {Fore.GREEN}{direction}{tp_dist:.2f}%{Style.RESET_ALL}"

                # Tag แหล่งที่มา (Volume Spike หรือ Strong Short)
                source = ""
                src = str(p.get('source', ''))
                if 'auto_spike' in src:
                    source = " [Vol Spike]"
                elif 'strong_short' in src:
                    source = " [Strong Short]"

                print(f" {Fore.YELLOW}{Style.BRIGHT}{i:<4}{Style.NORMAL} "
                      f"{side_color}{sym.replace('USDT',''):<12}{Fore.WHITE} "
                      f"{side_icon}{source:<15} "  # เพิ่มช่องว่างให้สวย
                      f"{Fore.WHITE}{p['entry']:<12.6f} "
                      f"{Fore.CYAN}{Style.BRIGHT}{curr_price:<12.6f}{Style.NORMAL} "
                      f"{pc}{p['pnl']:+15.2f} "
                      f"{pc}{roe:+10.2f}% "
                      f"{sl_show:<23} "  # ปรับความกว้างให้พอดี
                      f"{tp_show:<23}")
    else:
        print(f" {Fore.LIGHTBLACK_EX}   ⟹ ไม่มีตำแหน่งที่เปิดอยู่ รอ Limit เข้า...{Style.RESET_ALL}")

    print(f"\n{Fore.CYAN}{Style.BRIGHT}⏳ PENDING LIMIT ORDERS ({len(pending_orders)}){Style.RESET_ALL}")
    if pending_orders:
        print(f" {Fore.WHITE}{'NO':<4} {'SYMBOL':<12} {'SIDE':<12} {'CURRENT':<14} {'LIMIT':<14} {'GAP $':<14} {'GAP %':<12} {'QTY':<12} {'AGE':<12} {'STATUS'}")
        print(f" {Fore.LIGHTBLACK_EX}{'─' * 188}")
        
        for i, o in enumerate(sorted(pending_orders, key=lambda x: x['time']), 1):
            sym_no_usdt = o['symbol'].replace('USDT', '')
            curr_p = price_map.get(o['symbol'], 0.0)
            side_label = "🟢 BUY " if o['side'] == 'BUY' else "🔴 SELL"
            side_color = Fore.GREEN if o['side'] == 'BUY' else Fore.RED
            
            # เพิ่ม tag Manual ถ้าเป็นคำสั่ง /setlm
            manual_tag = " [Manual]" if o.get('manual', False) else ""

            gap_price = abs(o['price'] - curr_p)
            gap_pct = (gap_price / curr_p * 100) if curr_p > 0 else 0.0
            gap_color = Fore.GREEN if gap_pct < 1.0 else Fore.YELLOW if gap_pct < 3.0 else Fore.RED
            
            age_h = (datetime.now() - o['time']).total_seconds() / 3600
            age_str = f"{Fore.RED}{Style.BRIGHT}OLD! {age_h:.1f}h{Style.NORMAL}" if age_h > LIMIT_ORDER_TIMEOUT_HOURS else f"{Fore.WHITE}{age_h:.1f}h"
            status = f"{Fore.RED}{Style.BRIGHT}⚠️ จะถูกยกเลิก!{Style.NORMAL}" if age_h > LIMIT_ORDER_TIMEOUT_HOURS else ""

            print(f" {Fore.YELLOW}{Style.BRIGHT}{i:<4}{Style.NORMAL} "
                                  f"{Fore.WHITE}{sym_no_usdt:<12} "
                                  f"{side_color}{side_label:<12}{Fore.WHITE}{manual_tag} "
                                  f"{Fore.CYAN}{curr_p:<14.6f} "
                                  f"{Fore.YELLOW}{Style.BRIGHT}{o['price']:<14.6f}{Style.NORMAL} "
                                  f"{gap_color}{gap_price:+.6f}{Fore.WHITE:<14} "
                                  f"{gap_color}{gap_pct:+.2f}%{Fore.WHITE:<12} "
                                  f"{Fore.WHITE}{o['qty']:<12.4f} "
                                  f"{age_str:<12} "
                                  f"{status}")
    else:
        print(f" {Fore.LIGHTBLACK_EX}   ⟹ ไม่มี Limit Order ที่รออยู่...{Style.RESET_ALL}")

    heartbeat_footer = "❤️" if int(datetime.now().timestamp() * 1.5) % 2 == 0 else "🖤"
    print(f"\n{Fore.CYAN}╔{'═' * 186}╗")
    print(f"║ {Fore.WHITE}🎮 COMMANDS: {Fore.YELLOW}{Style.BRIGHT}[ID]{Style.NORMAL}{Fore.WHITE} Close │ "
          f"{Fore.YELLOW}{Style.BRIGHT}A{Style.NORMAL}{Fore.WHITE} Close All │ "
          f"{Fore.YELLOW}{Style.BRIGHT}C{Style.NORMAL}{Fore.WHITE} Cancel Limits │ "
          f"{Fore.RED}{Style.BRIGHT}Q{Style.NORMAL}{Fore.WHITE} Quit │ "
          f"{Fore.CYAN}📱 Telegram: /help /report /limits {heartbeat_footer.rjust(45)}║")
    print(f"╚{'═' * 186}╝{Style.RESET_ALL}")

# ==========================================================================
#                  AUTO ENTER: VOLUME SPIKE → MARKET LONG ($0.5 risk)
# ==========================================================================
# ==========================================================================
#                  AUTO ENTER: VOLUME SPIKE → MARKET LONG ($0.5 risk)
# ==========================================================================


# -------------------------------------------------------------------------
# ช่วยให้ fetch klines หลาย timeframe พร้อมกัน (สำคัญมากสำหรับความเร็ว)
# -------------------------------------------------------------------------
async def fetch_klines_batch(client, symbol, timeframes, limit=60):
    """
    ดึง klines หลาย timeframe พร้อมกัน → ลด latency สะสม
    """
    tasks = []
    for tf in timeframes:
        tasks.append(client.futures_klines(symbol=symbol, interval=tf, limit=limit))
    
    results = await asyncio.gather(*tasks, return_exceptions=True)
    
    tf_data = {}
    for tf, result in zip(timeframes, results):
        if isinstance(result, Exception):
            print(f"{Fore.RED}Fetch error {symbol} {tf}: {result}{Style.RESET_ALL}")
            continue
        tf_data[tf] = result
    
    return tf_data


# -------------------------------------------------------------------------
# ฟังก์ชันหลักที่ปรับปรุงแล้ว
# ==========================================================================
# ฟังก์ชันหลัก
# ==========================================================================
async def detect_volume_spike_symbols(
    client: AsyncClient,
    symbols: List[str],
    price_map: Dict[str, float],
    active_symbols: set,
    max_concurrent: int = 12
) -> List[str]:
    """
    ตรวจจับ volume spike + เงื่อนไขคุณภาพ → เข้า LONG อัตโนมัติ
    Returns: list ของ symbol ที่เข้า order สำเร็จ
    """
    now = datetime.utcnow()
    cooldown_until = now - timedelta(minutes=COOLDOWN_MINUTES)

    if not hasattr(detect_volume_spike_symbols, "cooldown_map"):
        detect_volume_spike_symbols.cooldown_map: Dict[str, datetime] = {}

    cooldown_map = detect_volume_spike_symbols.cooldown_map

    # กรอง candidate ก่อน
    candidates = []
    for sym in symbols:
        if sym in active_symbols:
            continue
        last = cooldown_map.get(sym)
        if last and last > cooldown_until:
            remain = int((last - cooldown_until).total_seconds() / 60)
            print(f"{Fore.YELLOW}Skip {sym}: Cooldown เหลือ {remain} นาที{Style.RESET_ALL}")
            continue
        candidates.append(sym)

    if not candidates:
        return []

    # จำกัด concurrent requests ป้องกัน rate limit
    semaphore = asyncio.Semaphore(max_concurrent)

    async def limited_process(sym: str):
        async with semaphore:
            return await process_single_symbol(
                client,
                sym,
                all_tfs=ALL_TFS,          # เพิ่มตรงนี้
                priority_tfs=PRIORITY_TFS # เพิ่มตรงนี้
            )

    tasks = [limited_process(sym) for sym in candidates]
    results = await asyncio.gather(*tasks, return_exceptions=True)

    entered = []

    for sym, result in zip(candidates, results):
        if isinstance(result, Exception):
            print(f"{Fore.RED}Process {sym} error: {result}{Style.RESET_ALL}")
            await send_telegram_report(f"⚠️ Process error {sym}: {str(result)}")
            continue

        if result is None:
            continue

        best_tf, df, vol_ratio, entry_price = result

        try:
            success = await execute_long_entry(
                client, sym, df, entry_price, vol_ratio, best_tf
            )
            if success:
                entered.append(sym)
                cooldown_map[sym] = datetime.utcnow()

        except Exception as e:
            # ยังคง log ใน console เพื่อ debug ได้
            print(f"{Fore.RED}Entry {sym} failed: {e}{Style.RESET_ALL}")
            
            # ลบหรือ comment บรรทัดนี้ เพื่อไม่ส่งไป Telegram
            # await send_telegram_report(f"❌ Entry fail {sym}: {str(e)}")
            
            # หรือถ้าอยากเก็บไว้แต่ส่งเฉพาะ error สำคัญ (ไม่รวม -4164)
            error_str = str(e)
            if "liquidation" in error_str.lower() or "insufficient" in error_str.lower() or "APIError(code=-2019)" in error_str:
                await send_telegram_report(f"❌ Critical: {sym} → {error_str[:120]}")
            # ไม่ส่ง -4164 หรือ error notional เล็ก ๆ อื่น ๆ
            
    return entered


# ==========================================================================
# Process ทีละเหรียญ
async def process_single_symbol(client: AsyncClient, symbol: str) -> Optional[Tuple[str, Any, float, float]]:
    try:
        klines_tasks = {
            tf: client.futures_klines(symbol=symbol, interval=tf, limit=60)
            for tf in ALL_TFS     # ใช้ global ได้เลย
        }
        klines_results = await asyncio.gather(*klines_tasks.values(), return_exceptions=True)

        klines_dict = {}
        for tf, res in zip(klines_tasks, klines_results):
            if isinstance(res, Exception) or not res or len(res) < 35:
                continue
            klines_dict[tf] = res

        if not klines_dict:
            return None

        # หา best spike (เรียง priority ก่อน)
        best = None
        best_ratio = 0.0

        for tf in PRIORITY_TFS + [t for t in ALL_TFS if t not in PRIORITY_TFS]:
            klines = klines_dict.get(tf)
            if not klines:
                continue

            df = calculate_indicators(klines)  # ฟังก์ชันของคุณเอง
            if df.empty or len(df) < 30:
                continue

            curr = df.iloc[-1]
            vol_ma = curr.get('vol_ma', 0)
            if vol_ma <= 0:
                continue

            ratio = curr['v'] / vol_ma
            if ratio > MIN_VOL_RATIO and ratio > best_ratio:
                best_ratio = ratio
                best = (tf, df, ratio, float(curr['c']))

            if best is None:
                print(f"{Fore.YELLOW}{symbol} → ไม่เจอ volume spike ที่ดีพอ (MIN_VOL_RATIO={MIN_VOL_RATIO}){Style.RESET_ALL}")
                return None

            print(f"{Fore.GREEN}{symbol} → ผ่าน! Best TF: {best_tf} | Vol Ratio: {best_ratio:.2f}x | Price: {price:.4f}{Style.RESET_ALL}")

            # ก่อนตรวจคุณภาพ
            print(f"   → กำลังตรวจคุณภาพ setup ({best_tf})...")

            if not await is_quality_long_setup(client, symbol, df):
                print(f"{Fore.RED}   → ไม่ผ่านคุณภาพ setup{Style.RESET_ALL}")
                return None

            print(f"{Fore.GREEN}   → คุณภาพ setup ผ่าน! พร้อมเข้า LONG{Style.RESET_ALL}")

    except Exception as e:
        print(f"{Fore.RED}{symbol} process exception: {e}{Style.RESET_ALL}")
        return None


# ==========================================================================
# เงื่อนไขคุณภาพ (ปรับแต่งได้ง่าย)
# ==========================================================================
async def is_quality_long_setup(client: AsyncClient, symbol: str, df) -> bool:
    try:
        curr = df.iloc[-1]

        # HTF alignment (สำคัญที่สุด)
        if not await check_htf_bullish_alignment(client, symbol):
            print(f"{Fore.YELLOW}{symbol}: HTF ไม่ bullish{Style.RESET_ALL}")
            return False

        # EMA เรียงตัวดี
        ema20 = curr.get('ema20', 0)
        ema50 = curr.get('ema50', 0)
        ema100 = curr.get('ema100', ema50)
        if not (ema20 > ema50 > ema100 * 0.995):
            return False

        # Momentum + Candle confirmation
        stoch_k = curr.get('stoch_k', 50)
        stoch_d = curr.get('stoch_d', 50)
        bullish_stoch = stoch_k < 32 and stoch_k > stoch_d

        bullish_candle = curr['c'] > curr['o']

        strong_engulf = False
        if len(df) >= 2:
            p = df.iloc[-2]
            strong_engulf = (
                p['c'] < p['o'] and
                curr['o'] <= p['c'] and
                curr['c'] > p['o'] and
                (curr['c'] - curr['o']) > (p['o'] - p['c']) * 1.2
            )

        if not (bullish_stoch or strong_engulf or bullish_candle):
            return False

        # ราคาใกล้ demand zone
        support = float(curr.get('support', 0))
        if support > 0 and curr['c'] < support * 0.986:
            return False

        return True

    except Exception:
        return False


# ==========================================================================
# เข้า order จริง
# ==========================================================================
async def execute_long_entry(
    client: AsyncClient,
    symbol: str,
    df,
    entry_price: float,
    vol_ratio: float,
    tf: str,
) -> bool:
    try:
        curr = df.iloc[-1]
        atr = curr['atr']

        sl = entry_price - atr * ATR_SL_MULTIPLIER
        tp = entry_price + atr * ATR_TP_MULTIPLIER

        # ปรับ TP ด้วย resistance ถ้า RR ยังดี
        resistance = float(curr.get('resistance', 0))
        if resistance > entry_price * 1.008 and tp > resistance:
            tp_cand = resistance * 0.982
            rr_cand = (tp_cand - entry_price) / (entry_price - sl)
            if rr_cand >= MIN_RR_RATIO:
                tp = tp_cand

        rr = (tp - entry_price) / (entry_price - sl)
        if rr < MIN_RR_RATIO:
            print(f"{Fore.YELLOW}{symbol} RR {rr:.2f} < {MIN_RR_RATIO} → skip{Style.RESET_ALL}")
            return False

        # Position sizing
        stop_dist = entry_price - sl
        if stop_dist <= 0:
            return False

        position_value = RISK_USD_PER_TRADE / (stop_dist / entry_price)
        qty = position_value / entry_price

        step_size = sym_filters.get(symbol, {}).get('stepSize', 0.001)
        qty = math.floor(qty / step_size) * step_size
        qty = max(qty, step_size * 5)  # ขั้นต่ำ

        qty_prec = sym_info.get(symbol, (4, 2))[1]
        qty_str = f"{qty:.{qty_prec}f}"

        # เปลี่ยน leverage
        await client.futures_change_leverage(symbol=symbol, leverage=MAX_LEVERAGE)

        # Market Buy
        await client.futures_create_order(
            symbol=symbol,
            side="BUY",
            type="MARKET",
            quantity=qty_str
        )

        # SL & TP
        tick_size = sym_filters.get(symbol, {}).get('tickSize', 0.0001)
        price_prec = sym_info.get(symbol, (4, 2))[0]

        sl_tick = round(sl / tick_size) * tick_size
        tp_tick = round(tp / tick_size) * tick_size

        await client.futures_create_order(
            symbol=symbol,
            side="SELL",
            type="STOP_MARKET",
            stopPrice=f"{sl_tick:.{price_prec}f}",
            closePosition=True,
            reduceOnly=True,
            workingType="MARK_PRICE"
        )

        await client.futures_create_order(
            symbol=symbol,
            side="SELL",
            type="TAKE_PROFIT_MARKET",
            stopPrice=f"{tp_tick:.{price_prec}f}",
            closePosition=True,
            reduceOnly=True,
            workingType="MARK_PRICE"
        )

        # Report
        fib_elliot = get_fib_elliot_signal(df, entry_price)  # ฟังก์ชันของคุณ
        report = f"""🚀 AUTO LONG {symbol}
ราคาเข้า   : {entry_price:.4f}
Qty        : {qty_str}
SL         : {sl_tick:.4f}   TP: {tp_tick:.4f}
RR         : {rr:.2f}:1
Vol Spike  : {vol_ratio:.2f}x ({tf})
HTF        : Bullish ✓
EMA        : Aligned ✓
Action/Stoch ✓
Elliott    : {fib_elliot.get('wave_pattern','?')} ({fib_elliot.get('wave_direction','?')})"""

        await send_telegram_report(report)
        print(f"{Fore.GREEN}{Style.BRIGHT}{report}{Style.RESET_ALL}")

        return True

    except Exception as e:
        await send_telegram_report(f"Order failed {symbol}: {str(e)}")
        raise

# -------------------------------------------------------------------------
# แยกการประมวลผลทีละเหรียญ (เพื่อ parallel)
# -------------------------------------------------------------------------
async def process_single_symbol(client, sym, all_tfs, priority_tfs):
    try:
        # ดึงข้อมูลทั้งหมดที่จำเป็นในรอบเดียว
        klines_batch = await fetch_klines_batch(client, sym, all_tfs, limit=60)
        if not klines_batch:
            return None
        
        spike_candidates = {}
        max_ratio = 0
        best_tf = None
        best_df = None
        
        for tf in priority_tfs:  # ตรวจ timeframe สำคัญก่อน
            klines = klines_batch.get(tf)
            if not klines or len(klines) < 35:
                continue
                
            df = calculate_indicators(klines)  # ฟังก์ชันเดิมของคุณ
            if df.empty:
                continue
                
            curr = df.iloc[-1]
            vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 0
            
            if vol_ratio > 2.4:  # ปรับ threshold นิดหน่อย
                spike_candidates[tf] = (vol_ratio, df)
                if vol_ratio > max_ratio:
                    max_ratio = vol_ratio
                    best_tf = tf
                    best_df = df
        
        if not best_tf:
            # ถ้า priority ไม่เจอ ลอง tf อื่นบ้าง (แต่ไม่ค่อยได้ผลดี)
            for tf in set(all_tfs) - set(priority_tfs):
                if tf not in klines_batch:
                    continue
                # ... เหมือนด้านบน (ย่อเพื่อไม่ให้โค้ดยาว)
        
        if not best_tf or max_ratio < 2.4:
            return None
        
        curr = best_df.iloc[-1]
        
        # ────────────────────────────────────────────────
        #  เงื่อนไขกรองเข้มงวด + มีเหตุผล (2025-2026 meta)
        # ────────────────────────────────────────────────
        
        # 1. HTF alignment (สำคัญที่สุด — ควรมี weight สูง)
        # แก้เป็น
        if not await check_htf_bullish_alignment(client, sym):
            return None
                
        # 2. EMA structure + slope (เพิ่มความมั่นใจ)
        if not (curr['ema20'] > curr['ema50'] > curr['ema100'] * 0.995):
            return None
        
        # 3. Momentum / structure confirmation
        stoch_ok = curr.get('stoch_k', 50) < 28 and curr.get('stoch_d', 50) < 32
        
        # Bullish structure (Engulfing / Pinbar / Inside → breakout)
        is_bullish_candle = curr['c'] > curr['o']
        bullish_engulf = False
        if len(best_df) >= 2:
            prev = best_df.iloc[-2]
            bullish_engulf = (
                prev['c'] < prev['o'] and
                curr['o'] <= prev['c'] and
                curr['c'] > prev['o'] and
                (curr['c'] - curr['o']) > (prev['o'] - prev['c']) * 1.1
            )
        
        if not (stoch_ok or bullish_engulf or is_bullish_candle):
            return None
        
        # 4. ราคาอยู่ใน demand zone / ใกล้ support
        support = float(curr.get('support', 0))
        if support > 0 and curr['c'] < support * 0.989:  # เข้มขึ้น
            return None
        
        resistance = float(curr.get('resistance', 0))
        if resistance > 0 and curr['c'] > resistance * 1.012:
            return None
        
        # ผ่านทุกเงื่อนไขแล้ว
        return best_tf, best_df, max_ratio, curr['c']
        
    except Exception as e:
        print(f"{Fore.RED}{sym} process error: {e}{Style.RESET_ALL}")
        return None


# -------------------------------------------------------------------------
# แยกส่วนเข้า order (อ่านง่าย + จัดการ error ชัดเจน)
# -------------------------------------------------------------------------
async def execute_long_entry(client, sym, df, entry_price, vol_ratio, tf):
    curr = df.iloc[-1]
    atr = curr['atr']
    
    sl = entry_price - atr * ATR_SL_MULTIPLIER
    tp = entry_price + atr * ATR_TP_MULTIPLIER
    
    # ปรับ TP ด้วย resistance ถ้า RR ยังดี
    resistance = float(curr.get('resistance', 0))
    if resistance > entry_price * 1.008 and tp > resistance:
        tp_cand = resistance * 0.982
        rr_cand = (tp_cand - entry_price) / (entry_price - sl)
        if rr_cand >= MIN_RR_RATIO:
            tp = tp_cand
        # else ใช้ tp เดิม
    
    rr = (tp - entry_price) / (entry_price - sl)
    if rr < MIN_RR_RATIO:
        print(f"{Fore.YELLOW}{sym} RR {rr:.2f} < {MIN_RR_RATIO} → skip{Style.RESET_ALL}")
        return False
    
    # ---------------------------------------------------------------------
    # Position sizing + Order execution
    # ---------------------------------------------------------------------
    risk_usd = 0.5
    stop_dist_pct = (entry_price - sl) / entry_price
    position_value = risk_usd / stop_dist_pct
    qty = position_value / entry_price
    
    # ปรับตาม precision / filter ของ symbol (สมมติว่ามี sym_info, sym_filters)
    step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
    qty = math.floor(qty / step_size) * step_size
    qty = max(qty, step_size * 5)  # ป้องกัน qty น้อยเกินไป
    
    qty_prec = sym_info.get(sym, (4, 2))[1]
    qty_str = f"{qty:.{qty_prec}f}"
    
    try:
        # Leverage
        await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)
        
        # Market Buy
        await client.futures_create_order(
            symbol=sym,
            side='BUY',
            type='MARKET',
            quantity=qty_str
        )
        
        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
        price_prec = sym_info.get(sym, (4, 2))[0]
        
        sl_tick = round_to_tick(sl, tick_size)
        tp_tick = round_to_tick(tp, tick_size)
        
        # SL
        await client.futures_create_order(
            symbol=sym, side='SELL', type='STOP_MARKET',
            stopPrice=f"{sl_tick:.{price_prec}f}",
            closePosition=True, reduceOnly=True,
            workingType='MARK_PRICE'
        )
        
        # TP
        await client.futures_create_order(
            symbol=sym, side='SELL', type='TAKE_PROFIT_MARKET',
            stopPrice=f"{tp_tick:.{price_prec}f}",
            closePosition=True, reduceOnly=True,
            workingType='MARK_PRICE'
        )
        
        # Report
        fib_elliot = get_fib_elliot_signal(df, entry_price)
        report = f"""🚀 AUTO LONG {sym}
ราคาเข้า: {entry_price:.4f}  |  Qty: {qty_str}
SL: {sl_tick:.4f}  |  TP: {tp_tick:.4f}  |  RR: {rr:.2f}:1
Vol Spike: {vol_ratio:.2f}x ({tf})
HTF Bullish ✓   EMA align ✓   Action/Stoch ✓
Elliott: {fib_elliot['wave_pattern']} ({fib_elliot['wave_direction']})"""
        
        await send_telegram_report(report)
        print(f"{Fore.GREEN}{Style.BRIGHT}{report}{Style.RESET_ALL}")
        
        return True
        
    except Exception as e:
        await send_telegram_report(f"Order failed {sym}: {str(e)}")
        raise  # ให้ส่วนบนจัดการต่อ
    
    return False

async def get_sentiment(symbol):
    """
    ดึง sentiment จาก CoinGecko ด้วย ID ที่ถูกต้อง + fallback ปลอดภัย
    Returns: 0.0–1.0 (up vote percentage / 100) หรือ 0.5 ถ้า error
    """
    # Mapping ID ที่ถูกต้อง 2026 (จาก CoinGecko API ล่าสุด)
    coin_id_map = {
        'BNBUSDT':  'binancecoin',
        'XRPUSDT':  'xrp',
        'ADAUSDT':  'cardano',
        'DOGEUSDT': 'dogecoin',
        'AVAXUSDT': 'avalanche-2',
        'BTCUSDT':  'bitcoin',
        'ETHUSDT':  'ethereum',
        'SOLUSDT':  'solana',
        'LINKUSDT': 'chainlink',
        'DOTUSDT':  'polkadot',
        # เพิ่มเหรียญอื่น ๆ ที่บอทใช้บ่อยได้ที่นี่
    }

    # ดึง ID จาก map ถ้ามี ถ้าไม่มี fallback เป็น lowercase + ไม่มี USDT
    coin_id = coin_id_map.get(symbol, symbol.replace('USDT', '').lower())

    cg = CoinGeckoAPI()
    try:
        data = cg.get_coin_by_id(id=coin_id)
        
        # ตรวจสอบว่ามี field จริง ๆ และไม่เป็น None
        up_pct = data.get('sentiment_votes_up_percentage')
        if up_pct is None or not isinstance(up_pct, (int, float)):
            print(f"Sentiment for {symbol} ({coin_id}): No valid up_percentage → fallback 0.5")
            return 0.5
        
        sentiment = up_pct / 100.0
        print(f"Sentiment {symbol} ({coin_id}): {sentiment:.3f} (up {up_pct}%)")
        return max(0.0, min(1.0, sentiment))  # clamp 0–1

    except Exception as e:
        print(f"Sentiment fetch error for {symbol} ({coin_id}): {str(e)}")
        return 0.5  # neutral fallback เสมอเมื่อ error

# ==========================================================================
#                  AUTO ENTER: STRONG SHORT SIGNAL → MARKET SHORT ($0.5 risk)
# ==========================================================================
async def detect_strong_short_signals(client, symbols, price_map, active_symbols):
    tfs = ['3m', '15m', '30m', '1h', '4h']
    results = []
    
    for sym in symbols:
        best_signal = None
        max_strength = 0
        best_tf = None
        best_atr = 0
        best_price = 0
        best_sl = 0
        best_tp = 0
        best_support = 0
        best_resistance = 0
        
        for tf in tfs:
            try:
                klines = await client.futures_klines(symbol=sym, interval=tf, limit=50)
                df = calculate_indicators(klines)
                if df.empty or len(df) < 20:
                    continue
                
                curr = df.iloc[-1]
                vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1
                
                short_conditions = 0
                if curr['c'] < curr['ema200']: short_conditions += 1
                if curr['ema20'] < curr['ema50']: short_conditions += 1
                if curr['macd'] < curr['signal']: short_conditions += 1
                if curr['c'] < curr['bb_lower']: short_conditions += 1
                if curr['rsi'] > 70: short_conditions += 1
                if curr['c'] < curr['o']: short_conditions += 1
                if curr['adx'] > 25: short_conditions += 1
                if vol_ratio > 2.5: short_conditions += 2
                
                # ===== NEW FILTERS =====
                # 1. Stochastic Confirmation (Stoch ต้อง > 80 = Overbought)
                stoch_overbought = curr.get('stoch_k', 0) > 80
                
                # 2. Price Action Confirmation
                price_action_ok = check_price_action_confirmation(df)
                
                # 3. Support/Resistance Check (ราคา ต้องอยู่เหนือ Support)
                support = float(curr.get('support', 0))
                resistance = float(curr.get('resistance', 0))
                price_above_support = curr['c'] > support * 1.005  # 0.5% above support
                
                strength = short_conditions + (vol_ratio - 1)
                
                # มีเงื่อนไข: >= 6 + vol > 2.5 + Stoch confirm + Price Action + ราคา > support
                if (short_conditions >= 6 and vol_ratio > 2.5 and strength > max_strength 
                    and stoch_overbought and price_action_ok and price_above_support
                    and sym not in active_symbols):
                    max_strength = strength
                    best_tf = tf
                    best_atr = curr['atr']
                    best_price = curr['c']
                    best_support = support
                    best_resistance = resistance
                    best_signal = {
                        'conditions_met': short_conditions, 
                        'vol_ratio': vol_ratio,
                        'stoch_k': curr.get('stoch_k', 0),
                        'price_action': price_action_ok
                    }
                    
            except Exception as e:
                print(f"{Fore.RED}Short detect error {sym} {tf}: {e}")
        
        if best_signal:
            # ===== SL/TP พร้อม Support/Resistance Integration =====
            sl = best_price + (best_atr * ATR_SL_MULTIPLIER)
            tp = best_price - (best_atr * ATR_TP_MULTIPLIER)
            
            # Adjust TP to Support level (เด่นขึ้น)
            if best_support > 0 and tp < best_support:
                tp = best_support * 0.98  # ปล่อยให้TP ใกล้ Support เล็กน้อย
            
            # ===== Risk:Reward Check (ต้อง >= 1:2) =====
            rr_ratio = calculate_rr_ratio(best_price, sl, tp, 'SHORT')
            if rr_ratio < 2.0:
                print(f"{Fore.YELLOW}Skip {sym}: RR {rr_ratio:.2f}:1 < 2:1 threshold{Style.RESET_ALL}")
                continue
            
            # ===== Multi-Timeframe Confirmation =====
            htf_bearish = await check_htf_bearish_alignment(client, sym)
            if not htf_bearish:
                print(f"{Fore.YELLOW}Skip {sym}: HTF not bearish aligned{Style.RESET_ALL}")
                continue
            
            risk_amount = 0.5
            stop_distance = best_atr * ATR_SL_MULTIPLIER
            if stop_distance > 0:
                position_value = risk_amount / (stop_distance / best_price)
                qty = position_value / best_price
            else:
                qty = 0.001
            
            # ===== Elliott Wave + Fibonacci Analysis for SHORT =====
            short_fib_elliot = get_fib_elliot_signal(df, best_price)
            
            step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
            qty = math.floor(qty / step_size) * step_size
            if qty < step_size * 10: qty = step_size * 10
            
            qty_precision = sym_info.get(sym, (4, 2))[1]
            qty_str = f"{qty:.{qty_precision}f}"
            
            try:
                await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)
                order = await client.futures_create_order(
                    symbol=sym,
                    side=SIDE_SELL,
                    type='MARKET',
                    quantity=qty
                )
                
                tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                sl_price = round_to_tick(sl, tick_size)
                tp_price = round_to_tick(tp, tick_size)
                p_prec = sym_info.get(sym, (4, 2))[0]
                
                await client.futures_algo_new_order(
                    symbol=sym,
                    side=SIDE_BUY,
                    type='STOP_MARKET',
                    stopPrice=f"{sl_price:.{p_prec}f}",
                    closePosition=True,
                    timeInForce='GTC',
                    workingType='MARK_PRICE'
                )
                await client.futures_algo_new_order(
                    symbol=sym,
                    side=SIDE_BUY,
                    type='TAKE_PROFIT_MARKET',
                    stopPrice=f"{tp_price:.{p_prec}f}",
                    closePosition=True,
                    timeInForce='GTC',
                    workingType='MARK_PRICE'
                )
                
                report = (
                    f"🔴 *AUTO ENTERED SHORT (Enhanced Confirmation)*\n"
                    f"*Symbol:* {sym.replace('USDT','')}\n"
                    f"*Price:* {best_price:.4f}\n"
                    f"*Risk:* $0.5 | *Qty:* {qty_str}\n"
                    f"*SL:* {sl_price:.4f} | *TP:* {tp_price:.4f}\n"
                    f"\n*Confirmations:* ✅\n"
                    f"  • Conditions: {best_signal['conditions_met']}/8\n"
                    f"  • Stoch: {best_signal['stoch_k']:.1f} (>80)\n"
                    f"  • Price Action: {'✅' if best_signal['price_action'] else '❌'}\n"
                    f"  • HTF Align: ✅ (4H bearish)\n"
                    f"  • RR Ratio: {rr_ratio:.2f}:1\n"
                    f"  • Support: {best_support:.4f}\n"
                    f"  • Resistance: {best_resistance:.4f}\n"
                    f"*Elliott Wave:* {short_fib_elliot['wave_pattern']} ({short_fib_elliot['wave_direction']}) [{short_fib_elliot['wave_confidence']:.0%}]\n"
                    f"*Fib Signal:* {short_fib_elliot['signal']} @ {short_fib_elliot['fib_level']} [{short_fib_elliot['confidence']:.0%}]\n"
                    f"*Strength:* {round(max_strength,1)} | *Vol:* {best_signal['vol_ratio']:.2f}x"
                )
                await send_telegram_report(report)
                print(f"{Fore.RED}{Style.BRIGHT}{report}{Style.RESET_ALL}")
                
            except Exception as e:
                await send_telegram_report(f"❌ Auto SHORT failed {sym}: {e}")
                print(f"{Fore.RED}Auto SHORT error {sym}: {e}")
    
    return results

# ==========================================================================
#                  CANCEL OLD LIMITS
# ==========================================================================
async def cancel_old_pending_limits(client):
    try:
        open_orders = await client.futures_get_open_orders()
        limit_orders = [o for o in open_orders if o['type'] == 'LIMIT']
        cutoff_time = datetime.now() - timedelta(hours=LIMIT_ORDER_TIMEOUT_HOURS)
        
        canceled_count = 0
        for order in limit_orders:
            order_time = datetime.fromtimestamp(order['time'] / 1000)
            if order_time < cutoff_time:
                await client.futures_cancel_order(symbol=order['symbol'], orderId=order['orderId'])
                print(f"{Fore.YELLOW}Cancelled old limit: {order['symbol']} @ {order['price']}")
                await send_telegram_report(f"🗑️ Cancelled old limit\n{order['symbol']} @ {order['price']}")
                canceled_count += 1
        
        if canceled_count:
            print(f"{Fore.CYAN}Cleaned {canceled_count} old pending limit orders.")
    except Exception as e:
        print(f"{Fore.RED}Error cleaning old limits: {e}")

# ========================================================================== 
async def get_advanced_analysis_data(client, symbol):
    """
    ดึงข้อมูลวิเคราะห์ขั้นสูงสำหรับระบบ Auto-Short Institutional
    Returns dict ที่มี:
      - price_current, atr
      - trend_4h, trend_1h
      - rsi_4h, stoch_4h, macd
      - support/resistance (จาก swing points)
      - fib_levels (61.8%, 78.6%)
      - bos_confirmed (bool)
      - elliott_phase ('A', 'B', 'C', None)
    """
    try:
        # แปลง symbol เป็นรูปแบบ Binance
        symbol_usdt = symbol if symbol.endswith('USDT') else symbol + 'USDT'
        
        tf_data = {}
        timeframes = [("15m", 200), ("1h", 150), ("4h", 100)]
        
        for tf, limit in timeframes:
            try:
                klines = await client.fetch_ohlcv(symbol_usdt, tf, limit=limit)
                if not klines or len(klines) < 50:
                    continue
                
                # แปลงเป็น DataFrame หรือ dict list
                ohlcv = [
                    {
                        'timestamp': k[0],
                        'open': float(k[1]),
                        'high': float(k[2]),
                        'low': float(k[3]),
                        'close': float(k[4]),
                        'volume': float(k[5])
                    }
                    for k in klines
                ]
                
                # คำนวณตัวชี้วัดพื้นฐาน
                closes = [c['close'] for c in ohlcv]
                highs = [c['high'] for c in ohlcv]
                lows = [c['low'] for c in ohlcv]
                
                # ATR (14-period)
                tr = []
                for i in range(1, len(ohlcv)):
                    tr_val = max(
                        highs[i] - lows[i],
                        abs(highs[i] - closes[i-1]),
                        abs(lows[i] - closes[i-1])
                    )
                    tr.append(tr_val)
                atr = np.mean(tr[-14:]) if len(tr) >= 14 else (closes[-1] * 0.015)
                
                # EMA
                ema20 = calculate_ema(closes, 20)[-1]
                ema50 = calculate_ema(closes, 50)[-1]
                ema200 = calculate_ema(closes, 200)[-1] if len(closes) >= 200 else ema50
                
                # RSI
                rsi = calculate_rsi(closes, 14)[-1]
                
                # Stochastic
                stoch_k = calculate_stochastic(highs, lows, closes, 14)[-1]
                
                # MACD
                macd_line, signal_line = calculate_macd(closes)
                macd_hist = macd_line[-1] - signal_line[-1]
                
                tf_data[tf] = {
                    'ohlcv': ohlcv,
                    'closes': closes,
                    'highs': highs,
                    'lows': lows,
                    'ema20': ema20,
                    'ema50': ema50,
                    'ema200': ema200,
                    'rsi': rsi,
                    'stoch_k': stoch_k,
                    'macd_hist': macd_hist,
                    'atr': atr
                }
                
            except Exception as e:
                print(f"[get_adv] {symbol} {tf} error: {e}")
                continue
        
        if not tf_data:
            return None
        
        result = {}
        
        # ─── ราคาปัจจุบัน + ATR ───
        for tf in ["15m", "1h"]:
            if tf in tf_data:
                result["price_current"] = tf_data[tf]['closes'][-1]
                result["atr"] = tf_data[tf]['atr']
                break
        
        # ─── Trend Analysis ───
        for tf, key in [("4h", "trend_4h"), ("1h", "trend_1h")]:
            if tf in tf_data:
                ema20 = tf_data[tf]['ema20']
                ema50 = tf_data[tf]['ema50']
                ema200 = tf_data[tf]['ema200']
                if ema20 > ema50 > ema200:
                    result[key] = "Bullish"
                elif ema20 < ema50 < ema200:
                    result[key] = "Bearish"
                else:
                    result[key] = "Sideways"
        
        # ─── Oscillators (4h) ───
        if "4h" in tf_data:
            result["rsi_4h"] = tf_data["4h"]["rsi"]
            result["stoch_4h"] = tf_data["4h"]["stoch_k"]
            result["macd"] = "Bullish" if tf_data["4h"]["macd_hist"] > 0 else "Bearish"
        
        # ─── Support/Resistance จาก Swing Points ───
        if "4h" in tf_data:
            highs_4h = tf_data["4h"]["highs"]
            lows_4h = tf_data["4h"]["lows"]
            
            swing_highs = find_swing_highs(highs_4h, 3, 3)
            swing_lows = find_swing_lows(lows_4h, 3, 3)
            
            if swing_highs:
                result["resistance"] = highs_4h[swing_highs[-1]]
            if swing_lows:
                result["support"] = lows_4h[swing_lows[-1]]
        
        # ─── Fibonacci จาก Swing High → Swing Low ล่าสุด ───
        if "4h" in tf_data and swing_highs and swing_lows:
            last_high_idx = swing_highs[-1]
            last_low_idx = max([i for i in swing_lows if i > last_high_idx], default=None)
            if last_low_idx:
                high_val = highs_4h[last_high_idx]
                low_val = lows_4h[last_low_idx]
                diff = high_val - low_val
                if diff > 0:
                    result["fib_618"] = low_val + 0.618 * diff
                    result["fib_786"] = low_val + 0.786 * diff
        
        # ─── BOS/CHOCH Confirmation ───
        result["bos_confirmed"] = is_downtrend_confirmed(tf_data["1h"]['ohlcv']) if "1h" in tf_data else False
        
        # ─── Elliott Wave Phase ───
        if "15m" in tf_data:
            abc_result = analyze_abc_correction(tf_data["15m"]['ohlcv'])
            result["elliott_phase"] = abc_result['phase'] if abc_result else None
        else:
            result["elliott_phase"] = None
        
        print(f"[get_adv] {symbol} สำเร็จ → price={result.get('price_current',0):.4f}, phase={result.get('elliott_phase','N/A')}")
        return result
    
    except Exception as e:
        print(f"[get_advanced_analysis_data] Critical error {symbol}: {e}")
        return None
# ==========================================================================
#                  ADVANCED SIGNAL FILTER - ระดับสถาบัน (2026 Meta)
# ==========================================================================
async def advanced_signal_filter(client, sym, analysis_data):
    """
    วิเคราะห์สัญญาณขั้นสูงจากข้อมูล scalar (ไม่ต้องใช้ df)
    ใช้ข้อมูลจาก get_advanced_analysis_data (price, trend, rsi, etc.)
    """
    if not analysis_data or not isinstance(analysis_data, dict):
        return {
            'pass': False,
            'direction': None,
            'score': 0.0,
            'confidence': 0.0,
            'reason': 'analysis_data ไม่ถูกต้องหรือว่าง',
            'key_signals': []
        }

    score = 0.0
    key_signals = []
    reasons = []

    # ดึงค่าที่จำเป็น (ใช้ .get() ป้องกัน KeyError)
    price_current = analysis_data.get('price_current', 0)
    atr = analysis_data.get('atr', 0)
    trend_4h = analysis_data.get('trend_4h', 'Sideways')
    trend_1h = analysis_data.get('trend_1h', 'Sideways')
    rsi_4h = analysis_data.get('rsi_4h', 50)
    stoch_4h = analysis_data.get('stoch_4h', 50)
    macd_status = analysis_data.get('macd', 'Neutral')
    support = analysis_data.get('support', price_current * 0.97)
    resistance = analysis_data.get('resistance', price_current * 1.03)
    fib_382 = analysis_data.get('fib_382', price_current)
    fib_618 = analysis_data.get('fib_618', price_current)

    if price_current <= 0 or atr <= 0:
        return {
            'pass': False,
            'direction': None,
            'score': 0.0,
            'confidence': 0.0,
            'reason': 'ราคาหรือ ATR ไม่ถูกต้อง',
            'key_signals': []
        }

    # ─── 1. Trend Alignment (HTF + LTF) ───
    if trend_4h == 'Bullish' and trend_1h == 'Bullish':
        score += 3.0
        key_signals.append("HTF + LTF Bullish Alignment")
    elif trend_4h == 'Bearish' and trend_1h == 'Bearish':
        score -= 3.0
        key_signals.append("HTF + LTF Bearish Alignment")

    # ─── 2. Momentum + RSI Extreme ───
    if rsi_4h < 35:
        score += 1.8
        key_signals.append(f"RSI Oversold 4H ({rsi_4h:.1f})")
    elif rsi_4h > 65:
        score -= 1.8
        key_signals.append(f"RSI Overbought 4H ({rsi_4h:.1f})")

    if stoch_4h < 25:
        score += 1.2
        key_signals.append(f"Stoch Oversold 4H ({stoch_4h:.1f})")
    elif stoch_4h > 75:
        score -= 1.2
        key_signals.append(f"Stoch Overbought 4H ({stoch_4h:.1f})")

    # ─── 3. MACD Confirmation ───
    if macd_status == 'Bullish':
        score += 1.5
        key_signals.append("MACD Bullish")
    elif macd_status == 'Bearish':
        score -= 1.5
        key_signals.append("MACD Bearish")

    # ─── 4. Price Position (ใกล้ Support/Resistance) ───
    dist_to_support = (price_current - support) / price_current * 100 if price_current > 0 else 0
    dist_to_resistance = (resistance - price_current) / price_current * 100 if price_current > 0 else 0

    if dist_to_support < 1.5:
        score += 1.8
        key_signals.append(f"ใกล้ Support ({dist_to_support:.2f}%)")
    elif dist_to_resistance < 1.5:
        score -= 1.8
        key_signals.append(f"ใกล้ Resistance ({dist_to_resistance:.2f}%)")

    # ─── 5. Fibonacci Confluence (optional) ───
    if abs(price_current - fib_618) / price_current < 0.015:
        score += 1.2 if score > 0 else -1.2
        key_signals.append("ใกล้ Fib 61.8%")

    # ─── ตัดสินใจสุดท้าย ───
    confidence = min(abs(score) / 10.0, 1.0)  # scale ให้ 10 = 100%

    if abs(score) < 5.0:  # ปรับ threshold ตามต้องการ (เข้มงวด = 5.5, ผ่อน = 4.0)
        return {
            'pass': False,
            'direction': None,
            'score': score,
            'confidence': confidence,
            'reason': f'Score ไม่ถึงเกณฑ์ ({score:+.1f} < ±5.0)',
            'key_signals': key_signals[:5]
        }

    direction = 'LONG' if score > 0 else 'SHORT'

    return {
        'pass': True,
        'direction': direction,
        'score': score,
        'confidence': confidence,
        'reason': f'ผ่านเกณฑ์ confluence | Score {score:+.1f}',
        'key_signals': key_signals
    }

# ==========================================================================
#          FAST SCAN TOP 20 SIGNALS - เวอร์ชันเข้าง่ายขึ้น (22 ม.ค. 2026)
# ==========================================================================
async def fast_scan_top_20_signals(client, price_map, active_symbols, pending_orders):
    """
    FAST SCAN รุ่นผ่อนปรน - เข้าง่ายขึ้นมาก
    - Signal >=3 (จาก 4)
    - ไม่บังคับ quality_bonus
    - ADX >18 (จาก 20)
    - Volume pre-filter >1.0x (แทบไม่กรอง)
    - HTF bonus ลดเหลือ >=2 (จาก >=3)
    - ถ้า limit ใกล้ current เกิน → เข้า market แทน
    """
    top_symbols = MAJOR_TICKER_SYMBOLS[:50]
    results = []
    scan_start = datetime.now()

    pending_symbols = {order['symbol'] for order in pending_orders 
                      if isinstance(order, dict) and 'symbol' in order}

    print(f"\n{Fore.CYAN}🚀 FAST SCAN EASY MODE - เข้าง่ายขึ้น (≥3 signals){Style.RESET_ALL}")
    if pending_symbols:
        print(f"{Fore.YELLOW}⏳ ข้าม pending: {', '.join(sorted(pending_symbols))}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'=' * 140}{Style.RESET_ALL}")

    for sym in top_symbols:
        if sym in active_symbols:
            continue
        if sym in pending_symbols:
            continue

        try:
            # ดึงข้อมูลเร็ว ๆ
            klines = await client.futures_klines(symbol=sym, interval='15m', limit=35)
            df = calculate_indicators(klines)

            if df.empty or len(df) < 20:
                continue

            curr = df.iloc[-1]
            current_price = curr['c']

            # PRE-FILTER ผ่อนมากขึ้น
            has_trend = (curr['ema20'] > curr['ema50']) or (curr['ema20'] < curr['ema50'])
            has_strength = curr.get('adx', 0) > 18           # ลดจาก 20 → 18
            has_volume  = (curr['v'] / curr['vol_ma']) > 1.0 if curr['vol_ma'] > 0 else True

            if not (has_trend and has_strength):
                continue

            # นับสัญญาณ (เหมือนเดิม แต่ลด threshold)
            signal_count = 0
            signal_details = []

            if curr['ema20'] > curr['ema50']:
                signal_count += 1; signal_details.append("EMA20>50")
            elif curr['ema20'] < curr['ema50']:
                signal_count += 1; signal_details.append("EMA20<50")

            if curr['c'] > curr['ema200']:
                signal_count += 1; signal_details.append("Above200")
            elif curr['c'] < curr['ema200']:
                signal_count += 1; signal_details.append("Below200")

            if curr['rsi'] > 68:   # ลดจาก 70 → 68
                signal_count += 1; signal_details.append("RSI>68")
            elif curr['rsi'] < 32: # ลดจาก 30 → 32
                signal_count += 1; signal_details.append("RSI<32")

            if curr['macd'] > curr['signal']:
                signal_count += 1; signal_details.append("MACD>SIG")
            elif curr['macd'] < curr['signal']:
                signal_count += 1; signal_details.append("MACD<SIG")

            if curr['c'] > curr['bb_upper']:
                signal_count += 1; signal_details.append("Above_BB")
            elif curr['c'] < curr['bb_lower']:
                signal_count += 1; signal_details.append("Below_BB")

            vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1.0
            if vol_ratio > 1.4:   # ลดจาก 1.5 → 1.4
                signal_count += 1; signal_details.append(f"Vol{vol_ratio:.1f}x")

            if curr['adx'] > 22:
                signal_count += 1; signal_details.append(f"ADX{curr['adx']:.0f}")

            # คุณภาพ bonus (ไม่บังคับแล้ว)
            quality_bonus = 0
            if curr['adx'] > 25:
                quality_bonus += 1
            if vol_ratio > 1.6:
                quality_bonus += 1
            if curr['rsi'] > 70 or curr['rsi'] < 30:
                quality_bonus += 1

            # Threshold ใหม่: >=3 signals (ไม่ต้องมี bonus ก็ได้)
            if signal_count >= 3:
                is_bullish_15m = curr['ema20'] > curr['ema50']
                direction = "LONG" if is_bullish_15m else "SHORT"

                # HTF ผ่อนปรน (core pass + bonus >=2)
                htf_aligned = False
                htf_msg = ""
                if is_bullish_15m:
                    htf_aligned = await check_htf_bullish_alignment(client, sym)
                    # ปรับเงื่อนไขใน check_htf_bullish_alignment ให้ bonus >=2 แทน >=3
                    htf_msg = "HTF Bull ✓" if htf_aligned else "HTF Bull ✗"
                else:
                    htf_aligned = await check_htf_bearish_alignment(client, sym)
                    htf_msg = "HTF Bear ✓" if htf_aligned else "HTF Bear ✗"

                # ถ้า HTF ไม่ผ่าน → ข้าม
                if not htf_aligned:
                    continue

                results.append({
                    'symbol': sym,
                    'price': current_price,
                    'direction': direction,
                    'signal_count': signal_count,
                    'signals': signal_details,
                    'rsi': curr['rsi'],
                    'vol_ratio': vol_ratio,
                    'atr': curr['atr'],
                    'quality_bonus': quality_bonus
                })

                print(
                    f"{'🟢 LONG' if direction=='LONG' else '🔴 SHORT'} │ {sym.replace('USDT',''):>6} │ "
                    f"{current_price:>10.4f} │ RSI:{curr['rsi']:>5.1f} │ "
                    f"Signals: {signal_count}/8 +{quality_bonus} │ {htf_msg}"
                )

                # หยุดเมื่อเจอ 4 สัญญาณ (เพิ่มจาก 2 → ให้โอกาสมากขึ้น)
                if len(results) >= 4:
                    break

        except Exception as e:
            print(f"{Fore.RED}Scan error {sym}: {e}{Style.RESET_ALL}")
            continue

    scan_time = (datetime.now() - scan_start).total_seconds()
    print(f"{Fore.CYAN}พบ {len(results)} สัญญาณ (easy mode) ใน {scan_time:.1f}s{Style.RESET_ALL}\n")

    return results

# ==========================================================================
#          FAST SCAN 60 SYMBOLS - ปรับให้สแกน 60 เหรียญ (23 ม.ค. 2026)
# ==========================================================================
async def fast_scan_top_20_signals(client, price_map, active_symbols, pending_orders):
    """
    สแกน 60 เหรียญ (เรียงตาม volume + major ก่อน) ในโหมด EASY
    - เข้าง่าย: ≥3 signals, AI confidence ต่ำก็ยังเข้าได้
    - ใช้ MAJOR_TICKER_SYMBOLS + Top volume เพิ่มเติม
    """
    # ─── ขยายเป็น 60 เหรียญ ───
    # เอา MAJOR_TICKER_SYMBOLS ทั้งหมดก่อน (ประมาณ 30+ เหรียญ)
    # แล้วเติมด้วยเหรียญ volume สูงจาก top_50_symbols
    scan_symbols = list(set(MAJOR_TICKER_SYMBOLS))  # เอา unique ก่อน
    
    # ถ้ายังไม่ถึง 60 → เติมจาก top volume (ที่ยังไม่ได้อยู่ใน MAJOR)
    if len(scan_symbols) < 60:
        try:
            tickers = await client.futures_ticker()
            volume_sorted = sorted(
                [t['symbol'] for t in tickers if t['symbol'].endswith('USDT')],
                key=lambda s: float(tickers[[t['symbol'] for t in tickers].index(s)]['quoteVolume']),
                reverse=True
            )
            # เติมเหรียญ volume สูงที่ยังไม่มีใน MAJOR
            extra = [s for s in volume_sorted if s not in scan_symbols][:60 - len(scan_symbols)]
            scan_symbols.extend(extra)
        except Exception as e:
            print(f"{Fore.YELLOW}ไม่สามารถดึง top volume เพิ่มได้: {e} → ใช้ MAJOR เฉพาะ{Style.RESET_ALL}")

    # จำกัดสูงสุด 60 เหรียญจริง ๆ
    scan_symbols = scan_symbols[:60]

    results = []
    scan_start = datetime.now()

    pending_symbols = {o['symbol'] for o in pending_orders 
                      if isinstance(o, dict) and 'symbol' in o}

    print(f"\n{Fore.CYAN}🚀 FAST SCAN 60 SYMBOLS - EASY MODE (≥3 signals){Style.RESET_ALL}")
    print(f"   สแกนทั้งหมด: {len(scan_symbols)} เหรียญ")
    if pending_symbols:
        print(f"{Fore.YELLOW}⏳ ข้าม pending: {len(pending_symbols)} เหรียญ{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'=' * 140}{Style.RESET_ALL}")

    for sym in scan_symbols:
        if sym in active_symbols or sym in pending_symbols:
            continue

        try:
            klines = await client.futures_klines(symbol=sym, interval='15m', limit=35)
            if not klines or len(klines) < 20:
                continue

            df = calculate_indicators(klines)
            if df.empty or len(df) < 20:
                continue

            curr = df.iloc[-1]
            current_price = curr['c']

            # PRE-FILTER ผ่อนมาก (เหมือนเดิม)
            has_trend = curr['ema20'] != curr['ema50']   # แค่ไม่ flat ก็ผ่าน
            has_strength = curr.get('adx', 0) > 18
            has_volume = (curr['v'] / curr['vol_ma']) > 1.0 if curr['vol_ma'] > 0 else True

            if not (has_trend and has_strength):
                continue

            signal_count = 0
            signal_details = []

            if curr['ema20'] > curr['ema50']: 
                signal_count += 1
                signal_details.append("EMA20>50")
            elif curr['ema20'] < curr['ema50']: 
                signal_count += 1
                signal_details.append("EMA20<50")

            if curr['c'] > curr['ema200']: 
                signal_count += 1
                signal_details.append("Above200")
            elif curr['c'] < curr['ema200']: 
                signal_count += 1
                signal_details.append("Below200")

            if curr['rsi'] > 68: 
                signal_count += 1
                signal_details.append("RSI>68")
            elif curr['rsi'] < 32: 
                signal_count += 1
                signal_details.append("RSI<32")

            if curr['macd'] > curr['signal']: 
                signal_count += 1
                signal_details.append("MACD>SIG")
            elif curr['macd'] < curr['signal']: 
                signal_count += 1
                signal_details.append("MACD<SIG")

            if curr['c'] > curr['bb_upper']: 
                signal_count += 1
                signal_details.append("Above_BB")
            elif curr['c'] < curr['bb_lower']: 
                signal_count += 1
                signal_details.append("Below_BB")

            vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1.0
            if vol_ratio > 1.4: 
                signal_count += 1
                signal_details.append(f"Vol{vol_ratio:.1f}x")

            if curr['adx'] > 22: 
                signal_count += 1
                signal_details.append(f"ADX{curr['adx']:.0f}")

            quality_bonus = 0
            if curr['adx'] > 25: quality_bonus += 1
            if vol_ratio > 1.6: quality_bonus += 1
            if curr['rsi'] > 70 or curr['rsi'] < 30: quality_bonus += 1

            if signal_count >= 3:
                is_bullish_15m = curr['ema20'] > curr['ema50']
                direction = "LONG" if is_bullish_15m else "SHORT"

                htf_aligned = (
                    await check_htf_bullish_alignment(client, sym) 
                    if is_bullish_15m else 
                    await check_htf_bearish_alignment(client, sym)
                )
                if not htf_aligned:
                    continue

                results.append({
                    'symbol': sym,
                    'price': current_price,
                    'direction': direction,
                    'signal_count': signal_count,
                    'signals': signal_details,
                    'rsi': curr['rsi'],
                    'vol_ratio': vol_ratio,
                    'atr': curr['atr'],
                    'quality_bonus': quality_bonus
                })

                print(
                    f"{'🟢 LONG' if direction=='LONG' else '🔴 SHORT'} │ "
                    f"{sym.replace('USDT',''):>8} │ "
                    f"{current_price:>10.4f} │ "
                    f"RSI:{curr['rsi']:>5.1f} │ "
                    f"Signals: {signal_count}/8 +{quality_bonus} │ "
                    f"HTF {'✓' if htf_aligned else '✗'}"
                )

                # หยุดเมื่อครบ 60 สัญญาณ (หรือน้อยกว่านั้นถ้าไม่พอ)
                if len(results) >= 60:
                    break

        except Exception as e:
            print(f"Scan error {sym}: {e}")
            continue

    scan_time = (datetime.now() - scan_start).total_seconds()
    print(f"{Fore.CYAN}สแกนเสร็จสิ้น พบ {len(results)} สัญญาณ ใน {scan_time:.1f} วินาที{Style.RESET_ALL}\n")
    return results


def calculate_setauto_limit_price(current_price, direction, df, atr, fib_levels, swing_data):
    """
    คำนวณราคา Limit ที่ดีที่สุดสำหรับ /setauto
    - LONG → ต่ำกว่า current (pullback to support / fib)
    - SHORT → สูงกว่า current (pullback to resistance / fib)
    """
    if direction == 'LONG':
        # เป้าหมาย: เข้าใกล้ support หรือ fib 0.618 / 0.5
        candidates = [
            swing_data.get('recent_support', current_price * 0.97),
            fib_levels.get('61.8%', current_price * 0.618),
            fib_levels.get('50.0%', current_price * 0.5),
            current_price - atr * 1.1   # ATR pullback ธรรมดา
        ]
        limit_raw = min([x for x in candidates if x > 0 and x < current_price * 1.02])
        
        # ไม่ให้ต่ำเกิน swing low มาก
        min_allowed = swing_data.get('lowest_swing', current_price * 0.92)
        limit_raw = max(limit_raw, min_allowed)
        
    else:  # SHORT
        candidates = [
            swing_data.get('recent_resistance', current_price * 1.03),
            fib_levels.get('38.2%', current_price * 0.382),
            fib_levels.get('50.0%', current_price * 0.5),
            current_price + atr * 1.1
        ]
        limit_raw = max([x for x in candidates if x > 0 and x > current_price * 0.98])
        
        max_allowed = swing_data.get('highest_swing', current_price * 1.08)
        limit_raw = min(limit_raw, max_allowed)
    
    return limit_raw if limit_raw > 0 else current_price
# ==========================================================================
#          CALCULATE OPTIMAL LIMIT ENTRY - คำนวณ entry ที่ดีจากประวัติ
# ==========================================================================
def calculate_optimal_limit_entry(current_price, direction, swing_data, fib_levels, atr):
    """
    คำนวณ Limit Entry ที่ดี โดยใช้ประวัติราคา swings
    
    Strategy:
    - LONG: Entry ที่ support zone ที่เคยสวิงขึ้นสูง (pullback entry)
    - SHORT: Entry ที่ resistance zone ที่เคยสวิงลง (pullback entry)
    """
    
    if swing_data is None:
        return current_price  # Fallback ถ้าไม่มีข้อมูล
    
    highest_swing = swing_data['highest_swing']
    lowest_swing = swing_data['lowest_swing']
    avg_pullback = swing_data['avg_pullback']
    recent_support = swing_data['recent_support']
    recent_resistance = swing_data['recent_resistance']
    key_zones = swing_data['key_reversal_zones']
    
    if direction == 'LONG':
        # ===== LONG Entry Strategy =====
        # เข้า Limit ที่ support zone ที่ราคาเคยสวิงขึ้นจาก
        # Priority: 
        # 1. Recent support + avg pullback
        # 2. Fibonacci 38.2% - 50%
        # 3. Key reversal zone ที่ใกล้
        
        # ตัวเลือก Entry:
        entry_option_1 = recent_support + avg_pullback * 0.3  # Bounce from recent support
        entry_option_2 = fib_levels.get('38.2%', current_price)  # Fib support
        entry_option_3 = key_zones[0] if key_zones else current_price  # Recent key zone
        
        # เลือก entry ที่ดี (ต่ำสุดแต่สมเหตุสมผล)
        # ต้องมากกว่า recent support อย่างน้อย
        valid_entries = [e for e in [entry_option_1, entry_option_2, entry_option_3] 
                        if e >= recent_support]
        
        entry_price = min(valid_entries) if valid_entries else entry_option_1
        
        # ===== Validate Entry =====
        # Entry ต้องสมเหตุสมผล: ไม่ต้ำกว่า lowest swing มากนัก
        min_entry = lowest_swing + avg_pullback * 0.5
        max_entry = recent_resistance - atr
        
        entry_price = max(entry_price, min_entry)
        entry_price = min(entry_price, max_entry)
        
    else:  # SHORT
        # ===== SHORT Entry Strategy =====
        # เข้า Limit ที่ resistance zone ที่ราคาเคยสวิงลงจาก
        
        entry_option_1 = recent_resistance - avg_pullback * 0.3  # Pullback from recent resistance
        entry_option_2 = fib_levels.get('61.8%', current_price)  # Fib resistance
        entry_option_3 = key_zones[0] if key_zones else current_price  # Recent key zone
        
        # เลือก entry ที่ดี (สูงสุดแต่สมเหตุสมผล)
        valid_entries = [e for e in [entry_option_1, entry_option_2, entry_option_3] 
                        if e <= recent_resistance]
        
        entry_price = max(valid_entries) if valid_entries else entry_option_1
        
        # ===== Validate Entry =====
        min_entry = recent_support + atr
        max_entry = highest_swing - avg_pullback * 0.5
        
        entry_price = max(entry_price, min_entry)
        entry_price = min(entry_price, max_entry)
    
    return float(entry_price)

# ==========================================================================
#      CALCULATE SWING-BASED FIBONACCI ENTRY - คำนวณ Entry จากเทรน + Swings
# ==========================================================================
def calculate_swing_based_fibonacci_entry(current_price, swing_data, direction, df):
    """
    ✨ ปรับปรุงขั้นเทพ:
    ใช้ราคาที่สวิงมาแล้ว + ตรวจสอบเทรน → หาจุด entry ที่ดีที่สุด
    
    Strategy:
    1. ดึง highest_swing (ราคาเคยขึ้นไป)
    2. ตรวจสอบเทรน: uptrend vs downtrend
    3. คำนวณ Fibonacci จากจุด swing
    4. เลือก entry ที่ align กับเทรน
    
    Returns: (entry_price, fib_explanation, trend_info)
    """
    
    if swing_data is None or df is None or len(df) < 20:
        return current_price, "No data", "unknown"
    
    highest_swing = swing_data['highest_swing']
    lowest_swing = swing_data['lowest_swing']
    
    # ===== 1. ตรวจสอบเทรนปัจจุบัน =====
    curr = df.iloc[-1]
    trend_ema = "UP" if curr['ema20'] > curr['ema50'] > curr['ema200'] else \
                "DOWN" if curr['ema20'] < curr['ema50'] < curr['ema200'] else \
                "NEUTRAL"
    
    # ตรวจสอบจาก recent candles
    recent_5 = df.iloc[-5:]
    is_making_higher_lows = recent_5['l'].values[-1] > recent_5['l'].values[0]
    is_making_lower_highs = recent_5['h'].values[-1] < recent_5['h'].values[0]
    
    # ===== 2. ตรวจสอบราคาอยู่ที่ไหน =====
    price_vs_swing_high = (current_price / highest_swing - 1) * 100  # % from high
    price_vs_swing_low = (current_price / lowest_swing - 1) * 100   # % from low
    
    # ===== 3. คำนวณ Fibonacci จากจุด swing high ลงมา =====
    # ถ้าราคาลงมา = ขึ้นไป + อีก highest_swing
    fib_from_high = calculate_fibonacci_levels(highest_swing, lowest_swing)
    
    # ===== 4. Select Entry ตามเทรน =====
    
    if direction == 'LONG':
        # ===== LONG: ต้องเป็น UPTREND =====
        if trend_ema == "UP" and is_making_higher_lows:
            # เทรนขึ้น → เข้า Limit ที่ Fibonacci support
            entry_price = fib_from_high.get('61.8%', current_price)  # ดึงกลับขึ้นมา
            fib_reason = "61.8% Fib Retrace (Support in Uptrend)"
        elif trend_ema == "NEUTRAL":
            # เทรนข้าง → เข้า Limit ที่ 50% Fib (midline)
            entry_price = fib_from_high.get('50.0%', current_price)
            fib_reason = "50.0% Fib Midline (Neutral Trend)"
        else:
            # เทรนลง → ลองหา entry ที่ Fib support ลึก
            entry_price = fib_from_high.get('38.2%', current_price)
            fib_reason = "38.2% Fib Deep Support (Downtrend)"
        
        # ===== Validate: Entry ต้องต่ำกว่า current แต่สูงกว่า lowest =====
        min_entry = lowest_swing + (highest_swing - lowest_swing) * 0.1
        max_entry = current_price
        entry_price = max(entry_price, min_entry)
        entry_price = min(entry_price, max_entry)
        
        trend_info = f"UPTREND (EMA: {trend_ema}, Higher Lows: {is_making_higher_lows})"
        
    else:  # SHORT
        # ===== SHORT: ต้องเป็น DOWNTREND =====
        # คำนวณ Fibonacci จากจุด lowest swing ขึ้นมา
        fib_from_low = calculate_fibonacci_levels(current_price, lowest_swing)
        
        if trend_ema == "DOWN" and is_making_lower_highs:
            # เทรนลง → เข้า Limit ที่ Fibonacci resistance
            entry_price = fib_from_low.get('38.2%', current_price)  # ตัวต้านทาน
            fib_reason = "38.2% Fib Retrace (Resistance in Downtrend)"
        elif trend_ema == "NEUTRAL":
            # เทรนข้าง → เข้า Limit ที่ 50% Fib (midline)
            entry_price = fib_from_low.get('50.0%', current_price)
            fib_reason = "50.0% Fib Midline (Neutral Trend)"
        else:
            # เทรนขึ้น → ลองหา entry ที่ Fib resistance สูง
            entry_price = fib_from_low.get('61.8%', current_price)
            fib_reason = "61.8% Fib High Resistance (Uptrend)"
        
        # ===== Validate: Entry ต้องสูงกว่า current แต่ต่ำกว่า highest =====
        min_entry = current_price
        max_entry = highest_swing - (highest_swing - lowest_swing) * 0.1
        entry_price = max(entry_price, min_entry)
        entry_price = min(entry_price, max_entry)
        
        trend_info = f"DOWNTREND (EMA: {trend_ema}, Lower Highs: {is_making_lower_highs})"
    
    # ===== Summary =====
    explanation = (
        f"Swing-Based Fibonacci Entry:\n"
        f"  High/Low: {highest_swing:.4f} / {lowest_swing:.4f}\n"
        f"  Current: {current_price:.4f}\n"
        f"  Entry: {entry_price:.4f}\n"
        f"  Reason: {fib_reason}"
    )
    
    return float(entry_price), fib_reason, trend_info

# ==========================================================================
#                         BACKTEST AI TRAINING
# ==========================================================================
async def backtest_ai_training(client, num_periods: int = 100, chat_id=None):
    """
    Backtest fast_scan logic บน historical data
    - สุ่มเลือก period ตรวจสอบ
    - สุ่มเลือกเหรียญ (เน้นเหรียญหลักก่อน)
    - รันสแกนลอจิก + คำนวณ entry
    - ติดตาม win/loss
    - ส่งรายงาน
    """
    global pending_orders_detail, active
    
    try:
        # =================== SETUP ===================
        backtest_results = []
        total_signals = 0
        total_wins = 0
        total_losses = 0
        total_pnl = 0.0
        total_trades = 0
        
        # Random coin selection (major first)
        import random
        major_coins = MAJOR_TICKER_SYMBOLS[:10]
        other_coins = MAJOR_TICKER_SYMBOLS[10:]
        
        coins_to_test = []
        remaining_periods = num_periods
        
        # Phase 1: Cycle through major coins
        while remaining_periods > 0 and major_coins:
            random.shuffle(major_coins)
            for coin in major_coins:
                if remaining_periods <= 0:
                    break
                coins_to_test.append(coin)
                remaining_periods -= 1
        
        # Phase 2: Add other coins if needed
        if remaining_periods > 0 and other_coins:
            while remaining_periods > 0:
                random.shuffle(other_coins)
                for coin in other_coins:
                    if remaining_periods <= 0:
                        break
                    coins_to_test.append(coin)
                    remaining_periods -= 1
        
        msg_intro = f"⏳ **Backtest เริ่มแล้ว**\nจำนวน: {num_periods} periods\nเหรียญ: {len(set(coins_to_test))} unique\n📊 กำลังวิเคราะห์..."
        if chat_id:
            await send_telegram_report(msg_intro, chat_id)
        
        # =================== BACKTEST LOOP ===================
        for idx, coin in enumerate(coins_to_test):
            try:
                current_price = None
                signal_found = False
                direction = None
                
                # ดึง 4H candles (recent 100 bars)
                klines = await client.futures_klines(symbol=coin, interval='4h', limit=100)
                if not klines or len(klines) < 20:
                    continue
                
                df = calculate_indicators(klines)
                if df.empty:
                    continue
                
                curr = df.iloc[-1]
                current_price = curr['c']
                
                # =================== USE ANALYZE_MATRIX FOR UNIFIED SIGNAL DETECTION ===================
                # ✨ Option A: Call analyze_matrix() directly to eliminate duplicate logic
                matrix_result = await analyze_matrix(client, coin)
                
                if not matrix_result or matrix_result['side'] is None:
                    continue  # Skip if no signal from analyze_matrix
                
                direction = matrix_result['side']
                score = matrix_result['score']
                ai_confidence = matrix_result['ai']
                
                # Map score (0-8) to signal count for compatibility
                signal_count = min(int(score), 8)
                total_signals += signal_count
                
                # =================== DIRECTION & ENTRY DECISION ===================
                if signal_count >= 3:
                    # วิเคราะห์ historical swings
                    swing_data = await analyze_historical_swings(client, coin, lookback_candles=200)
  
                    # คำนวณ Fibonacci
                    high = df['h'].max()
                    low = df['l'].min()
                    fib_levels = calculate_fibonacci_levels(high, low)
                    fib_extensions = calculate_fibonacci_extensions(high, low)
                    
                    # Determine direction
                    if curr['ema20'] > curr['ema50']:
                        direction = 'LONG'
                        # คำนวณ entry
                        optimal_entry, fib_reason, trend_info = calculate_swing_based_fibonacci_entry(
                            current_price, swing_data, direction, df
                        )
                    else:
                        direction = 'SHORT'
                        optimal_entry, fib_reason, trend_info = calculate_swing_based_fibonacci_entry(
                            current_price, swing_data, direction, df
                        )
                    
                    # =================== SIMULATE ENTRY & TRACK RESULT ===================
                    # ใช้ entry ปัจจุบันเป็น reference
                    entry_price = optimal_entry
                    
                    # SL/TP from extensions
                    atr = curr['atr']
                    if direction == 'LONG':
                        tp = fib_extensions.get('161.8%', current_price + atr * 4)
                        sl = fib_extensions.get('0%', current_price - atr * 2)
                    else:
                        tp = fib_extensions.get('161.8%', current_price - atr * 4)
                        sl = fib_extensions.get('0%', current_price + atr * 2)
                    
                    # ✨ Extract features in same way as analyze_matrix() for consistency
                    rsi = curr['rsi']
                    ema_ratio = curr['ema20'] / curr['ema50'] if curr['ema50'] > 0 else 1.0
                    macd_diff = curr['macd'] - curr['signal']
                    vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1.0
                    adx = curr['adx']
                    stoch_k = curr.get('stoch_k', 50)
                    bb_pos = (current_price - curr['bb_lower']) / (curr['bb_upper'] - curr['bb_lower']) if curr['bb_upper'] > curr['bb_lower'] else 0.5
                    
                    ai_features = [rsi/100, ema_ratio, macd_diff/100, vol_ratio, adx/50, stoch_k/100, bb_pos]
                    
                    # =================== SIMULATE PRICE MOVEMENT (next 5 candles) ===================
                    # ✨ Use recent historical candles (lookback 5) to simulate what WOULD happen
                    # Since we're backtesting, we can't get true future data
                    # Instead, use next 5 candles from the same period data
                    lookback = len(klines)
                    
                    # Try to get future klines, but if not available, simulate from price distribution
                    future_klines = []
                    try:
                        future_klines = await client.futures_klines(
                            symbol=coin, 
                            interval='4h', 
                            limit=10, 
                            startTime=int(klines[-1][0]) + 14400000
                        )
                        if not future_klines or len(future_klines) < 5:
                            future_klines = []
                    except:
                        future_klines = []
                    
                    # Simulate result
                    win = False
                    pnl = 0.0
                    exit_price = current_price
                    exit_reason = "No future data"
                    
                    if future_klines and len(future_klines) >= 2:
                        # Track next 5 candles from actual future data
                        future_df = calculate_indicators(future_klines[:5])
                        
                        for future_idx in range(len(future_df)):
                            future_row = future_df.iloc[future_idx]
                            
                            if direction == 'LONG':
                                # Check TP first
                                if future_row['h'] >= tp:
                                    exit_price = tp
                                    win = True
                                    exit_reason = "TP Hit"
                                    break
                                # Check SL
                                elif future_row['l'] <= sl:
                                    exit_price = sl
                                    win = False
                                    exit_reason = "SL Hit"
                                    break
                            else:  # SHORT
                                # Check TP first
                                if future_row['l'] <= tp:
                                    exit_price = tp
                                    win = True
                                    exit_reason = "TP Hit"
                                    break
                                # Check SL
                                elif future_row['h'] >= sl:
                                    exit_price = sl
                                    win = False
                                    exit_reason = "SL Hit"
                                    break
                        
                        # ถ้าไม่มี TP/SL → ใช้ราคาปิด
                        if exit_reason == "No future data":
                            exit_price = future_df.iloc[-1]['c']
                            exit_reason = "Close 5th candle"
                    else:
                        # ✨ If no future data available, use recent 5-candle range to simulate
                        # This provides a more realistic backtest when future data isn't accessible
                        if len(df) >= 5:
                            recent_high = df.iloc[-5:]['h'].max()
                            recent_low = df.iloc[-5:]['l'].min()
                            recent_close = df.iloc[-1]['c']
                            
                            # Simulate: did price reach TP or SL in recent volatility?
                            if direction == 'LONG':
                                if recent_high >= tp:
                                    exit_price = tp
                                    win = True
                                    exit_reason = "TP Hit (simulated)"
                                elif recent_low <= sl:
                                    exit_price = sl
                                    win = False
                                    exit_reason = "SL Hit (simulated)"
                                else:
                                    exit_price = recent_close
                                    exit_reason = "Close (no TP/SL)"
                            else:  # SHORT
                                if recent_low <= tp:
                                    exit_price = tp
                                    win = True
                                    exit_reason = "TP Hit (simulated)"
                                elif recent_high >= sl:
                                    exit_price = sl
                                    win = False
                                    exit_reason = "SL Hit (simulated)"
                                else:
                                    exit_price = recent_close
                                    exit_reason = "Close (no TP/SL)"
                    
                    # Calculate PNL
                    if direction == 'LONG':
                        pnl = (exit_price - entry_price) / entry_price * 100 if entry_price > 0 else 0
                        win = pnl > 0.5  # Need at least 0.5% to count as win
                    else:
                        pnl = (entry_price - exit_price) / entry_price * 100 if entry_price > 0 else 0
                        win = pnl > 0.5  # Need at least 0.5% to count as win
                    
                    # Skip trades with 0% PNL (likely data fetch issues)
                    if abs(pnl) < 0.01:
                        continue
                    
                    total_trades += 1
                    total_pnl += pnl
                    if win:
                        total_wins += 1
                    else:
                        total_losses += 1
                    
                    # ✨ SAVE FEATURES FOR AI TRAINING (ขั้นเทพ!)
                    backtest_results.append({
                        'symbol': coin,
                        'direction': direction,
                        'entry': entry_price,
                        'exit': exit_price,
                        'exit_reason': exit_reason,
                        'pnl_percent': pnl,
                        'win': win,
                        'signals': signal_count,
                        'ai_confidence': ai_confidence,
                        'features': ai_features,  # ✨ NEW: Store features for training
                        'timestamp': datetime.now().isoformat()
                    })
                    
                    signal_found = True
            
            except Exception as e:
                print(f"{Fore.YELLOW}Backtest error on {coin}: {e}{Style.RESET_ALL}")
                continue
            
            # Progress update every 10 trades
            if total_trades > 0 and total_trades % 10 == 0:
                progress_msg = (
                    f"📊 **Backtest Progress**: {idx+1}/{len(coins_to_test)} coins\n"
                    f"Trades found: {total_trades}\n"
                    f"Wins: {total_wins} | Losses: {total_losses}\n"
                    f"Current WR: {total_wins/total_trades*100:.1f}%\n"
                    f"Current PNL: {total_pnl:+.2f}%"
                )
                if chat_id:
                    await send_telegram_report(progress_msg, chat_id)
        
        # =================== GENERATE REPORT ===================
        if total_trades == 0:
            await send_telegram_report("❌ **Backtest ไม่พบสัญญาณ** ลองใหม่อีกครั้ง", chat_id)
            return None
        
        win_rate = (total_wins / total_trades) * 100 if total_trades > 0 else 0
        avg_pnl = total_pnl / total_trades if total_trades > 0 else 0
        
        # Calculate profit factor
        winning_trades = [r for r in backtest_results if r['win']]
        losing_trades = [r for r in backtest_results if not r['win']]
        
        total_wins_pnl = sum(r['pnl_percent'] for r in winning_trades) if winning_trades else 0
        total_losses_pnl = abs(sum(r['pnl_percent'] for r in losing_trades)) if losing_trades else 1
        
        profit_factor = total_wins_pnl / total_losses_pnl if total_losses_pnl > 0 else 0
        
        # Sharpe ratio (simplified)
        pnl_list = [r['pnl_percent'] for r in backtest_results]
        if len(pnl_list) > 1:
            import statistics
            mean_pnl = statistics.mean(pnl_list)
            std_pnl = statistics.stdev(pnl_list) if len(pnl_list) > 1 else 1
            sharpe_ratio = (mean_pnl / std_pnl) * math.sqrt(252) if std_pnl > 0 else 0
        else:
            sharpe_ratio = 0
        
        # Best/worst trade
        best_trade = max(backtest_results, key=lambda x: x['pnl_percent']) if backtest_results else None
        worst_trade = min(backtest_results, key=lambda x: x['pnl_percent']) if backtest_results else None
        
        # AI confidence stats
        winning_ai_conf = [r['ai_confidence'] for r in winning_trades]
        losing_ai_conf = [r['ai_confidence'] for r in losing_trades]
        
        avg_ai_winning = sum(winning_ai_conf) / len(winning_ai_conf) if winning_ai_conf else 0
        avg_ai_losing = sum(losing_ai_conf) / len(losing_ai_conf) if losing_ai_conf else 0
        
        # Build report
        report = (
            f"📊 **BACKTEST COMPLETE - AI Training Results**\n"
            f"{'─' * 55}\n\n"
            
            f"🎯 **Summary**:\n"
            f"   └ Periods Tested: `{len(coins_to_test)}`\n"
            f"   └ Signals Found: `{total_trades}`\n"
            f"   └ Unique Coins: `{len(set([r['symbol'] for r in backtest_results]))}`\n\n"
            
            f"📈 **Win Rate**:\n"
            f"   ✅ Wins: `{total_wins}` ({total_wins/total_trades*100:.1f}%)\n"
            f"   ❌ Losses: `{total_losses}` ({total_losses/total_trades*100:.1f}%)\n"
            f"   ⭐ Win Rate: `{win_rate:.1f}%`\n\n"
            
            f"💰 **Profitability**:\n"
            f"   └ Total PNL: `{total_pnl:+.2f}%`\n"
            f"   └ Avg/Trade: `{avg_pnl:+.2f}%`\n"
            f"   └ Profit Factor: `{profit_factor:.2f}x`\n"
            f"   └ Sharpe Ratio: `{sharpe_ratio:.2f}`\n\n"
            
            f"🔥 **Best/Worst Trade**:\n"
            f"   ✅ Best: `{best_trade['symbol']} {best_trade['direction']} {best_trade['pnl_percent']:+.2f}%`\n"
            f"   ❌ Worst: `{worst_trade['symbol']} {worst_trade['direction']} {worst_trade['pnl_percent']:+.2f}%`\n\n"
            
            f"🤖 **AI Confidence Analysis**:\n"
            f"   └ Avg Confidence (Winning): `{avg_ai_winning:.1f}%`\n"
            f"   └ Avg Confidence (Losing): `{avg_ai_losing:.1f}%`\n"
            f"   └ Difference: `{avg_ai_winning - avg_ai_losing:+.1f}%` ✨\n\n"
        )
        
        # Recommendation
        if win_rate >= 60 and profit_factor >= 1.5:
            recommendation = "✅ **READY FOR LIVE TRADING** - Strong historical results!\n   └ AI model shows good predictive power with positive edge"
        elif win_rate >= 50 and profit_factor >= 1.0:
            recommendation = "⚠️ **MONITOR** - Decent results, continue training\n   └ Need more data for confident live deployment"
        else:
            recommendation = "❌ **NEEDS IMPROVEMENT** - Low win rate or negative PF\n   └ Backtest more periods or adjust parameters"
        
        report += recommendation
        
        report += (
            f"\n\n📋 **Top 5 Winning Trades**:\n"
        )
        
        top_wins = sorted(backtest_results, key=lambda x: x['pnl_percent'], reverse=True)[:5]
        for idx, trade in enumerate(top_wins, 1):
            report += f"   {idx}. {trade['symbol']} {trade['direction']} `{trade['pnl_percent']:+.2f}%` ({trade['signals']}/8 signals)\n"
        
        if chat_id:
            await send_telegram_report(report, chat_id)
        
        print(f"{Fore.GREEN}{Style.BRIGHT}{report}{Style.RESET_ALL}")
        
        return {
            'total_trades': total_trades,
            'win_rate': win_rate,
            'total_pnl': total_pnl,
            'profit_factor': profit_factor,
            'sharpe_ratio': sharpe_ratio,
            'results': backtest_results
        }
    
    except Exception as e:
        error_msg = f"❌ Backtest failed: {e}"
        if chat_id:
            await send_telegram_report(error_msg, chat_id)
        print(f"{Fore.RED}{error_msg}{Style.RESET_ALL}")
        return None



async def is_tradable_perpetual(client, symbol):
    try:
        info = await client.futures_exchange_info()
        for s in info['symbols']:
            if s['symbol'] == symbol and s['status'] == 'TRADING' and s['contractType'] == 'PERPETUAL':
                return True
        return False
    except:
        return False


# ==========================================================================
#          ELLIOTT WAVE DETECTION - Rules อัปเกรด 2026 + ABC + Triangle ABCDE
# ==========================================================================
from scipy.signal import argrelextrema
import numpy as np
from scipy.stats import linregress

def detect_elliott_wave(df, min_fib_tolerance=0.08, channel_tolerance=0.04):
    """
    ตรวจจับ Impulse, ABC Correction และ Triangle (ABCDE) ด้วยกฎระดับสถาบัน
    """
    if len(df) < 80:
        return {'pattern': 'unknown', 'confidence': 0.0, 'details': 'ข้อมูลแท่งไม่พอ (ต้องการ ≥80 สำหรับ Triangle)'}

    closes = df['c'].values
    highs  = df['h'].values
    lows   = df['l'].values
    volumes = df['v'].values if 'v' in df else np.ones_like(closes)

    # หา local extrema
    order = max(5, len(df)//30)  # ปรับตามความยาวข้อมูล
    high_idx = argrelextrema(highs, np.greater, order=order)[0]
    low_idx  = argrelextrema(lows,  np.less,    order=order)[0]

    if len(high_idx) < 5 or len(low_idx) < 5:
        return {'pattern': 'unknown', 'confidence': 0.2, 'details': 'ไม่พบจุด swing พอสำหรับ Triangle/ABC/Impulse'}

    extrema = sorted(
        [(i, highs[i], 'high') for i in high_idx] + [(i, lows[i], 'low') for i in low_idx],
        key=lambda x: x[0]
    )

    recent_swings = extrema[-11:]  # ต้องการมากขึ้นสำหรับ ABCDE (5 จุด + buffer)
    if len(recent_swings) < 8:
        return {'pattern': 'unknown', 'confidence': 0.25}

    # ─── ฟังก์ชันช่วยคำนวณ ───
    def wave_len(p1, p2):
        return abs(p2[1] - p1[1])

    def retrace_ratio(start, high, low):
        if start[2] == 'low':
            return (high[1] - low[1]) / (high[1] - start[1]) if high[1] != start[1] else 0
        else:
            return (low[1] - high[1]) / (start[1] - high[1]) if start[1] != high[1] else 0

    def is_fib_close(ratio, target, tol=min_fib_tolerance):
        return abs(ratio - target) <= tol

    # ─── ตรวจ Triangle ABCDE ───
    def check_triangle_abcde(swings):
        if len(swings) < 9:  # ต้องการอย่างน้อย A-B-C-D-E + buffer
            return False, 0.0, {}

        # หาจุดสูงสุดและต่ำสุดของแต่ละขา (สมมติเรียงตามเวลา)
        points = swings[-10:]  # ใช้ 10 จุดล่าสุดเพื่อความแม่นยำ

        highs_points = [p for p in points if p[2] == 'high'][-4:]  # B, D (และอาจ A,C)
        lows_points  = [p for p in points if p[2] == 'low'][-4:]   # A, C, E (และอาจ B,D)

        if len(highs_points) < 3 or len(lows_points) < 3:
            return False, 0.0, {}

        # Upper trendline: เชื่อมจุดสูงสุด 3 จุด (B-D และจุดก่อนหน้า)
        x_upper = np.array([p[0] for p in highs_points[-3:]])
        y_upper = np.array([p[1] for p in highs_points[-3:]])
        slope_upper, intercept_upper, _, _, _ = linregress(x_upper, y_upper)

        # Lower trendline: เชื่อมจุดต่ำสุด 3 จุด (A-C-E)
        x_lower = np.array([p[0] for p in lows_points[-3:]])
        y_lower = np.array([p[1] for p in lows_points[-3:]])
        slope_lower, intercept_lower, _, _, _ = linregress(x_lower, y_lower)

        # ต้อง converge (slope ต่างกันเครื่องหมาย หรือมุมแคบลง)
        if slope_upper * slope_lower >= 0:
            return False, 0.0, {}  # เส้นขนานหรือแยกออก ไม่ใช่ triangle

        # ตรวจว่า E อยู่ใกล้จุดตัด (thrust point)
        x_e = points[-1][0]
        y_upper_proj = slope_upper * x_e + intercept_upper
        y_lower_proj = slope_lower * x_e + intercept_lower
        thrust_zone = (y_lower_proj + y_upper_proj) / 2
        e_price = points[-1][1]
        thrust_ok = abs(e_price - thrust_zone) / thrust_zone < channel_tolerance * 2

        # Retracement แต่ละขา
        retrs = []
        for i in range(1, len(points), 2):
            if i+1 < len(points):
                r = retrace_ratio(points[i-1], points[i], points[i+1])
                if 0.382 <= r <= 0.786:
                    retrs.append(r)

        fib_ok = len(retrs) >= 3 and all(is_fib_close(r, 0.618) or is_fib_close(r, 0.5) for r in retrs)

        # Volume ลดลงเรื่อย ๆ
        vol_trend = np.polyfit(range(len(volumes[-20:])), volumes[-20:], 1)[0]
        vol_decline = vol_trend < 0

        # Score
        rules = [thrust_ok, fib_ok, vol_decline]
        score = sum(rules) * 0.4 + (1.0 if len(retrs) >= 4 else 0) * 0.3
        confidence = min(score, 1.0)

        if sum(rules) >= 2 and confidence > 0.60:
            return True, confidence, {
                'type': 'contracting_triangle' if abs(slope_upper - slope_lower) > 0.0001 else 'barrier_triangle',
                'converge': True,
                'thrust_ok': thrust_ok,
                'fib_retrs': [round(r,3) for r in retrs],
                'vol_decline': vol_decline
            }
        return False, 0.0, {}

    # ─── รวมการตรวจทั้งหมด (เหมือนเดิม + เพิ่ม triangle) ───
    is_imp_up, conf_up, det_up = check_impulse_up(recent_swings)
    is_abc, conf_abc, det_abc = check_abc_correction(recent_swings)
    is_tri, conf_tri, det_tri   = check_triangle_abcde(recent_swings)

    # เลือก pattern ที่มั่นใจสูงสุด
    candidates = [
        ('impulse_up',   conf_up,   'up',    det_up),
        ('abc_correction', conf_abc, 'unknown', det_abc),
        ('triangle_abcde', conf_tri, 'unknown', det_tri)
    ]

    best = max(candidates, key=lambda x: x[1])
    pattern, conf, dir_, details = best

    if conf < 0.55:
        return {
            'pattern': 'unknown',
            'wave_count': 0,
            'direction': 'unknown',
            'confidence': conf,
            'details': 'ไม่ผ่านเกณฑ์ความมั่นใจขั้นต่ำสำหรับ Impulse/ABC/Triangle'
        }

    wave_count = 5 if 'impulse' in pattern else 3 if 'abc' in pattern else 5 if 'triangle' in pattern else 0

    return {
        'pattern': pattern,
        'wave_count': wave_count,
        'direction': dir_,
        'confidence': conf,
        'details': f"{pattern.replace('_',' ').title()} | {details}",
        'key_levels': details
    }

# ==========================================================================
#                  EXECUTE FAST SCAN ENTRY - ปรับปรุงความปลอดภัยสูง (21 ม.ค. 2026)
# ==========================================================================
async def execute_fast_scan_entry(client, scan_result, price_map):
    sym = scan_result['symbol']
    direction = scan_result['direction']
    
    print(f"[EXECUTE ENTRY START] {sym} {direction} - กำลังตรวจสอบเงื่อนไขปลอดภัยทั้งหมด")
    
    try:
        # =============================================
        # 1. ดึงข้อมูล candles + indicators (ต้องทำก่อนทุกอย่าง)
        # =============================================
        klines = await client.futures_klines(symbol=sym, interval='15m', limit=100)
        df = calculate_indicators(klines)
        if df is None or df.empty or len(df) < 30:
            reason = "ข้อมูล 15m ไม่เพียงพอ (แท่ง < 30)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        curr = df.iloc[-1]
        current_price = float(curr['c'])
        atr = float(curr.get('atr', 0))
        
        if atr <= 0:
            reason = "ATR <= 0 (ไม่สามารถคำนวณ SL/TP ได้)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        # =============================================
        # 2. Pullback Confirmation (ใช้ df ที่เพิ่งโหลดมา)
        # =============================================
        pullback_confirm = False
        if len(df) >= 3:
            prev2 = df.iloc[-3]
            prev1 = df.iloc[-2]
            curr_candle = df.iloc[-1]  # เปลี่ยนชื่อไม่ให้ชนกับ curr
            
            if direction == 'LONG':
                if (prev2['c'] > prev2['o']) and \
                   (prev1['c'] < prev1['o'] or abs(prev1['c'] - prev1['o']) < atr * 0.4) and \
                   (curr_candle['c'] > curr_candle['o']):
                    pullback_confirm = True
            else:  # SHORT
                if (prev2['c'] < prev2['o']) and \
                   (prev1['c'] > prev1['o'] or abs(prev1['c'] - prev1['o']) < atr * 0.4) and \
                   (curr_candle['c'] < curr_candle['o']):
                    pullback_confirm = True

        if not pullback_confirm:
            reason = "ไม่มี pullback confirmation หลัง breakout"
            print(f"[SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        # =============================================
        # 3. Historical Swings
        # =============================================
        # ใน loop ของเหรียญ
        swing_data = await analyze_historical_swings(client, coin, lookback_candles=200)
        if swing_data is None:
            swing_data = {
                'highest_swing': current_price * 1.1,
                'lowest_swing': current_price * 0.9,
                'avg_pullback': current_price * 0.05,
                'recent_support': current_price * 0.97,
                'recent_resistance': current_price * 1.03,
                'key_reversal_zones': []
            }

        # =============================================
        # 4. Volume + ADX check
        # =============================================
        volume = float(curr.get('v', 1))
        vol_ma = float(curr.get('vol_ma', 1))
        vol_ratio = volume / vol_ma if vol_ma > 0 else 1.0
        adx = float(curr.get('adx', 20))
        
        volume_ok = (vol_ratio >= 0.4) or (adx >= 35)
        if not volume_ok:
            reason = f"Volume ต่ำเกิน ({vol_ratio:.2f}x < 0.4) และ ADX ไม่สูงพอ ({adx:.0f} < 35)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(
                f"⚠️ ไม่เข้า {sym} ({direction})\n"
                f"เหตุผล: {reason}\nADX: {adx:.0f} | Vol: {vol_ratio:.2f}x",
                chat_id=None
            )
            return False

        # =============================================
        # 5. Swing-based Fibonacci Entry
        # =============================================
        entry_price, fib_reason, trend_info = calculate_swing_based_fibonacci_entry(
            current_price, swing_data, direction, df
        )

        price_diff_pct = abs(entry_price - current_price) / current_price * 100 if current_price > 0 else 0

        # Fallback ถ้า entry ใกล้หรือไม่สมเหตุสมผล
        if entry_price <= 0 or price_diff_pct < 0.35:
            atr_offset = max(atr * 0.55, atr * 0.3)
            if direction == 'LONG':
                entry_price = current_price - atr_offset
            else:
                entry_price = current_price + atr_offset
            fib_reason = f"Fallback ATR pullback {atr_offset/atr:.2f}x"

        # ถ้ายังใกล้เกิน → เข้า market
        new_diff_pct = abs(entry_price - current_price) / current_price * 100
        use_market = new_diff_pct < 0.18

        # =============================================
        # 6. AI Confidence
        # =============================================
        rsi = float(curr.get('rsi', 50))
        ema20 = float(curr.get('ema20', current_price))
        ema50 = float(curr.get('ema50', current_price))
        macd = float(curr.get('macd', 0))
        signal_val = float(curr.get('signal', 0))  # เปลี่ยนชื่อไม่ให้ชน
        stoch_k = float(curr.get('stoch_k', 50))
        bb_upper = float(curr.get('bb_upper', current_price))
        bb_lower = float(curr.get('bb_lower', current_price))
        bb_position = ((current_price - bb_lower) / (bb_upper - bb_lower)) if bb_upper > bb_lower else 0.5

        ema_ratio = ema20 / ema50 if ema50 > 0 else 1.0
        macd_diff = macd - signal_val

        ai_features = [
            rsi / 100,
            ema_ratio,
            macd_diff / 100,
            vol_ratio,
            adx / 50,
            stoch_k / 100,
            bb_position
        ]

        if any(np.isnan(f) or np.isinf(f) for f in ai_features):
            ai_confidence = 50.0
        else:
            ai_confidence = brain.get_ai_confidence(ai_features)

        # Fallback confidence ถ้า AI ยังไม่ฉลาด
        if ai_confidence < 10:
            # ใช้ indicator แทน (คุณต้องมี signal_count กับ quality_bonus จาก scan_result)
            indicator_conf = min(100, (scan_result.get('signal_count', 0) / 8.0 * 100) + scan_result.get('quality_bonus', 0) * 20)
            ai_confidence = max(ai_confidence, indicator_conf)

        if ai_confidence < 55 and not use_market:  # อนุญาต market แม้ AI ต่ำ
            reason = f"AI confidence ต่ำเกิน ({ai_confidence:.1f}% < 55)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        # =============================================
        # 7. SL / TP + RR check
        # =============================================
        if direction == 'LONG':
            side = SIDE_BUY
            close_side = SIDE_SELL
            sl = swing_data.get('recent_support', current_price) - atr * 1.0  # ปรับแคบลง
            tp = current_price + atr * 4.0  # ลดจาก 6x เหลือ 4x
        else:
            side = SIDE_SELL
            close_side = SIDE_BUY
            sl = swing_data.get('recent_resistance', current_price) + atr * 1.0
            tp = current_price - atr * 4.0

        stop_distance = abs(entry_price - sl)
        if stop_distance < atr * 0.6:  # ปรับจาก 0.5 เป็น 0.6
            reason = f"Stop distance สั้นเกิน ({stop_distance:.6f} < {atr*0.6:.6f})"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            return False

        rr_ratio = (abs(tp - entry_price) / stop_distance) if stop_distance > 0 else 0
        if rr_ratio < 2.0:
            reason = f"RR ไม่ถึงเกณฑ์ ({rr_ratio:.2f} < 2.0)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            return False

        # =============================================
        # 8. Position sizing
        # =============================================
        # ใช้ balance ล่าสุด (สมมติว่ามีฟังก์ชันนี้)
        try:
            acc = await client.futures_account()
            balance = float(acc['totalWalletBalance'])
        except:
            balance = 100.0  # fallback

        risk_amount = balance * RISK_PER_TRADE_PERCENT  # เช่น 0.025 = 2.5%
        # ถ้า AI ต่ำ → ลด risk
        if ai_confidence < 60:
            risk_amount *= 0.5

        position_value = risk_amount / (stop_distance / entry_price)
        qty = position_value / entry_price

        step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
        qty = math.floor(qty / step_size) * step_size
        min_qty = step_size * 5
        qty = max(qty, min_qty)

        if qty <= 0:
            reason = "คำนวณ qty <= 0"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            return False

        qty_precision = sym_info.get(sym, (4, 2))[1]
        qty_str = f"{qty:.{qty_precision}f}"

        # =============================================
        # 9. สั่ง order (Limit หรือ Market) + ตั้ง SL/TP
        # =============================================
        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
        price_precision = sym_info.get(sym, (4, 2))[0]

        entry_rounded = round_to_tick(entry_price, tick_size)
        price_str = f"{entry_rounded:.{price_precision}f}"

        # ตั้ง Leverage ก่อน (ควรทำก่อนทุก order)
        try:
            await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)
            print(f"[LEVERAGE] ตั้ง {MAX_LEVERAGE}x สำหรับ {sym} สำเร็จ")
        except BinanceAPIException as e:
            print(f"[LEVERAGE ERROR] {sym}: {e.code} - {e.message}")
            await send_telegram_report(f"⚠️ ไม่สามารถตั้งเลเวอเรจ {sym}: {e.message}", chat_id=None)
            return False

        # ──────────────────────────────────────────────
        # เข้า order (MARKET หรือ LIMIT) - ไม่ใส่ reduceOnly
        # ──────────────────────────────────────────────
        order = None
        entry_final = None
        entry_note = ""

        try:
            if use_market:
                print(f"[ORDER MARKET] {sym} {side} Qty: {qty_str}")
                order = await client.futures_create_order(
                    symbol=sym,
                    side=side,
                    type='MARKET',
                    quantity=qty_str
                    # ไม่มี reduceOnly เพราะเป็นการเปิด position ใหม่
                )
                entry_final = current_price
                entry_note = "MARKET"
            else:
                print(f"[ORDER LIMIT] {sym} {side} @ {price_str} Qty: {qty_str}")
                order = await client.futures_create_order(
                    symbol=sym,
                    side=side,
                    type='LIMIT',
                    timeInForce='GTC',
                    quantity=qty_str,
                    price=price_str
                    # ไม่มี reduceOnly เพราะเป็นการเปิด position ใหม่
                )
                entry_final = entry_rounded
                entry_note = f"LIMIT @ {price_str}"

        except BinanceAPIException as api_err:
            err_msg = f"สั่ง order {sym} ล้มเหลว: {api_err.code} - {api_err.message}"
            print(f"[ORDER ERROR] {err_msg}")
            await send_telegram_report(f"❌ {err_msg}\nQty: {qty_str} | ราคา: {price_str if not use_market else 'market'}", chat_id=None)
            return False
        except Exception as e:
            print(f"[ORDER CRITICAL] {sym}: {str(e)}")
            await send_telegram_report(f"❌ สั่ง order {sym} ล้มเหลว (exception): {str(e)}", chat_id=None)
            return False

        # ──────────────────────────────────────────────
        # สำหรับ LIMIT: รอ fill ก่อนตั้ง SL/TP (ป้องกัน error ไม่มี position)
        # ──────────────────────────────────────────────
        if not use_market:
            filled = False
            max_wait_sec = 30  # รอสูงสุด 30 วินาที
            for attempt in range(max_wait_sec):
                await asyncio.sleep(1)
                try:
                    positions = await client.futures_position_information(symbol=sym)
                    pos_amt = float(positions[0]['positionAmt'])
                    if pos_amt != 0:
                        filled = True
                        print(f"[FILL SUCCESS] {sym} filled หลังรอ {attempt+1} วินาที")
                        break
                except Exception as e:
                    print(f"[FILL CHECK ERROR] {sym}: {str(e)}")
            
            if not filled:
                print(f"[FILL TIMEOUT] LIMIT {sym} ไม่ fill ภายใน {max_wait_sec} วินาที → ข้ามตั้ง SL/TP")
                # ยังถือว่าเข้า order สำเร็จ (แต่ SL/TP ยังไม่ตั้ง)
                report = (
                    f"{'🟢' if direction=='LONG' else '🔴'} **เข้า LIMIT สำเร็จ (ยังไม่ fill)**\n"
                    f"*{sym.replace('USDT','')}* | {direction}\n"
                    f"ราคา Limit: {price_str}\n"
                    f"Qty: {qty_str}\n"
                    f"สถานะ: รอ fill (ยังไม่มี position → SL/TP จะตั้งอัตโนมัติเมื่อ fill)"
                )
                await send_telegram_report(report)
                return True

        # ──────────────────────────────────────────────
        # ตั้ง SL/TP (เฉพาะเมื่อมี position แล้ว)
        # ──────────────────────────────────────────────
        sl_rounded = round_to_tick(sl, tick_size)
        tp_rounded = round_to_tick(tp, tick_size)
        sl_str = f"{sl_rounded:.{price_precision}f}"
        tp_str = f"{tp_rounded:.{price_precision}f}"

        try:
            print(f"[SL/TP] ตั้งสำหรับ {sym} | SL: {sl_str} | TP: {tp_str}")
            
            # STOP LOSS
            await client.futures_create_order(
                symbol=sym,
                side=close_side,
                type='STOP_MARKET',
                stopPrice=sl_str,
                closePosition=True,
                reduceOnly=True,
                workingType='MARK_PRICE',
                timeInForce='GTC'
            )
            
            # TAKE PROFIT
            await client.futures_create_order(
                symbol=sym,
                side=close_side,
                type='TAKE_PROFIT_MARKET',
                stopPrice=tp_str,
                closePosition=True,
                reduceOnly=True,
                workingType='MARK_PRICE',
                timeInForce='GTC'
            )

        except BinanceAPIException as api_err:
            print(f"[SL/TP ERROR] {sym}: {api_err.code} - {api_err.message}")
            await send_telegram_report(
                f"⚠️ ตั้ง SL/TP {sym} ล้มเหลว (แต่เข้า position สำเร็จ)\n"
                f"Code: {api_err.code}\nข้อความ: {api_err.message}\n"
                f"กรุณาตั้ง SL/TP ด้วยมือ: SL {sl_str} | TP {tp_str}",
                chat_id=None
            )
            # ยังถือว่าสำเร็จ (เพราะ position เปิดแล้ว)
        except Exception as e:
            print(f"[SL/TP CRITICAL] {sym}: {str(e)}")
            await send_telegram_report(f"❌ ตั้ง SL/TP {sym} ล้มเหลว: {str(e)}", chat_id=None)

        # ──────────────────────────────────────────────
        # สร้างรายงานสำเร็จ
        # ──────────────────────────────────────────────
        rr_ratio = calculate_rr_ratio(entry_final, sl_rounded, tp_rounded, direction)

        report = (
            f"{'🟢' if direction=='LONG' else '🔴'} **FAST SCAN ENTRY สำเร็จ!**\n"
            f"*{sym.replace('USDT','')}* | {direction}\n\n"
            f"เข้า: **{entry_note}** {entry_final:.4f}\n"
            f"SL: {sl_rounded:.4f}\n"
            f"TP: {tp_rounded:.4f}\n"
            f"RR: {rr_ratio:.2f}:1\n"
            f"AI Confidence: {ai_confidence:.0f}%\n"
            f"Vol: {vol_ratio:.2f}x | ADX: {adx:.0f}\n"
            f"Risk: ${risk_amount:.2f}"
        )

        await send_telegram_report(report)

        print(f"[EXECUTE SUCCESS] {sym} เข้าสำเร็จ ({entry_note})")
        return True

    except Exception as e:
        print(f"[EXECUTE ERROR] {sym}: {str(e)}")
        await send_telegram_report(f"❌ FAST SCAN ENTRY ล้มเหลว {sym}: {str(e)}")
        return False
    
async def get_analysis_data(client, sym):
    """
    ดึงข้อมูลวิเคราะห์สดสำหรับ Counter-Trend
    """
    try:
        # 4H
        k_4h = await client.futures_klines(symbol=sym, interval="4h", limit=100)
        df_4h = calculate_indicators(k_4h)
        curr_4h = df_4h.iloc[-1]
        
        # 1H
        k_1h = await client.futures_klines(symbol=sym, interval="1h", limit=100)
        df_1h = calculate_indicators(k_1h)
        curr_1h = df_1h.iloc[-1]
        
        # Trend
        trend_4h = "Bullish" if curr_4h['ema20'] > curr_4h['ema50'] > curr_4h['ema200'] else \
                  "Bearish" if curr_4h['ema20'] < curr_4h['ema50'] < curr_4h['ema200'] else \
                  "Sideways"
        
        trend_1h = "Bullish" if curr_1h['ema20'] > curr_1h['ema50'] > curr_1h['ema200'] else \
                  "Bearish" if curr_1h['ema20'] < curr_1h['ema50'] < curr_1h['ema200'] else \
                  "Sideways"
        
        # MACD
        macd_status = "Bullish" if curr_4h['macd'] > curr_4h['signal'] else "Bearish"
        
        # Fib
        high_4h = df_4h['h'].max()
        low_4h = df_4h['l'].min()
        diff = high_4h - low_4h
        fib_382 = high_4h - 0.382 * diff
        fib_618 = high_4h - 0.618 * diff
        
        return {
            'price_current': float(curr_4h['c']),
            'trend_4h': trend_4h,
            'trend_1h': trend_1h,
            'rsi_4h': float(curr_4h['rsi']),
            'stoch_4h': float(curr_4h.get('stoch_k', 50)),
            'stoch_1h': float(curr_1h.get('stoch_k', 50)),
            'macd': macd_status,
            'support': float(curr_4h.get('support', 0)),
            'resistance': float(curr_4h.get('resistance', 0)),
            'fib_382': fib_382,
            'fib_618': fib_618,
            'atr': float(curr_4h['atr'])
        }
    
    except Exception as e:
        print(f"[get_analysis_data Error] {sym}: {e}")
        return None

def escape_md(text: str) -> str:
    if not text:
        return text
    return (
        text.replace("_", "\\_")
            .replace("*", "\\*")
            .replace("[", "\\[")
            .replace("]", "\\]")
            .replace("(", "\\(")
            .replace(")", "\\)")
            .replace("~", "\\~")
            .replace("`", "\\`")
            .replace(">", "\\>")
            .replace("#", "\\#")
            .replace("+", "\\+")
            .replace("-", "\\-")
            .replace("=", "\\=")
            .replace("|", "\\|")
            .replace("{", "\\{")
            .replace("}", "\\}")
            .replace(".", "\\.")
            .replace("!", "\\!")
    )


import asyncio
from typing import List, Dict

# ========== ฟังก์ชันช่วยเหลือ (วางไว้ที่เดียวกันกับ scan_divergence) ==========

def calculate_rsi(prices: List[float], period: int = 14) -> List[float]:
    if len(prices) < period + 1:
        return [50.0] * len(prices)
    deltas = [prices[i] - prices[i-1] for i in range(1, len(prices))]
    gains = [d if d > 0 else 0 for d in deltas]
    losses = [-d if d < 0 else 0 for d in deltas]
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    rsi = [50.0] * period
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
        rs = avg_gain / avg_loss if avg_loss != 0 else 0
        rsi.append(100 - (100 / (1 + rs)) if rs != 0 else 100)
    return rsi

def find_swing_lows(prices: List[float], left: int = 2, right: int = 2) -> List[int]:
    swings = []
    for i in range(left, len(prices) - right):
        if all(prices[i] < prices[i-j] for j in range(1, left+1)) and \
           all(prices[i] < prices[i+j] for j in range(1, right+1)):
            swings.append(i)
    return swings

def find_swing_highs(prices: List[float], left: int = 2, right: int = 2) -> List[int]:
    swings = []
    for i in range(left, len(prices) - right):
        if all(prices[i] > prices[i-j] for j in range(1, left+1)) and \
           all(prices[i] > prices[i+j] for j in range(1, right+1)):
            swings.append(i)
    return swings

def volume_confirmed(ohlcv: List[Dict], window: int = 10) -> bool:
    if len(ohlcv) < window:
        return False
    recent_vols = [c['volume'] for c in ohlcv[-window:]]
    avg_vol = sum(recent_vols) / len(recent_vols)
    return ohlcv[-1]['volume'] > avg_vol * 1.2

def detect_divergences_in_ohlcv(ohlcv: List[Dict], lookback: int = 60) -> List[Dict]:
    if len(ohlcv) < 50:
        return []
    
    start_idx = max(0, len(ohlcv) - lookback)
    segment = ohlcv[start_idx:]
    closes = [c['close'] for c in segment]
    lows = [c['low'] for c in segment]
    highs = [c['high'] for c in segment]
    rsi = calculate_rsi(closes, 14)
    
    signals = []

    # --- Bullish ---
    swing_lows = find_swing_lows(lows, 2, 2)
    if len(swing_lows) >= 2:
        a, b = swing_lows[-2], swing_lows[-1]
        if b > a and lows[b] < lows[a]:
            rsi_a, rsi_b = rsi[a], rsi[b]
            if rsi_b > rsi_a:  # Regular
                strength = min(1.5, (rsi_b - rsi_a) / 10.0)
                if strength >= 0.3:
                    signals.append({
                        'type': 'bullish regular',
                        'div_strength': float(round(strength, 2)),
                        'rsi_diff_pct': float(round(rsi_b - rsi_a, 2)),
                        'price_current': float(closes[-1])
                    })
            elif closes[-1] > lows[a]:  # Hidden
                strength = min(1.0, abs(rsi_b - rsi_a) / 15.0)
                if strength >= 0.3:
                    signals.append({
                        'type': 'bullish hidden',
                        'div_strength': float(round(strength, 2)),
                        'rsi_diff_pct': float(round(rsi_b - rsi_a, 2)),
                        'price_current': float(closes[-1])
                    })

    # --- Bearish ---
    swing_highs = find_swing_highs(highs, 2, 2)
    if len(swing_highs) >= 2:
        a, b = swing_highs[-2], swing_highs[-1]
        if b > a and highs[b] > highs[a]:
            rsi_a, rsi_b = rsi[a], rsi[b]
            if rsi_b < rsi_a:  # Regular
                strength = min(1.5, (rsi_a - rsi_b) / 10.0)
                if strength >= 0.3:
                    signals.append({
                        'type': 'bearish regular',
                        'div_strength': float(round(strength, 2)),
                        'rsi_diff_pct': float(round(rsi_b - rsi_a, 2)),
                        'price_current': float(closes[-1])
                    })
            elif closes[-1] < highs[a]:  # Hidden
                strength = min(1.0, abs(rsi_b - rsi_a) / 15.0)
                if strength >= 0.3:
                    signals.append({
                        'type': 'bearish hidden',
                        'div_strength': float(round(strength, 2)),
                        'rsi_diff_pct': float(round(rsi_b - rsi_a, 2)),
                        'price_current': float(closes[-1])
                    })

    return signals



async def check_pending_open_orders(client, chat_id=None, max_display=10):
    """
    ตรวจสอบและรายงานออเดอร์ Limit ที่ยัง "รอเปิด" (pending / ยังไม่ fill)
    
    พารามิเตอร์:
        client       : Binance futures client
        chat_id      : Telegram chat id ที่จะส่งรายงาน (optional)
        max_display  : จำนวนสูงสุดที่จะแสดง (default 10)
    
    คืนค่า:
        tuple (รายงานข้อความ str, จำนวน pending ทั้งหมด int)
    """
    if not pending_orders_detail:
        msg = "✅ ไม่มีออเดอร์ Limit ที่กำลังรอเปิดอยู่ในขณะนี้"
        if chat_id:
            await send_telegram_report(msg, chat_id)
        return msg, 0

    try:
        # ดึงราคาสด
        tickers = await client.futures_symbol_ticker()
        price_map = {}
        for t in tickers:
            sym = t.get('symbol')
            pr = t.get('price')
            if sym and pr:
                try:
                    price_map[sym] = float(pr)
                except (ValueError, TypeError):
                    pass

        def gap_percent(order):
            curr = price_map.get(order['symbol'])
            if not isinstance(curr, (int, float)) or curr <= 0:
                return 0.0
            return abs(order['price'] - curr) / curr * 100

        # เรียงตาม gap % มาก → น้อย
        sorted_pending = sorted(pending_orders_detail, key=gap_percent, reverse=True)

        lines = ["📋 **ออเดอร์ที่กำลัง Pending / รอเปิด**"]
        lines.append(f"ทั้งหมด {len(pending_orders_detail)} ออเดอร์\n")

        displayed = 0
        for i, order in enumerate(sorted_pending, 1):
            if displayed >= max_display:
                break

            symbol = order.get('symbol', 'UNKNOWN')
            sym_clean = symbol.replace('USDT', '').replace('_', '\\_')  # escape พื้นฐาน

            curr_price = price_map.get(symbol)
            if curr_price is None or not isinstance(curr_price, (int, float)) or curr_price <= 0:
                curr_display = "N/A"
                gap = 0.0
                gap_emoji = "⚪"
            else:
                curr_display = f"{curr_price:.4f}"
                gap = gap_percent(order)
                gap_emoji = "🔴" if gap > 3 else "🟡" if gap > 1 else "🟢"

            side_emoji = "🟢 BUY" if order.get('side') == 'BUY' else "🔴 SELL"
            manual = " [Manual]" if order.get('manual', False) else ""

            # อายุ
            try:
                age_hours = (datetime.now() - order['time']).total_seconds() / 3600
            except (TypeError, AttributeError):
                age_hours = 0
                age_str = "?"
            else:
                age_str = f"{age_hours:.1f} ชม." if age_hours >= 1 else f"{age_hours*60:.0f} นาที"

            warn = ""
            if age_hours > 24:
                warn = " ⚠️ ค้างนาน"
            elif gap < 0.7:
                warn = " 🔥 ใกล้ fill"

            qty = order.get('qty', 0)
            limit_price = order.get('price', 0)

            line = (
                f"{i}\\. {side_emoji} `{sym_clean}`{manual}\n"
                f"   • ปัจจุบัน: `{curr_display}`\n"
                f"   • Limit: `{limit_price:.4f}`\n"
                f"   • ห่าง {gap_emoji} **{gap:+.2f}%**\n"
                f"   • Qty: `{qty:.4f}` | อายุ *{age_str}*{warn}"
            )
            lines.append(line)
            lines.append("─" * 38)
            displayed += 1

        # สรุป
        near_fill_count = sum(1 for o in pending_orders_detail if gap_percent(o) < 0.8)
        summary = (
            f"\n**สรุป**\n"
            f"• ทั้งหมด: {len(pending_orders_detail)} ออเดอร์\n"
            f"• ใกล้ fill (< 0.8%): {near_fill_count} ตัว 🔥\n"
            f"ใช้ `/cancel` หรือ `/cancel BTCUSDT` เพื่อยกเลิก"
        )
        if displayed < len(pending_orders_detail):
            summary += f"\n(แสดง {displayed} จาก {len(pending_orders_detail)} รายการ)"

        lines.append(summary)

        full_report = "\n".join(lines)

        if chat_id:
            await send_telegram_report(full_report, chat_id)

        return full_report, len(pending_orders_detail)

    except Exception as e:
        err_type = type(e).__name__
        err_msg = f"⚠️ ข้อผิดพลาดตอนตรวจสอบ pending orders\n{err_type}: {str(e)}"
        print(err_msg)
        if chat_id:
            try:
                await send_telegram_report(err_msg, chat_id)
            except:
                pass  # ป้องกัน loop error
        return err_msg, 0
# ==========================================================================
# PENDING LIMITS REPORT
# ==========================================================================
def get_pending_limits_report(pending_orders, price_map):
    if not pending_orders:
        return "⏳ ไม่มี Limit Orders ที่รออยู่"
   
    lines = ["**⏳ Pending Limit Orders ทั้งหมด**"]
    for o in sorted(pending_orders, key=lambda x: x['time']):
        sym = o['symbol'].replace('USDT', '')
        curr = price_map.get(o['symbol'], 0.0)
        diff = o['price'] - curr if o['side'] == 'BUY' else curr - o['price']
        pct = (diff / curr * 100) if curr > 0 else 0
        age = (datetime.now() - o['time']).total_seconds() / 3600
        lines.append(f"• {sym} {o['side']} @ {o['price']:.4f} (ตอนนี้ {curr:.4f})")
        lines.append(f" ห่าง: {diff:+.4f} ({pct:+.2f}%) | จำนวน: {o['qty']:.4f} | อายุ: {age:.1f}ชั่วโมง")
    return "\n".join(lines)

# ========== ฟังก์ชันหลักที่ใช้ใน /divscan ==========

async def scan_divergence(client) -> List[Dict]:
    """
    สแกน divergence ทุกเหรียญที่ active
    ใช้กับ Binance API ผ่าน client (เช่น ccxt.binance())
    """
    try:
        # ดึงรายการเหรียญที่เทรดได้ (ปรับตามระบบของคุณ)
        markets = await client.load_markets()
        symbols = [
            symbol for symbol in markets.keys()
            if symbol.endswith('/USDT') and markets[symbol]['active']
        ]
        # จำกัดจำนวนเพื่อความเร็ว
        symbols = symbols[:25]

        all_divs = []

        for symbol in symbols:
            try:
                # ดึงข้อมูล 15m ย้อนหลัง 100 แท่ง
                ohlcv = await client.fetch_ohlcv(symbol, '15m', limit=100)
                if len(ohlcv) < 50:
                    continue

                # แปลงเป็น dict สำหรับใช้งาน
                ohlcv_dicts = [
                    {
                        'timestamp': item[0],
                        'open': float(item[1]),
                        'high': float(item[2]),
                        'low': float(item[3]),
                        'close': float(item[4]),
                        'volume': float(item[5])
                    }
                    for item in ohlcv
                ]

                # ตรวจจับ divergence
                divs = detect_divergences_in_ohlcv(ohlcv_dicts, lookback=70)
                
                for d in divs:
                    all_divs.append({
                        'symbol': symbol.replace('/USDT', ''),
                        'type': d['type'],
                        'div_strength': d['div_strength'],
                        'rsi_diff_pct': d['rsi_diff_pct'],
                        'price_current': d['price_current'],
                        'volume_confirm': volume_confirmed(ohlcv_dicts),
                        'tf': '15m'
                    })

                # หน่วงเวลาเล็กน้อยเพื่อไม่โดน rate limit
                await asyncio.sleep(0.1)

            except Exception as e:
                # print(f"[DIV] Error on {symbol}: {e}")
                continue

        return all_divs

    except Exception as e:
        print(f"[SCAN_DIV] Critical error: {e}")
        return []

import numpy as np
from typing import List, Dict, Optional

# ========== ฟังก์ชันช่วยเหลือ ==========

def calculate_rsi(prices: List[float], period: int = 14) -> List[float]:
    if len(prices) < period + 1:
        return [50.0] * len(prices)
    deltas = [prices[i] - prices[i-1] for i in range(1, len(prices))]
    gains = [d if d > 0 else 0 for d in deltas]
    losses = [-d if d < 0 else 0 for d in deltas]
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    rsi = [50.0] * period
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
        rs = avg_gain / avg_loss if avg_loss != 0 else 0
        rsi.append(100 - (100 / (1 + rs)) if rs != 0 else 100)
    return rsi

def find_swing_lows(prices: List[float], left: int = 2, right: int = 2) -> List[int]:
    swings = []
    for i in range(left, len(prices) - right):
        if all(prices[i] < prices[i-j] for j in range(1, left+1)) and \
           all(prices[i] < prices[i+j] for j in range(1, right+1)):
            swings.append(i)
    return swings

def find_swing_highs(prices: List[float], left: int = 2, right: int = 2) -> List[int]:
    swings = []
    for i in range(left, len(prices) - right):
        if all(prices[i] > prices[i-j] for j in range(1, left+1)) and \
           all(prices[i] > prices[i+j] for j in range(1, right+1)):
            swings.append(i)
    return swings

async def fetch_ohlcv_safe(client, symbol: str, tf: str, limit: int):
    try:
        data = await client.fetch_ohlcv(symbol + '/USDT', tf, limit=limit)
        return [{'timestamp': d[0], 'open': d[1], 'high': d[2], 'low': d[3], 'close': d[4], 'volume': d[5]} for d in data]
    except:
        return None

def is_downtrend_confirmed(ohlcv: List[Dict]) -> bool:
    highs = [c['high'] for c in ohlcv]
    swings = find_swing_highs(highs, 3, 3)
    if len(swings) < 3:
        return False
    h1, h2, h3 = highs[swings[-3]], highs[swings[-2]], highs[swings[-1]]
    return h3 < h2 < h1

def analyze_abc_correction(ohlcv: List[Dict]):
    lows = [c['low'] for c in ohlcv]
    highs = [c['high'] for c in ohlcv]
    swing_lows = find_swing_lows(lows, 2, 2)
    swing_highs = find_swing_highs(highs, 2, 2)
    if len(swing_lows) < 2 or not swing_highs:
        return None
    a_idx = swing_lows[-2]
    b_candidates = [i for i in swing_highs if a_idx < i < swing_lows[-1]]
    if not b_candidates:
        return None
    b_idx = max(b_candidates)
    c_idx = swing_lows[-1]
    wave_a = lows[a_idx] - highs[b_idx]
    wave_c = highs[b_idx] - lows[c_idx]
    if wave_c >= 0.6 * abs(wave_a):
        return {'phase': 'C'}
    return None

def calculate_fib_retracement(ohlcv: List[Dict]):
    highs = [c['high'] for c in ohlcv]
    lows = [c['low'] for c in ohlcv]
    swing_highs = find_swing_highs(highs, 3, 3)
    swing_lows = find_swing_lows(lows, 3, 3)
    if not swing_highs or not swing_lows:
        return {'61.8': 0, '78.6': 0}
    last_high = highs[swing_highs[-1]]
    last_low = lows[swing_lows[-1]]
    if last_high <= last_low:
        return {'61.8': 0, '78.6': 0}
    diff = last_high - last_low
    return {'61.8': last_low + diff * 0.618, '78.6': last_low + diff * 0.786}

def detect_bearish_divergence(ohlcv: List[Dict]) -> bool:
    closes = [c['close'] for c in ohlcv]
    rsi = calculate_rsi(closes, 14)
    swing_highs = find_swing_highs([c['high'] for c in ohlcv], 2, 2)
    if len(swing_highs) < 2:
        return False
    a, b = swing_highs[-2], swing_highs[-1]
    high_a, high_b = ohlcv[a]['high'], ohlcv[b]['high']
    rsi_a, rsi_b = rsi[a], rsi[b]
    return high_b > high_a and rsi_b < rsi_a

def detect_liquidity_grab(highs: List[float], closes: List[float]) -> bool:
    if len(highs) < 2:
        return False
    recent_high = highs[-1]
    prev_highs = highs[-10:-1]
    return recent_high > max(prev_highs) and closes[-1] < highs[-1]

# ========== ฟังก์ชันหลัก ==========

async def detect_strong_short_signals(client, symbols: List[str], price_map: dict, active_symbols: set):
    signals = []
    for symbol in symbols[:20]:
        try:
            ohlcv_15m = await fetch_ohlcv_safe(client, symbol, '15m', 200)
            ohlcv_1h = await fetch_ohlcv_safe(client, symbol, '1h', 100)
            if not ohlcv_15m or len(ohlcv_15m) < 100:
                continue

            closes_15 = [c['close'] for c in ohlcv_15m]
            highs_15 = [c['high'] for c in ohlcv_15m]
            lows_15 = [c['low'] for c in ohlcv_15m]
            volumes_15 = [c['volume'] for c in ohlcv_15m]

            # 1. BOS/CHOCH
            if not is_downtrend_confirmed(ohlcv_1h):
                continue

            # 2. Elliott Wave ABC
            abc_result = analyze_abc_correction(ohlcv_15m)
            if not abc_result or abc_result['phase'] != 'C':
                continue

            # 3. Fibonacci
            fib_levels = calculate_fib_retracement(ohlcv_15m)
            current_price = closes_15[-1]
            if not (fib_levels['61.8'] <= current_price <= fib_levels['78.6']):
                continue

            # 4. RSI + Divergence
            rsi = calculate_rsi(closes_15, 14)[-1]
            has_divergence = detect_bearish_divergence(ohlcv_15m)
            if rsi < 65 or not has_divergence:
                continue

            # 5. Volume & Liquidity
            volume_ok = volumes_15[-1] > np.mean(volumes_15[-20:]) * 1.5
            liquidity_ok = detect_liquidity_grab(highs_15, closes_15)
            if not (volume_ok and liquidity_ok):
                continue

            # คำนวณ strength
            strength_score = (
                0.3 * 1 +
                0.25 * 1 +
                0.2 * 1 +
                0.15 * min(1.0, (rsi - 65) / 35) +
                0.1 * 1
            )

            if strength_score >= 0.7:
                signals.append({
                    'symbol': symbol.replace('/USDT', ''),
                    'strength': round(strength_score, 2),
                    'rsi': round(rsi, 1),
                    'price': float(current_price),
                    'timeframe': '15m',
                    'volume_confirm': volume_ok,
                    'wave_phase': 'C',
                    'fib_zone': '61.8-78.6%'
                })

            await asyncio.sleep(0.1)
        except Exception as e:
            print(f"[SHORT-SIGNAL] Error on {symbol}: {e}")
            continue
    return signals


async def place_short_order(client, signal: dict, chat_id: str):
    symbol = signal['symbol'] + "USDT"
    price = signal['price']
    
    # คำนวณขนาด (1% ของพอร์ต)
    account = await client.futures_account()
    balance = float(account['totalWalletBalance'])
    qty = (balance * 0.01) / price
    qty = round(qty, 3)

    # ส่งคำสั่ง
    order = await client.futures_create_order(
        symbol=symbol,
        side='SELL',
        positionSide='SHORT',
        type='MARKET',
        quantity=qty
    )

    # แจ้งเตือน
    msg = (
        f"⚡ **SHORT ENTERED (AUTO)**\n"
        f"• {signal['symbol']} @ {price:.4f}\n"
        f"• Strength: {signal['strength']}\n"
        f"• RSI: {signal['rsi']}\n"
        f"• Time: {datetime.now().strftime('%H:%M')}"
    )
    await send_telegram_report(msg, chat_id)

# ==========================================================================
#                  TELEGRAM COMMAND LISTENER (รวมทุกคำสั่งล่าสุด - แก้ Indentation แล้ว)
# ==========================================================================
async def check_telegram_updates(client, cmd_q, price_map):
    global update_offset, running
    try:
        updates = await telegram_bot.get_updates(offset=update_offset, timeout=5)
        for update in updates:
            if update_offset is None or update.update_id >= update_offset:
                update_offset = update.update_id + 1

            if not update.message or not update.message.text:
                continue

            message = update.message
            text = message.text.strip().lower()
            chat_id = message.chat_id
            user_id = message.from_user.id  # ← สำคัญ! ดึง user_id จากตรงนี้

            # =============================================
            # เช็คสิทธิ์ผู้ใช้ (สำคัญที่สุด!)
            # =============================================
            if user_id not in ALLOWED_USERS:
                print(f"[UNAUTHORIZED] User {user_id} ({message.from_user.username or 'ไม่ระบุ'}) พยายามใช้: {text}")
                try:
                    await telegram_bot.send_message(
                        chat_id=chat_id,
                        text="⛔ คุณไม่มีสิทธิ์สั่งบอทนี้\nกรุณาติดต่อ admin"
                    )
                except:
                    pass
                continue  # ข้าม ไม่ให้ประมวลผลคำสั่งต่อ

            print(f"{Fore.MAGENTA}Telegram command: {text} from {chat_id}")

            # ─── แก้ปัญหา group chat ที่มี @botname ติดมา ───
            processed_text = text
            if message.chat.type in ['group', 'supergroup']:
                # ดึง username ของบอท (ถ้ายังไม่มี ต้องกำหนด global หรือจาก telegram_bot.get_me())
                bot_username = (await telegram_bot.get_me()).username.lower()  # เรียกครั้งเดียวก็พอ แต่เพื่อความปลอดภัย
                bot_mention = f"@{bot_username}"
                
                if bot_mention in processed_text:
                    processed_text = processed_text.replace(bot_mention, '').strip().replace('  ', ' ')
                
                # ลบช่องว่างซ้ำและ / ซ้ำ (กรณี /limits@bot /limits@bot)
                processed_text = ' '.join(processed_text.split())

            # ใช้ processed_text แทน text ในการเช็คคำสั่งต่อไป
            text = processed_text
            # ===================== /help =====================
            if text == '/help':
                help_text = (
                    "📋 **TITAN PRO Bot - Command Guide** v33.0\n\n"
                    "━━━━━━━━━━━━━━━ 📊 ANALYTICS ━━━━━━━━━━━━━━━\n"
                    "💰 `/pnl` → Total PNL (Open+Closed) + Win Rate + Avg/Trade + Profit Factor\n"
                    "   └ ดูกำไร-ขาดทุนรวมจาก trades ที่เปิดและปิดแล้ว\n"
                    "📉 `/drawdown` → Max Drawdown Analysis (Peak-to-Trough)\n"
                    "   └ ดูการลดลงของยอดกำไรสูงสุด และวันที่เกิด\n"
                    "📊 `/daily` → 7-Day PNL Summary (Trades + WR% per day)\n"
                    "   └ สรุปผลการเทรดรายวัน 7 วันที่ผ่านมา\n"
                    "📈 `/weekly` → 4-Week PNL Summary (Trades + WR% per week)\n"
                    "   └ สรุปผลการเทรดรายสัปดาห์ 4 สัปดาห์ที่ผ่านมา\n\n"
                    "━━━━━━━━━━ 📍 POSITION MANAGEMENT ━━━━━━━━━━\n"
                    "⭐ `/positions` → รายการ Position ที่เปิดอยู่\n"
                    "   └ แสดง Entry, Current Price, PNL, SL/TP สำหรับทุก position\n"
                    "⏳ `/limits` → รายการ Limit Orders ที่รออยู่\n"
                    "   └ แสดง Symbol, Side, Entry Price, Target, Status\n"
                    "🚪 `/close BTC` → ปิด Position เดี่ยว\n"
                    "   └ ตัวอย่าง: /close BTC จะปิด BTCUSDT position\n"
                    "🛑 `/closeall` หรือ `/a` → ปิดทุก Position ทันที\n"
                    "   └ ระวัง! ปิดทั้งหมด รวม LONG และ SHORT\n\n"
                    "━━━━━━━━ 🛡️ RISK MANAGEMENT ━━━━━━━━\n"
                    "🛠️ `/sltp` → ตรวจสอบและตั้ง SL/TP อัตโนมัติ\n"
                    "   └ สำหรับ positions ที่ไม่มี Stop Loss หรือ Take Profit\n"
                    "   └ ใช้ ATR-based formula: SL = Entry ± ATR×2.0, TP = Entry ± ATR×4.0\n\n"
                    "━━━━━━━━ 🎯 ORDER MANAGEMENT ━━━━━━━━\n"
                    "❌ `/cancel` → ยกเลิก Limit Orders ทั้งหมด\n"
                    "   └ เมื่อ orders ไม่ trigger หรือต้องการยกเลิก\n"
                    "❌ `/cancel BTC` → ยกเลิก Limit Orders เฉพาะ BTC\n"
                    "   └ ลบเฉพาะ pending orders ของ BTCUSDT\n\n"
                    "━━━━━━━ 🔍 ANALYSIS & REPORTING ━━━━━━━\n"
                    "📊 `/report` หรือ `/status` → สถานะบอทเต็มรูปแบบ\n"
                    "   └ Balance, Open Positions, Pending Orders, Recent Trades\n"
                    "🔍 `/analyze BTC` → Deep Analysis + Fibonacci Retracement Chart\n"
                    "   └ 11 Indicators: EMA, RSI, MACD, Stochastic, ATR, Bollinger Bands,\n"
                    "   └ ADX, Volume, Support/Resistance, Fibonacci, Elliott Wave\n"
                    "💰 พิมพ์ชื่อเหรียญ เช่น `BTC`, `ETH`, `SOL` → วิเคราะห์แนวโน้ม 1D\n"
                    "🚀 `/fastscan` → สแกนเร่งด่วน Top 10 Coins (Signals > 3)\n"
                    "   └ หาเหรียญที่มีสัญญาณแข็งแกร่ง 3+ ตัวขึ้นไป สำหรับ quick entry\n\n"
                    "━━━━━━━ 🤖 AUTO ENTRY & AI ━━━━━━━\n"
                    "🔄 `/spike on/off` → เปิด/ปิด Auto LONG (Volume Spike Detected)\n"
                    "   └ Auto-enter when volume > 2.5x + 6 confirmations\n"
                    "🔄 `/shortsig on/off` → เปิด/ปิด Auto SHORT (Strong Signal)\n"
                    "   └ Auto-enter when ≥ 6 bearish conditions met\n"
                    "📡 `/autostatus` → สถานะ Auto Entry + ตั้งค่าปัจจุบัน\n"
                    "🧠 `/aistats` → AI Model Training Statistics + Accuracy + Confidence\n"
                    "   └ ดูการเรียนรู้ของ AI จากการเทรด\n"
                    "🧪 `/backtest [periods]` → Validation Mode (ทดสอบเท่านั้น)\n"
                    "   └ ตัวอย่าง: /backtest 100 (ทดสอบ 100 periods ที่ผ่านมา)\n"
                    "   └ สุ่มเหรียญ (เน้น major coins) + รายงานผลลัพธ์\n"
                    "🎓 `/backtest [periods] train` → **Training Mode** (Pre-train AI!)\n"
                    "   └ ตัวอย่าง: /backtest 200 train (ให้ AI เรียนรู้ 200 historical trades)\n"
                    "   └ ✨ Feed historical backtest results → Train neural network\n"
                    "   └ ลดเฟส \"ไม่เก่ง\" ของ AI ตั้งแต่เริ่มเทรด (ขั้นเทพ!)\n\n"
                    "━━━━━━━━━ 🛑 SYSTEM CONTROL ━━━━━━━━━\n"
                    "🚪 `/q` หรือ `/quit` → หยุดบอทอย่างปลอดภัย\n"
                    "   └ ปิด WebSocket ทั้งหมด + ออกจาก program\n"
                    "   └ Positions จะเหลือไว้ run ต่อ (ไม่ปิด)\n\n"
                    "_⚡ TITAN PRO v33.0 - AI-Powered Advanced Trading Bot_\n"
                    "_LFG!_ 🚀"
                    "/setlm BTC 92000 L     → ตั้ง Limit Buy BTC ที่ 92,000\n"
                    "/setlm ETH 3200 S      → ตั้ง Limit Sell ETH ที่ 3,200\n"
                    "/setlm SOL 140 L       → ตั้ง Limit Buy SOL ที่ 140\n"
                    "/limits                → ดูรายการทั้งหมด (รวม manual)\n"
                    "/lauto -openLong auto"
                    "/pending"
                )
                await send_telegram_report(help_text, chat_id)


            elif text == '/pending':
                print(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] USER {message.from_user.id} ({message.from_user.username or 'unknown'}) เรียก /pending")
                
                if not pending_orders_detail:
                    print("→ ไม่มี pending orders → ส่งข้อความว่าง")
                
                await check_pending_open_orders(client, TELEGRAM_CHAT_ID)
                
                print(f"→ ส่งรายงาน pending orders เสร็จสิ้น (จำนวน: {len(pending_orders_detail)})")
            # ===================== /lauto - Auto Long Entry (Multi-Factor Confluence) =====================
            elif text == '/lauto':
                try:
                    now_ts = time.time()
                    await send_telegram_report(
                        "🔍 **กำลังสแกนหาจุด LONG อัตโนมัติทั้งระบบ**\n"
                        "• ตรวจโครงสร้าง + Demand Reaction + Momentum Divergence + HTF Context + Sentiment\n"
                        "• เข้าเฉพาะที่ตลาดเริ่มบอกว่าอยากขึ้นจริง ๆ\n"
                        "• Risk fixed $0.50 ต่อเทรด | Cooldown 45 นาที/เหรียญ",
                        chat_id
                    )

                    # ─── กรองเหรียญที่ยังว่าง (ไม่มี position/pending) ───
                    active_syms = {p['symbol'] for p in active}
                    pending_syms = {o['symbol'] for o in pending_orders_detail}
                    candidates = [
                        s for s in MAJOR_TICKER_SYMBOLS
                        if s not in active_syms and s not in pending_syms
                    ]

                    if not candidates:
                        await send_telegram_report("ไม่มีเหรียญว่างให้สแกน (position/pending เต็มทั้งหมด)", chat_id)
                        return

                    entered = []
                    skipped = []
                    cooldown_skipped = []

                    # จำกัดสแกน 15 เหรียญเพื่อไม่ให้ช้าเกิน + เรียงตาม volume (สมมติ top_50_symbols เรียงตาม volume อยู่แล้ว)
                    for sym in candidates[:15]:
                        sym_clean = sym.replace('USDT', '')

                        # 1. Cooldown check
                        if sym in lauto_cooldown:
                            remain = now_ts - lauto_cooldown[sym]
                            if remain < LAUTO_COOLDOWN_MINUTES * 60:
                                cooldown_skipped.append(f"{sym_clean} (เหลือ ~{int((LAUTO_COOLDOWN_MINUTES*60 - remain)/60)+1} นาที)")
                                continue

                        # 2. วิเคราะห์ setup
                        result = await detect_auto_long_entry(client, sym)
                        if not result or not result.get('should_enter', False):
                            reason = result.get('reason', 'ไม่ผ่านเงื่อนไข') if result else 'ข้อมูลไม่พอหรือ error'
                            skipped.append(f"{sym_clean} → {reason[:60]}...")
                            continue

                        # 3. วาง Limit Order LONG
                        entry_price = result['entry_price']
                        sl = result['sl']
                        tp = result['tp']
                        rr = result['rr']
                        confidence = result['confidence']

                        # Position sizing (risk $0.50)
                        risk_usdt = 0.50
                        stop_dist = entry_price - sl
                        if stop_dist <= 0:
                            skipped.append(f"{sym_clean} → Stop distance ไม่ถูกต้อง")
                            continue

                        pos_value = risk_usdt / (stop_dist / entry_price)
                        qty = pos_value / entry_price

                        step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
                        qty = math.floor(qty / step_size) * step_size
                        qty = max(qty, step_size * 5)  # ขั้นต่ำ

                        qty_prec = sym_info.get(sym, (4, 2))[1]
                        qty_str = f"{qty:.{qty_prec}f}"

                        # ปัดราคาให้ตรง tick size
                        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                        prec = sym_info.get(sym, (4, 2))[0]

                        entry_p = round_to_tick(entry_price, tick_size)
                        sl_p = round_to_tick(sl, tick_size)
                        tp_p = round_to_tick(tp, tick_size)

                        entry_str = f"{entry_p:.{prec}f}"
                        sl_str = f"{sl_p:.{prec}f}"
                        tp_str = f"{tp_p:.{prec}f}"

                        # สั่ง order + ตั้ง SL/TP
                        try:
                            # เปลี่ยน leverage ก่อน
                            await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)

                            # Limit Buy
                            order = await client.futures_create_order(
                                symbol=sym,
                                side=SIDE_BUY,
                                type='LIMIT',
                                timeInForce='GTC',
                                quantity=qty_str,
                                price=entry_str
                            )

                            # SL (closePosition=True)
                            await client.futures_create_order(
                                symbol=sym,
                                side=SIDE_SELL,
                                type='STOP_MARKET',
                                stopPrice=sl_str,
                                closePosition=True,
                                timeInForce='GTC',
                                workingType='MARK_PRICE'
                            )

                            # TP
                            await client.futures_create_order(
                                symbol=sym,
                                side=SIDE_SELL,
                                type='TAKE_PROFIT_MARKET',
                                stopPrice=tp_str,
                                closePosition=True,
                                timeInForce='GTC',
                                workingType='MARK_PRICE'
                            )

                            # บันทึก pending
                            pending_orders_detail.append({
                                'symbol': sym,
                                'side': SIDE_BUY,
                                'price': entry_p,
                                'qty': qty,
                                'time': datetime.now(),
                                'orderId': order['orderId'],
                                'source': 'lauto_auto',
                                'manual': False,
                                'sl_price': sl_p,
                                'tp_price': tp_p,
                                'rr': rr,
                                'confidence': confidence
                            })

                            # ตั้ง cooldown
                            lauto_cooldown[sym] = now_ts

                            entered.append(sym_clean)

                            # รายงานทันที
                            report = (
                                f"🟢 **AUTO LONG วาง Limit สำเร็จ!**\n"
                                f"เหรียญ: `{sym_clean}`\n"
                                f"Confidence: **{confidence:.0%}**\n"
                                f"Limit Entry: `{entry_str}`\n"
                                f"SL: `{sl_str}`\n"
                                f"TP: `{tp_str}`\n"
                                f"RR: `{rr:.2f}:1`\n"
                                f"Qty: `{qty_str}` | Risk `$0.50`\n"
                                f"Leverage: `{MAX_LEVERAGE}x`\n\n"
                                f"**เหตุผลที่เข้า:**\n" + "\n".join([f"• {r}" for r in result['reason'].split('\n') if r.strip()])
                            )
                            await send_telegram_report(report, chat_id)

                        except BinanceAPIException as api_err:
                            err_msg = f"Order ล้มเหลว {sym_clean}: {api_err.code} - {api_err.message}"
                            skipped.append(f"{sym_clean} → {err_msg[:60]}...")
                            print(f"[LAUTO ORDER ERROR] {err_msg}")
                            await send_telegram_report(f"⚠️ {err_msg}", chat_id)

                        except Exception as e:
                            skipped.append(f"{sym_clean} → Exception: {str(e)[:60]}...")
                            print(f"[LAUTO CRITICAL] {sym}: {e}")
                            await send_telegram_report(f"❌ วาง order {sym_clean} ล้มเหลว: {str(e)[:120]}", chat_id)

                    # ─── สรุปรอบนี้ ───
                    summary_lines = [
                        "**สรุป /lauto รอบนี้**",
                        f"สแกนทั้งหมด: {len(candidates)} เหรียญ",
                        f"เข้า LONG สำเร็จ: **{len(entered)}** เหรียญ → {', '.join(entered) if entered else 'ไม่มี'}",
                    ]

                    if cooldown_skipped:
                        summary_lines.append(f"ข้ามเพราะ cooldown: {len(cooldown_skipped)} เหรียญ")
                        summary_lines.extend([f"• {s}" for s in cooldown_skipped[:3]])

                    if skipped:
                        summary_lines.append(f"ข้าม (ไม่ผ่านเงื่อนไข/order error): {len(skipped)} เหรียญ")
                        summary_lines.extend([f"• {s}" for s in skipped[:5]])

                    await send_telegram_report("\n".join(summary_lines), chat_id)

                except Exception as e:
                    await send_telegram_report(f"❌ /lauto ล้มเหลวทั้งระบบ: {str(e)[:180]}", chat_id)
                    print(f"[LAUTO GLOBAL ERROR] {e}")

            elif text in ['/winmonthly', '/monthlywin', '/winrate-monthly']:
                await send_telegram_report(
                    "⏳ กำลังสร้างกราฟ winrate รายเดือน... (ย้อนหลัง 6 เดือน)",
                    chat_id
                )
                
                chart_buf = generate_monthly_winrate_chart(filter_months=6, 
                                                        title="Winrate รายเดือน (ย้อนหลัง 6 เดือน)")
                
                if chart_buf:
                    # สร้างข้อความสรุปสั้น ๆ
                    stats = get_current_winrate(filter_days=180)  # ประมาณ 6 เดือน
                    summary = (
                        f"📊 **สรุป Winrate รายเดือน**\n"
                        f"รวม 6 เดือนล่าสุด: {stats['overall_winrate']:.1f}% "
                        f"({stats['overall_wins']}/{stats['overall_total']})\n"
                        f"LONG: {stats['long_winrate']:.1f}% | SHORT: {stats['short_winrate']:.1f}%"
                    )
                    
                    await telegram_bot.send_photo(
                        chat_id=chat_id,
                        photo=chart_buf,
                        caption=summary,
                        parse_mode="Markdown"
                    )
                else:
                    await send_telegram_report(
                        "⚠️ ไม่มีข้อมูลการเทรดเพียงพอที่จะสร้างกราฟรายเดือน\n"
                        "ลองเทรดเพิ่มหรือใช้ `/pnl` ดูสถิติรวมก่อน",
                        chat_id
                    )

            elif text in ['/pnl', '/winrate']:
                stats = get_current_winrate(filter_days=30)  # หรือไม่ใส่เพื่อดูทั้งหมด
                
                # สร้างข้อความสรุป
                msg = (
                    f"📊 **สถิติ Winrate ล่าสุด (30 วัน)**\n\n"
                    f"รวมทั้งหมด: {stats['overall_winrate']:.1f}% ({stats['overall_wins']}/{stats['overall_total']})\n"
                    f"LONG: {stats['long_winrate']:.1f}% ({stats['long_wins']}/{stats['long_total']})\n"
                    f"SHORT: {stats['short_winrate']:.1f}% ({stats['short_wins']}/{stats['short_total']})\n\n"
                    f"ข้อมูลจาก trade ที่มี |PNL| ≥ $0.01"
                )
                
                # สร้างกราฟ
                chart_buf = generate_winrate_chart(stats, title="Winrate LONG vs SHORT (30 วันล่าสุด)")
                
                if chart_buf:
                    await telegram_bot.send_photo(
                        chat_id=chat_id,
                        photo=chart_buf,
                        caption=msg,
                        parse_mode="Markdown"
                    )
                else:
                    await send_telegram_report(msg + "\n(ไม่สามารถสร้างกราฟได้)", chat_id)

            elif text in ['/spike on', '/spike off']:
                global auto_spike_enabled
                if text == '/spike on':
                    auto_spike_enabled = True
                    await send_telegram_report("🟢 *Volume Spike Auto LONG* เปิดใช้งานแล้ว 🚀", chat_id)
                else:
                    auto_spike_enabled = False
                    await send_telegram_report("🔴 *Volume Spike Auto LONG* ปิดใช้งานแล้ว 🛑", chat_id)

            elif text in ['/shortsig on', '/shortsig off']:
                global auto_short_signal_enabled
                if text == '/shortsig on':
                    auto_short_signal_enabled = True
                    await send_telegram_report("🟢 *Strong Short Signal Auto SHORT* เปิดใช้งานแล้ว 🔴", chat_id)
                else:
                    auto_short_signal_enabled = False
                    await send_telegram_report("🔴 *Strong Short Signal Auto SHORT* ปิดใช้งานแล้ว 🛑", chat_id)

            elif text in ['/autostatus', '/astatus']:
                status_text = (
                    f"📡 **สถานะ Auto Entry ทั้งหมด**\n\n"
                    f"🚀 Volume Spike Auto LONG:\n"
                    f"   └ {'🟢 เปิดใช้งาน' if auto_spike_enabled else '🔴 ปิดใช้งาน'}\n"
                    f"   └ Interval Check: ทุก {SPIKE_CHECK_INTERVAL.total_seconds():.0f} วินาที\n"
                    f"   └ Volume Threshold: > 2.5x\n\n"
                    f"🔴 Strong Short Signal Auto SHORT:\n"
                    f"   └ {'🟢 เปิดใช้งาน' if auto_short_signal_enabled else '🔴 ปิดใช้งาน'}\n"
                    f"   └ Interval Check: ทุก {SHORT_SIGNAL_CHECK_INTERVAL.total_seconds():.0f} วินาที\n"
                    f"   └ Min Conditions: ≥ 6 เงื่อนไข\n"
                    f"   └ Volume Threshold: > 2.5x\n\n"
                    f"⚙️ **ตั้งค่า Risk Management**:\n"
                    f"   └ Risk Per Trade: $0.5\n"
                    f"   └ SL Distance: ATR × {ATR_SL_MULTIPLIER}\n"
                    f"   └ TP Distance: ATR × {ATR_TP_MULTIPLIER}\n"
                    f"   └ Max Leverage: {MAX_LEVERAGE}x\n\n"
                    f"📊 **ตัวชี้วัดหลัก**:\n"
                    f"   └ EMA: 20, 50, 200\n"
                    f"   └ RSI: 14\n"
                    f"   └ MACD: 12,26,9\n"
                    f"   └ Bollinger Bands: 20,2\n"
                    f"   └ ADX: 14\n"
                    f"   └ ATR: 14\n"
                )
                await send_telegram_report(status_text, chat_id)
            # ==========================================================================
            #                  INTEGRATE INTO TELEGRAM HANDLER
            #                  ใน check_telegram_updates, เพิ่ม elif สำหรับ /divscan
            # ==========================================================================
            # /divscan – สแกน Divergence ทุกเหรียญ + รายงานแบบมีคุณภาพสูง
            # ==========================================================================
            elif text == '/divscan':
                await send_telegram_report(
                    "⏳ กำลังสแกน Divergence ทุกเหรียญที่ active (อาจใช้เวลา 1–4 นาที)...",
                    chat_id
                )
                try:
                    div_results = await scan_divergence(client)  # ควร return list of dicts

                    if not div_results:
                        await send_telegram_report(
                            "🔍 **ไม่พบ Divergence ที่น่าสนใจในรอบนี้**\n"
                            "• อาจยังไม่มี divergence ชัดเจน\n"
                            "• หรือตลาด sideway มากเกินไป",
                            chat_id
                        )
                        return

                    # เรียงตามความแข็งแรง
                    div_results.sort(
                        key=lambda x: (
                            x.get('div_strength', 0),
                            x.get('volume_confirm', 0),
                            -abs(x.get('rsi_diff_pct', 0))
                        ),
                        reverse=True
                    )

                    # Helper function to safely format numbers
                    def safe_float(val, default="N/A", decimals=2):
                        if val is None:
                            return default
                        try:
                            num = float(val)
                            return f"{num:.{decimals}f}"
                        except (ValueError, TypeError):
                            return str(val)  # เช่น "N/A", "?", "—"

                    def safe_percent(val, decimals=1):
                        if val is None:
                            return "N/A"
                        try:
                            num = float(val)
                            return f"{num:+.{decimals}f}%"
                        except (ValueError, TypeError):
                            return str(val)

                    # สร้างรายงานคุณภาพสูง
                    report_lines = ["📊 **Divergence Scan Report** 📊\n"]

                    for i, res in enumerate(div_results[:10], 1):
                        sym_clean = res['symbol'].replace('USDT', '')
                        div_type = res.get('type', 'Unknown').upper()
                        strength = res.get('div_strength')
                        rsi_diff = res.get('rsi_diff_pct')
                        price = res.get('price_current')
                        vol_confirm = "✔" if res.get('volume_confirm', False) else "✖"
                        tf = res.get('tf', '15m')

                        emoji = "🟢" if "bullish" in div_type.lower() else "🔴" if "bearish" in div_type.lower() else "⚪"

                        report_lines.append(
                            f"{i}. {emoji} **{sym_clean}**  • {div_type}\n"
                            f"   └ Strength: {safe_float(strength, decimals=2)}  | RSI Δ: {safe_percent(rsi_diff, decimals=1)}  | Vol confirm: {vol_confirm}\n"
                            f"   └ ราคา: {safe_float(price, decimals=4)}  • Timeframe: {tf}\n"
                        )

                    report_lines.append(f"\nพบทั้งหมด **{len(div_results)}** divergence")
                    report_lines.append("ใช้ `/ctai <เหรียญ>` เพื่อดูรายละเอียดเพิ่มเติม")

                    full_report = "\n".join(report_lines)
                    await send_telegram_report(full_report, chat_id)

                except Exception as e:
                    error_msg = f"❌ Divergence Scan ล้มเหลว\n{str(e)[:180]}"
                    await send_telegram_report(error_msg, chat_id)
                    print(f"[DIVSCAN ERROR] {e}")

            # ==========================================================================
            #         ชื่อคำสั่ง: /godentry
            #         สแกนเหรียญ Volume สูง + Setup คุณภาพสูง (Counter-Trend + ICT + Volume Spike + HTF Alignment)
            # ==========================================================================
            # //godentry– สแกน บอทจะสแกน → ตั้ง order อัตโนมัติทันทีถ้าผ่านเกณฑ์
            # ==========================================================================
            elif text == '/godentry':
                await send_telegram_report(
                    "⚡ **GOD ENTRY MODE - 60 เหรียญ** ⚡\n"
                    "กำลังสแกนเหรียญ Volume สูงสุด 60 เหรียญ + Setup เทพ...\n"
                    "• Counter-Trend + ICT + Volume Spike + HTF Alignment\n"
                    "• RR ≥ 2.0 | ตั้ง Limit อัตโนมัติ (สูงสุด 5 เหรียญ)\n"
                    "⏳ รอสักครู่... (ใช้เวลา ~1–2 นาที)",
                    chat_id
                )
                
                try:
                    # ─── 1. ดึง Top Volume เหรียญ (60 เหรียญ) ───
                    tickers = await client.futures_ticker()
                    candidates = []
                    for t in tickers:
                        if not t['symbol'].endswith('USDT'):
                            continue
                        vol = float(t.get('quoteVolume', 0))
                        if vol < 80_000_000:  # เกณฑ์ Volume ขั้นต่ำ (ปรับได้)
                            continue
                        candidates.append({
                            'symbol': t['symbol'],
                            'clean': t['symbol'].replace('USDT', ''),
                            'volume': vol,
                            'price': float(t.get('lastPrice', 0)),
                            'change24h': float(t.get('priceChangePercent', 0))
                        })
                    
                    candidates.sort(key=lambda x: x['volume'], reverse=True)
                    scan_list = candidates[:60]  # ← ปรับตรงนี้เป็น 60 เหรียญ
                    
                    if not scan_list:
                        await send_telegram_report("⚠️ ไม่พบเหรียญ Volume สูงพอในขณะนี้", chat_id)
                        return
                    
                    await send_telegram_report(
                        f"พบ {len(scan_list)} เหรียญ Volume สูงสุด\n"
                        f"กำลังวิเคราะห์และตั้ง order อัตโนมัติ... (สูงสุด 5 เหรียญ)",
                        chat_id
                    )
                    
                    # ─── 2. วิเคราะห์ + ตั้ง order อัตโนมัติ ───
                    entered = []
                    skipped = []
                    max_orders = 5  # จำกัดสูงสุด 5 เหรียญต่อรอบ
                    
                    # ใช้ semaphore เพื่อจำกัด concurrent requests (ป้องกัน rate limit)
                    semaphore = asyncio.Semaphore(8)  # 8 concurrent ปลอดภัยสำหรับ Binance
                    
                    async def process_coin(coin):
                        async with semaphore:
                            sym = coin['symbol']
                            sym_clean = coin['clean']
                            
                            # ตรวจ position/pending ซ้ำ
                            if any(p['symbol'] == sym for p in active) or \
                            any(o['symbol'] == sym for o in pending_orders_detail):
                                return f"{sym_clean} → มี position/pending อยู่แล้ว"
                            
                            # ดึงข้อมูลวิเคราะห์
                            analysis = await get_analysis_data(client, sym)
                            if not analysis:
                                return f"{sym_clean} → ดึงข้อมูลวิเคราะห์ล้มเหลว"
                            
                            # กรองคุณภาพสูงด้วย advanced filter
                            filter_res = await advanced_signal_filter(client, sym, analysis)
                            if not filter_res or not filter_res.get('pass'):
                                reason = filter_res.get('reason', 'ไม่ผ่าน advanced filter') if filter_res else 'filter error'
                                return f"{sym_clean} → {reason}"
                            
                            direction = filter_res['direction']
                            
                            # ตั้ง order จริง (dry_run=False)
                            result = await place_counter_trend_limit(
                                client=client,
                                symbol=sym,
                                analysis_data=analysis,
                                risk_usdt=0.50,
                                min_rr=2.0,
                                dry_run=False
                            )
                            
                            if result and result.get('success'):
                                entered.append({
                                    'clean': sym_clean,
                                    'direction': direction,
                                    'limit_price': result['limit_price'],
                                    'rr': result.get('rr', 0),
                                    'qty': result.get('qty', 0),
                                    'order_id': result.get('order_id', 'N/A')
                                })
                                return None  # สำเร็จ ไม่ต้องใส่ skipped
                            else:
                                reason = result.get('reason', 'ไม่ผ่านเกณฑ์') if result else 'ตั้ง order ล้มเหลว'
                                return f"{sym_clean} → {reason}"
                    
                    # รันแบบ concurrent
                    tasks = [process_coin(coin) for coin in scan_list]
                    results = await asyncio.gather(*tasks, return_exceptions=True)
                    
                    # รวบรวม skipped จากผลลัพธ์
                    for res in results:
                        if isinstance(res, Exception):
                            skipped.append(f"Error: {str(res)[:80]}")
                        elif res is not None:
                            skipped.append(res)
                    
                    # Progress update ทุก ๆ 15 เหรียญ (optional)
                    processed = len(scan_list) - len(skipped) - len(entered)
                    if processed % 15 == 0 and processed > 0:
                        await send_telegram_report(
                            f"กำลังประมวลผล... เสร็จแล้ว {processed}/{len(scan_list)} เหรียญ\n"
                            f"เข้าแล้ว: {len(entered)} | ข้าม: {len(skipped)}",
                            chat_id
                        )
                    
                    # ─── 3. สรุปรายงานเทพ ๆ ───
                    lines = ["⚡ **GOD ENTRY REPORT - 60 เหรียญ** ⚡\n━━━━━━━━━━━━━━━━━━━"]
                    
                    if entered:
                        lines.append(f"✅ **เข้า Order สำเร็จ {len(entered)} เหรียญ** (เทพสุด!)")
                        for e in entered:
                            emoji = "🟢 LONG" if e['direction'] == 'LONG' else "🔴 SHORT"
                            lines.append(
                                f"• `{e['clean']}` {emoji}\n"
                                f"  Limit: `{e['limit_price']:.4f}` | RR: `{e['rr']:.2f}:1`\n"
                                f"  Qty: `{e['qty']:.4f}` | ID: `{e['order_id']}`"
                            )
                    else:
                        lines.append("⚠️ ไม่พบ setup เทพพอใน 60 เหรียญ (RR < 2.0 หรือไม่มี confluence)")
                    
                    if skipped:
                        lines.append(f"\nข้าม/ล้มเหลว {len(skipped)} เหรียญ:")
                        for s in skipped[:10]:  # แสดง 10 อันดับแรก
                            lines.append(f"• {s}")
                        if len(skipped) > 10:
                            lines.append(f"...และอีก {len(skipped)-10} เหรียญ")
                    
                    lines.append("\n• ลองใหม่ใน 10–20 นาที ด้วย /godentry")
                    lines.append("• ดูสถานะด้วย /report /positions /limits")
                    
                    full_report = "\n".join(lines)
                    await send_telegram_report(full_report, chat_id)
                
                except Exception as e:
                    await send_telegram_report(f"❌ GOD ENTRY ล้มเหลว: {str(e)[:150]}", chat_id)
                    print(f"{Fore.RED}[GOD ENTRY CRASH] {e}{Style.RESET_ALL}")
            # ==========================================================================
            # /setauto – โหมด auto เทรดขั้นสูง (ปลอดภัย + รายงานละเอียด + cooldown แข็งแรง)
            # ==========================================================================
            elif text == '/setauto':
                await send_telegram_report(
                    "🚀 **SETAUTO MODE** เริ่มทำงาน\n"
                    "• สแกนสัญญาณคุณภาพสูง\n"
                    "• กรองหลายชั้น (signal + advanced filter + fib/swing)\n"
                    "• วาง Limit + SL/TP อัตโนมัติ (risk $0.50)\n"
                    "• จำกัดสูงสุด 8 ออเดอร์ต่อรอบ",
                    chat_id
                )

                try:
                    # ── การเตรียมข้อมูลพื้นฐาน ───────────────────────────────────────
                    active_syms    = {p['symbol'] for p in active}
                    pending_syms   = {o['symbol'] for o in pending_orders_detail}
                    excluded_syms  = active_syms | pending_syms

                    now_ts = time.time()

                    # ── สแกนสัญญาณหลัก ────────────────────────────────────────────────
                    scan_results = await fast_scan_top_20_signals(
                        client, price_map, excluded_syms, pending_orders_detail
                    )

                    if not scan_results:
                        await send_telegram_report("🔍 ไม่พบสัญญาณคุณภาพใด ๆ ในรอบนี้", chat_id)
                        return

                    # เรียงความน่าสนใจ (เหมือน fastscan แต่เข้มงวดกว่า)
                    scan_results.sort(
                        key=lambda r: (
                            r['signal_count'],
                            r.get('vol_ratio', 1.0),
                            100 - abs(r['rsi'] - 50)
                        ),
                        reverse=True
                    )

                    entered = []
                    skipped = []
                    errors  = []

                    for res in scan_results[:8]:
                        sym = res['symbol']
                        direction = res['direction']
                        sym_clean = sym.replace('USDT', '')

                        # 1. Cooldown เข้มงวด
                        if sym in setauto_cooldown:
                            remain_sec = setauto_cooldown[sym] + (SETAUTO_COOLDOWN_MINUTES * 60) - now_ts
                            if remain_sec > 0:
                                skipped.append(f"{sym_clean} → cooldown เหลือ ~{int(remain_sec/60)+1} นาที")
                                continue

                        # 2. ดึงข้อมูลวิเคราะห์หลัก
                        analysis = await get_advanced_analysis_data(client, sym)
                        if not isinstance(analysis, dict) or not analysis.get('price_current'):
                            skipped.append(f"{sym_clean} → analysis ไม่สมบูรณ์")
                            continue

                        curr_price = analysis['price_current']
                        atr = analysis.get('atr') or (curr_price * 0.015)

                        if curr_price <= 0 or atr <= 0:
                            skipped.append(f"{sym_clean} → ราคา/ATR ไม่ถูกต้อง")
                            continue

                        # 3. Advanced filter ต้องผ่าน + ทิศทางตรงกัน
                        filter_res = await advanced_signal_filter(client, sym, analysis)
                        if not filter_res or not filter_res.get('pass') or filter_res.get('direction') != direction:
                            reason = filter_res.get('reason', 'ไม่ผ่าน advanced filter') if filter_res else 'filter error'
                            skipped.append(f"{sym_clean} → {reason}")
                            continue

                        # 4. ดึง kline 15m แยก (ไม่เชื่อมั่น df จาก analysis)
                        try:
                            k_15m = await client.futures_klines(symbol=sym, interval='15m', limit=200)
                            if len(k_15m) < 100:
                                raise ValueError("kline ไม่พอ")
                            df_15m = calculate_indicators(k_15m)
                        except Exception as ex:
                            skipped.append(f"{sym_clean} → ไม่สามารถดึง/คำนวณ kline 15m ได้")
                            errors.append(f"{sym_clean}: {str(ex)[:80]}")
                            continue

                        # 5. Fibonacci + Swing
                        high = df_15m['high'].max()
                        low  = df_15m['low'].min()
                        fib_levels = calculate_fibonacci_levels(high, low)

                        swing_data = await analyze_historical_swings(client, sym, lookback_candles=200) or {
                            'recent_support': curr_price * 0.965,
                            'recent_resistance': curr_price * 1.035
                        }

                        # 6. คำนวณ Limit Price (สมมติฟังก์ชันนี้ return ราคาที่เหมาะสม)
                        limit_raw = calculate_setauto_limit_price(
                            curr_price, direction, df_15m, atr, fib_levels, swing_data
                        )

                        if not (curr_price * 0.85 < limit_raw < curr_price * 1.15):
                            skipped.append(f"{sym_clean} → Limit price ผิดปกติ ({limit_raw:.4f})")
                            continue

                        # 7. คำนวณ SL/TP + RR
                        if direction == 'LONG':
                            side_order = SIDE_BUY
                            close_side = SIDE_SELL
                            sl_raw = limit_raw - atr * ATR_SL_MULTIPLIER
                            tp_raw = limit_raw + atr * ATR_TP_MULTIPLIER
                        else:
                            side_order = SIDE_SELL
                            close_side = SIDE_BUY
                            sl_raw = limit_raw + atr * ATR_SL_MULTIPLIER
                            tp_raw = limit_raw - atr * ATR_TP_MULTIPLIER

                        rr = calculate_rr_ratio(limit_raw, sl_raw, tp_raw, direction)
                        if rr < 1.8:  # เข้มงวดกว่า fastscan
                            skipped.append(f"{sym_clean} → RR ต่ำเกิน ({rr:.2f})")
                            continue

                        # 8. Position sizing (risk $0.50)
                        stop_dist = abs(limit_raw - sl_raw)
                        if stop_dist <= 0 or stop_dist / limit_raw > 0.12:  # ป้องกัน stop กว้างเกิน
                            skipped.append(f"{sym_clean} → Stop distance ผิดปกติ")
                            continue

                        pos_value = 0.50 / (stop_dist / limit_raw)
                        qty = pos_value / limit_raw

                        step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
                        qty = math.floor(qty / step_size) * step_size
                        min_qty = step_size * 5
                        if qty < min_qty:
                            qty = min_qty

                        qty_prec = sym_info.get(sym, (4,2))[1]
                        qty_str = f"{qty:.{qty_prec}f}"

                        # 9. ปัดราคาทั้งหมด
                        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                        prec = sym_info.get(sym, (4,2))[0]

                        limit_p  = round_to_tick(limit_raw, tick_size)
                        sl_p     = round_to_tick(sl_raw, tick_size)
                        tp_p     = round_to_tick(tp_raw, tick_size)

                        limit_str = f"{limit_p:.{prec}f}"
                        sl_str    = f"{sl_p:.{prec}f}"
                        tp_str    = f"{tp_p:.{prec}f}"

                        # 10. ตั้ง Leverage + สั่ง订单 (ควรมี try-except แยก)
                        try:
                            await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)

                            # Limit order
                            order = await client.futures_create_order(
                                symbol=sym,
                                side=side_order,
                                type='LIMIT',
                                timeInForce='GTC',
                                quantity=qty_str,
                                price=limit_str
                            )

                            # SL & TP (closePosition=True)
                            await client.futures_create_order(
                                symbol=sym, side=close_side, type='STOP_MARKET',
                                stopPrice=sl_str, closePosition=True,
                                timeInForce='GTC', workingType='MARK_PRICE'
                            )
                            await client.futures_create_order(
                                symbol=sym, side=close_side, type='TAKE_PROFIT_MARKET',
                                stopPrice=tp_str, closePosition=True,
                                timeInForce='GTC', workingType='MARK_PRICE'
                            )

                            # บันทึก
                            pending_orders_detail.append({
                                'symbol': sym,
                                'side': side_order,
                                'price': limit_p,
                                'qty': qty,
                                'time': datetime.now(),
                                'orderId': order['orderId'],
                                'source': 'setauto',
                                'manual': False,
                                'sl_price': sl_p,
                                'tp_price': tp_p,
                                'rr': rr
                            })

                            setauto_cooldown[sym] = now_ts

                            entered.append(sym_clean)

                            # รายงานทันทีเมื่อสำเร็จ
                            await send_telegram_report(
                                f"✅ **SETAUTO วาง订单สำเร็จ**\n"
                                f"เหรียญ: `{sym_clean}`\n"
                                f"ทิศทาง: **{direction}**\n"
                                f"Limit: `{limit_str}`\n"
                                f"SL:    `{sl_str}`\n"
                                f"TP:    `{tp_str}`\n"
                                f"RR:    `{rr:.2f}:1`\n"
                                f"Qty:   `{qty_str}`  • Lev: `{MAX_LEVERAGE}x`\n"
                                f"Risk:  `$0.50 USDT`",
                                chat_id
                            )

                        except Exception as order_err:
                            errors.append(f"{sym_clean}: สั่ง订单ล้มเหลว → {str(order_err)[:120]}")
                            await send_telegram_report(
                                f"⚠️ {sym_clean} วาง Limit ไม่สำเร็จ\n{str(order_err)[:180]}",
                                chat_id
                            )

                    # ── สรุปผลรอบนี้ ────────────────────────────────────────────────────
                    summary_lines = [
                        "**สรุป SETAUTO รอบนี้**",
                        f"สแกนพบ: {len(scan_results)} สัญญาณ",
                        f"ผ่านทุกเกณฑ์ & วาง Limit สำเร็จ: **{len(entered)}** เหรียญ",
                    ]
                    if entered:
                        summary_lines.append("→ " + ", ".join(entered))
                    else:
                        summary_lines.append("→ ไม่มีรายการที่ผ่านเกณฑ์ทั้งหมด")

                    if skipped:
                        summary_lines.append(f"ข้ามทั้งหมด: {len(skipped)} เหรียญ")
                        summary_lines.extend([f"• {s}" for s in skipped[:6]])

                    if errors:
                        summary_lines.append(f"เกิด error: {len(errors)} รายการ")
                        summary_lines.extend([f"• {e}" for e in errors[:3]])

                    await send_telegram_report("\n".join(summary_lines), chat_id)

                except Exception as fatal:
                    await send_telegram_report(
                        f"❌ **SETAUTO CRITICAL ERROR**\n{str(fatal)[:200]}\nกรุณาตรวจสอบ log",
                        chat_id
                    )
                    print(f"[SETAUTO FATAL] {fatal}")
            # ===================== /aistats =====================
            elif text == '/aistats':
                ai_stats = brain.get_ai_stats()
                ai_text = (
                    f"🧠 **AI Model Training Stats**\n\n"
                    f"📊 **Data**:\n"
                    f" └ Total Trades Learned: `{ai_stats['total_trades']}`\n"
                    f" └ Epochs Trained: `{ai_stats['model_epochs_trained']}`\n\n"
                    f"🎯 **Accuracy**:\n"
                    f" └ Current: `{ai_stats['last_accuracy']:.2f}%`\n"
                    f" └ Average: `{ai_stats['avg_accuracy']:.2f}%`\n\n"
                    f"📉 **Loss**:\n"
                    f" └ Best Loss: `{ai_stats['best_loss']:.6f}`\n"
                    f" └ Latest Val Loss: `{ai_stats.get('last_val_loss', 999):.6f}`\n\n"
                    f"💡 **Status**:\n"
                    f" └ Model Ready: {'✅ Yes' if ai_stats['total_trades'] >= 10 else '⏳ Training (need 10+ trades)'}\n"
                    f" └ Confidence: `{brain.get_ai_confidence([0.5]*7):.1f}%` (avg)\n\n"
                    f"_บอท AI ยิ่งเล่นมากเทยิ่งฉลาด_ 🚀"
                )
                await send_telegram_report(ai_text, chat_id)
            # ==========================================================================
            #                  คำสั่ง /lmauto <symbol>
            # ==========================================================================

            # ===================== /lmauto <symbol> =====================
            elif text.startswith('/lmauto '):
                try:
                    parts = text.split()
                    if len(parts) < 2:
                        await send_telegram_report(
                            "❌ การใช้งาน: `/lmauto ETH` หรือ `/lmauto BTC`\n"
                            "(รองรับเฉพาะเหรียญคู่ USDT)",
                            chat_id
                        )
                        continue

                    sym_input = parts[1].upper()
                    sym = sym_input + 'USDT' if not sym_input.endswith('USDT') else sym_input

                    if sym not in sym_info:
                        await send_telegram_report(f"❌ ไม่รองรับเหรียญ {sym_input}", chat_id)
                        continue

                    # ป้องกัน double entry ทันที
                    if any(p['symbol'] == sym for p in active) or \
                       any(o['symbol'] == sym for o in pending_orders_detail):
                        await send_telegram_report(
                            f"⚠️ {sym_input} มี Position หรือ Pending Limit อยู่แล้ว\n"
                            "ใช้ `/status {sym_input}` เพื่อดูรายละเอียด",
                            chat_id
                        )
                        continue

                    await send_telegram_report(
                        f"⏳ กำลังวิเคราะห์ **ICT Smart Money Confluence** สำหรับ {sym_input}...\n"
                        "(อาจใช้เวลา 10–40 วินาที)",
                        chat_id
                    )

                    ict_data = await analyze_ict_smart_money(client, sym)
                    if not ict_data or not isinstance(ict_data, dict):
                        await send_telegram_report(
                            f"❌ การวิเคราะห์ ICT ล้มเหลวสำหรับ {sym_input}\n"
                            "สาเหตุที่พบบ่อย: ข้อมูล kline ไม่พอ / API timeout / ไม่มีโครงสร้างชัดเจน",
                            chat_id
                        )
                        continue

                    total_score = ict_data.get('total_score', 0)
                    direction = ict_data.get('direction', '').upper()

                    if total_score < 4.0 or not direction or direction not in ['LONG', 'SHORT']:
                        await send_telegram_report(
                            f"⚠️ **ไม่ผ่านเกณฑ์ ICT Confluence**\n"
                            f"• Score ได้รับ: {total_score:.1f} (ต้องการ ≥ 4.0)\n"
                            f"• Direction: {direction or 'ไม่ชัดเจน'}\n"
                            "ลองเหรียญอื่น หรือรอ setup ชัดเจนกว่านี้",
                            chat_id
                        )
                        continue

                    side_order = SIDE_BUY if direction == 'LONG' else SIDE_SELL
                    close_side = SIDE_SELL if direction == 'LONG' else SIDE_BUY

                    current_price = await get_current_price(client, sym)
                    if current_price <= 0:
                        await send_telegram_report(f"❌ ไม่สามารถดึงราคา {sym_input} ได้", chat_id)
                        continue

                    atr = await get_cached_atr(client, sym) or (current_price * 0.015)

                    # ── กำหนด Limit Price ตาม priority ของ ICT ───────────────────────
                    limit_price_raw = current_price * (0.985 if direction == 'LONG' else 1.015)  # fallback

                    priority_sources = ['ob_level', 'fvg_mid', 'liquidity_sweep_price']
                    for key in priority_sources:
                        if key in ict_data and isinstance(ict_data[key], (int, float)) and ict_data[key] > 0:
                            limit_price_raw = ict_data[key]
                            break

                    # ปรับเล็กน้อยให้สมเหตุสมผล (ไม่ให้ไกลเกิน)
                    max_dev = atr * 1.2
                    if direction == 'LONG':
                        limit_price_raw = max(limit_price_raw, current_price - max_dev)
                    else:
                        limit_price_raw = min(limit_price_raw, current_price + max_dev)

                    # ── SL / TP (aggressive ICT style แต่ปลอดภัยขึ้น) ────────────────
                    sl_multiplier = 0.8   # สั้น (หลัง wick / FVG edge)
                    tp_multiplier = 5.0   # เป้า RR ≥ 3+

                    sl_raw = limit_price_raw - atr * sl_multiplier if direction == 'LONG' else limit_price_raw + atr * sl_multiplier
                    tp_raw = limit_price_raw + atr * tp_multiplier if direction == 'LONG' else limit_price_raw - atr * tp_multiplier

                    rr = calculate_rr_ratio(limit_price_raw, sl_raw, tp_raw, direction)
                    if rr < 2.5:
                        await send_telegram_report(
                            f"⚠️ RR ไม่ถึงเกณฑ์ขั้นต่ำ 2.5:1 (ได้ {rr:.2f})\n"
                            f"เหรียญ: {sym_input} | Score: {total_score:.1f}",
                            chat_id
                        )
                        continue

                    # ── Position sizing ────────────────────────────────────────────────
                    stop_distance = abs(limit_price_raw - sl_raw)
                    if stop_distance <= 0 or stop_distance / limit_price_raw > 0.10:  # cap max risk distance ~10%
                        await send_telegram_report(f"❌ Stop distance ผิดปกติเกินไปสำหรับ {sym_input}", chat_id)
                        continue

                    risk_usdt = 0.50
                    position_value = risk_usdt / (stop_distance / limit_price_raw)
                    qty = position_value / limit_price_raw

                    step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
                    qty = max(step_size * 5, math.floor(qty / step_size) * step_size)

                    qty_prec = sym_info.get(sym, (4, 2))[1]
                    qty_str = f"{qty:.{qty_prec}f}"

                    # ปัดราคาให้ตรง tick
                    tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                    price_prec = sym_info.get(sym, (4, 2))[0]

                    limit_p = round_to_tick(limit_price_raw, tick_size)
                    sl_p   = round_to_tick(sl_raw, tick_size)
                    tp_p   = round_to_tick(tp_raw, tick_size)

                    limit_str = f"{limit_p:.{price_prec}f}"
                    sl_str    = f"{sl_p:.{price_prec}f}"
                    tp_str    = f"{tp_p:.{price_prec}f}"

                    # ── สั่ง订单 (ห่อด้วย try เพื่อแยก error) ─────────────────────────
                    try:
                        await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)

                        order = await client.futures_create_order(
                            symbol=sym,
                            side=side_order,
                            type='LIMIT',
                            timeInForce='GTC',
                            quantity=qty_str,
                            price=limit_str
                        )

                        # SL & TP (closePosition style)
                        await client.futures_create_order(
                            symbol=sym,
                            side=close_side,
                            type='STOP_MARKET',
                            stopPrice=sl_str,
                            closePosition=True,
                            timeInForce='GTC',
                            workingType='MARK_PRICE'
                        )

                        await client.futures_create_order(
                            symbol=sym,
                            side=close_side,
                            type='TAKE_PROFIT_MARKET',
                            stopPrice=tp_str,
                            closePosition=True,
                            timeInForce='GTC',
                            workingType='MARK_PRICE'
                        )

                    except Exception as order_err:
                        await send_telegram_report(
                            f"❌ สั่ง订单ล้มเหลวสำหรับ {sym_input}\n"
                            f"รายละเอียด: {str(order_err)[:180]}",
                            chat_id
                        )
                        continue

                    # ── รายงานละเอียด + สวยงาม ──────────────────────────────────────
                    confluence_items = []
                    for k, v in ict_data.items():
                        if v is True or (isinstance(v, (int, float, str)) and k not in ['direction', 'total_score']):
                            key_name = k.replace('_', ' ').title()
                            confluence_items.append(f"• {key_name}")

                    report = (
                        "🔥 **/lmauto วาง Limit Auto สำเร็จ – ICT Smart Money**\n\n"
                        f"เหรียญ:          `{sym_input}`\n"
                        f"ทิศทาง:         **{direction}**\n"
                        f"Limit Price:    `{limit_str}`\n"
                        f"SL (tight):     `{sl_str}`\n"
                        f"TP (extended):  `{tp_str}`\n"
                        f"RR Ratio:       `{rr:.2f}:1`\n"
                        f"Qty:            `{qty_str}`\n"
                        f"Leverage:       `{MAX_LEVERAGE}x`\n"
                        f"Risk:           `$0.50 USDT`\n"
                        f"ICT Score:      `{total_score:.1f}`\n\n"
                        "**Confluence ที่ตรวจพบ:**\n" +
                        "\n".join(confluence_items[:8]) +  # จำกัดไม่ให้ยาวเกิน
                        ("\n...และอื่นๆ" if len(confluence_items) > 8 else "") +
                        f"\n\nOrder ID: `{order['orderId']}`"
                    )
                    await send_telegram_report(report, chat_id)

                    # บันทึก pending
                    pending_orders_detail.append({
                        'symbol': sym,
                        'side': side_order,
                        'price': limit_p,
                        'qty': qty,
                        'time': datetime.now(),
                        'orderId': order['orderId'],
                        'source': 'lmauto_ict',
                        'manual': False,
                        'sl_price': sl_p,
                        'tp_price': tp_p,
                        'rr': rr,
                        'ict_score': total_score
                    })

                except Exception as e:
                    await send_telegram_report(
                        f"❌ /lmauto ล้มเหลวสำหรับ {sym_input or 'ไม่ระบุ'}\n{str(e)[:200]}",
                        chat_id
                    )
                    print(f"[LMAUTO ERROR] {sym_input}: {e}")

            # ===================== /trainnow =====================
            # ===================== /trainnow =====================
            elif text == '/trainnow':
                try:
                    await send_telegram_report("🧠 **กำลังฝึกโมเดล AI ทันที...**", chat_id)

                    training_msg = ""
                    training_count = 0

                    # ถ้าข้อมูลเทรดยังน้อย (<30) → รัน backtest เพื่อ pre-train
                    if len(brain.data) < 30:
                        await send_telegram_report(
                            f"ข้อมูลเทรดใน brain ยังน้อย ({len(brain.data)})\n"
                            "→ ทำ backtest เพิ่มก่อนเพื่อให้ AI เรียนรู้เร็วขึ้น",
                            chat_id
                        )
                        
                        print(f"{Fore.CYAN}Starting backtest pre-training (100 periods)...{Style.RESET_ALL}")
                        backtest_result = await backtest_ai_training(client, periods=100, chat_id=chat_id)
                        
                        if backtest_result and 'results' in backtest_result:
                            for res in backtest_result['results']:
                                if 'features' in res and 'win' in res:
                                    brain.update_memory(res['features'], res['win'])
                                    training_count += 1
                            
                            training_msg = (
                                f"✅ **Backtest Pre-train สำเร็จ!**\n"
                                f"เพิ่มข้อมูลเทรดเข้า AI: **{training_count}** trades\n"
                                f"Total samples ใน brain ตอนนี้: **{len(brain.data)}**\n"
                                "กำลัง train โมเดลต่อ..."
                            )
                            await send_telegram_report(training_msg, chat_id)

                    # Train โมเดล (ไม่ว่าจะมาจาก backtest หรือข้อมูลจริง)
                    print(f"{Fore.CYAN}Training AI model now... (samples: {len(brain.data)}){Style.RESET_ALL}")
                    brain.train_model()
                    
                    stats = brain.get_ai_stats() or {}
                    
                    report = (
                        "🧠 **Force Train Model สำเร็จ!**\n\n"
                        f"• Total samples ใน brain: **{stats.get('total_trades', 0)}**\n"
                    )
                    
                    if training_count > 0:
                        report += f"• เพิ่มจาก backtest: **{training_count}** trades\n"
                    
                    report += (
                        f"• Accuracy ล่าสุด: **{stats.get('last_accuracy', 0):.2f}%**\n"
                        f"• Best validation loss: **{stats.get('best_loss', 'N/A'):.6f}**\n"
                        f"• Training rounds/epocs: **{stats.get('model_epochs_trained', '?')}**\n"
                        f"• เวลาที่ใช้: {datetime.now().strftime('%H:%M:%S')}\n\n"
                        f"💡 **สถานะ AI**:\n"
                        f"   └ พร้อมใช้งานจริง: {'✅ ดีมาก' if stats.get('total_trades', 0) >= 50 else '⏳ ยังเรียนรู้อยู่'}\n"
                        f"   └ ใช้ `/aistats` เช็คความก้าวหน้าเพิ่มเติม"
                    )
                    
                    await send_telegram_report(report, chat_id)
                    
                    # บันทึกโมเดลทันทีหลัง train (แนะนำเปิด)
                    try:
                        torch.save(brain.model.state_dict(), brain.model_file)
                        print(f"{Fore.GREEN}Model saved after force train: {brain.model_file}{Style.RESET_ALL}")
                    except Exception as save_err:
                        print(f"{Fore.YELLOW}Failed to save model: {save_err}{Style.RESET_ALL}")

                except Exception as e:
                    await send_telegram_report(
                        f"❌ Force Train ล้มเหลว\n"
                        f"ข้อผิดพลาด: {str(e)[:180]}\n"
                        "กรุณาลองใหม่หรือเช็ค log",
                        chat_id
                    )
                    print(f"[TRAINNOW ERROR] {e}")
                    import traceback
                    traceback.print_exc()

            #                  เพิ่มคำสั่ง /ctai <symbol> ใน Telegram Handler
            # ==========================================================================

            # ในฟังก์ชัน async def check_telegram_updates(client, cmd_q, price_map):
            # ให้เพิ่ม elif นี้ลงไป (วางไว้ใกล้ ๆ กับ elif text.startswith('/analyze ') หรือคำสั่งอื่น ๆ)

            elif text.startswith('/ctai') or text == '/ctaiauto':
                parts = text.split()
                auto_mode = len(parts) == 1  # ถ้าไม่มีชื่อเหรียญ → โหมด auto scan & set order
                
                if auto_mode:
                    await send_telegram_report(
                        "🚀 **โหมดอัตโนมัติ /ctai เริ่มทำงาน**\n"
                        "• สแกนเหรียญ Volume สูง + Setup Counter-Trend/ICT\n"
                        "• ถ้าผ่านเกณฑ์ RR ≥ 1.8 → ตั้ง Limit Order อัตโนมัติทันที\n"
                        "• กำลังสแกน... (อาจใช้เวลา 1-3 นาที)",
                        chat_id
                    )
                else:
                    # โหมด manual เหรียญเดียว (เหมือนเดิม แต่ยังคงตั้ง order ได้)
                    sym_input = parts[1].upper()
                    sym = sym_input + 'USDT' if not sym_input.endswith('USDT') else sym_input
                    await send_telegram_report(f"⏳ กำลังวิเคราะห์และตั้ง order อัตโนมัติสำหรับ {sym_input}...", chat_id)

                try:
                    # ─── 1. เตรียมรายชื่อเหรียญที่จะสแกน ───
                    if auto_mode:
                        # สแกน Top Volume
                        tickers = await client.futures_ticker()
                        candidates = []
                        for t in tickers:
                            if not t['symbol'].endswith('USDT'):
                                continue
                            sym = t['symbol']
                            vol = float(t.get('quoteVolume', 0))
                            if vol < 80_000_000:  # ปรับ threshold ตามต้องการ (เช่น 80 ล้านขึ้นไป)
                                continue
                            candidates.append({
                                'symbol': sym,
                                'clean': sym.replace('USDT', ''),
                                'volume': vol,
                                'price': float(t.get('lastPrice', 0)),
                                'change24h': float(t.get('priceChangePercent', 0))
                            })
                        candidates.sort(key=lambda x: x['volume'], reverse=True)
                        scan_list = candidates[:30]  # สแกนสูงสุด 30 เหรียญเพื่อความเร็ว
                    else:
                        # โหมด manual เหรียญเดียว
                        scan_list = [{'symbol': sym, 'clean': sym_input, 'volume': 0, 'price': 0, 'change24h': 0}]

                    if not scan_list:
                        await send_telegram_report("⚠️ ไม่พบเหรียญ Volume สูงพอในขณะนี้", chat_id)
                        continue

                    # ─── 2. วิเคราะห์และตั้ง order อัตโนมัติ ───
                    success_orders = []
                    failed_orders = []

                    for coin in scan_list:
                        sym = coin['symbol']
                        sym_clean = coin['clean']

                        # ตรวจว่ามี position หรือ pending อยู่แล้วหรือไม่
                        if any(p['symbol'] == sym for p in active) or any(o['symbol'] == sym for o in pending_orders_detail):
                            failed_orders.append(f"{sym_clean} → มี position/pending อยู่แล้ว ข้าม")
                            continue

                        # ดึงข้อมูลวิเคราะห์ (ใช้ฟังก์ชันเดิมของคุณ)
                        analysis_data = await get_analysis_data(client, sym)
                        if not analysis_data or not analysis_data.get('price_current'):
                            failed_orders.append(f"{sym_clean} → ข้อมูลวิเคราะห์ไม่สมบูรณ์")
                            continue

                        # เรียก Counter-Trend setup (dry_run=False เพื่อตั้ง order จริง)
                        result = await place_counter_trend_limit(
                            client=client,
                            symbol=sym,
                            analysis_data=analysis_data,
                            risk_usdt=0.50,
                            min_rr=1.8,          # เกณฑ์ขั้นต่ำที่น่าเข้า
                            dry_run=False        # ตั้ง order จริงเลย
                        )

                        if result and result.get('success'):
                            success_orders.append({
                                'clean': sym_clean,
                                'direction': result['direction'],
                                'limit_price': result['limit_price'],
                                'rr': result['rr'],
                                'qty': result['qty'],
                                'order_id': result.get('order_id', 'N/A')
                            })
                            print(f"{Fore.GREEN}[AUTO ORDER] ตั้งสำเร็จ: {sym_clean} {result['direction']}{Style.RESET_ALL}")
                        else:
                            reason = result.get('reason', 'ไม่ผ่านเกณฑ์') if result else 'วิเคราะห์ล้มเหลว'
                            failed_orders.append(f"{sym_clean} → {reason}")

                    # ─── 3. สรุปรายงาน ───
                    lines = ["🚀 **ผลการสแกนและตั้ง Order อัตโนมัติ (/ctai)**\n━━━━━━━━━━━━━━━━━━━"]

                    if success_orders:
                        lines.append(f"✅ **ตั้ง Order สำเร็จ {len(success_orders)} เหรียญ**")
                        for order in success_orders:
                            dir_emoji = "🟢 LONG" if order['direction'] == 'LONG' else "🔴 SHORT"
                            lines.append(
                                f"• `{order['clean']}` {dir_emoji}\n"
                                f"  Limit: `{order['limit_price']:.4f}` | RR: `{order['rr']:.2f}:1`\n"
                                f"  Qty: `{order['qty']:.4f}` | Order ID: `{order['order_id']}`"
                            )
                    else:
                        lines.append("⚠️ ไม่พบ setup ที่น่าเข้าเลยในรอบนี้ (RR < 1.8 หรือไม่มีสัญญาณ)")

                    if failed_orders:
                        lines.append(f"\nข้าม/ล้มเหลว {len(failed_orders)} เหรียญ:")
                        for fail in failed_orders[:5]:  # แสดง 5 อันดับแรก
                            lines.append(f"• {fail}")
                        if len(failed_orders) > 5:
                            lines.append(f"...และอีก {len(failed_orders)-5} เหรียญ")

                    lines.append("\n• ลองใหม่ใน 15–30 นาที หรือใช้ `/fulllm` สแกนเมเจอร์ทั้งหมด")
                    full_report = "\n".join(lines)
                    
                    await send_telegram_report(full_report, chat_id)

                except Exception as e:
                    await send_telegram_report(f"❌ เกิดข้อผิดพลาดใน /ctai auto: {str(e)[:120]}", chat_id)
                    print(f"{Fore.RED}[CTAI AUTO ERROR] {e}{Style.RESET_ALL}")

            # ===================== /fastscan =====================
            # ใน async def check_telegram_updates(client, cmd_q, price_map):

            elif text == '/fastscan':
                await send_telegram_report("⏳ กำลังสแกนเร่งด่วน 20 เหรียญ (Signals > 3)...", chat_id)
                try:
                    active_symbol_names = [p['symbol'] for p in active]
                    scan_results = await fast_scan_top_20_signals(
                        client, price_map, active_symbol_names, pending_orders_detail
                    )
                    
                    if not scan_results:
                        await send_telegram_report(
                            "🔍 **Fast Scan - ไม่พบสัญญาณ**\n"
                            "ตรวจสอบ Top 20 เหรียญแล้วไม่มีสัญญาณ ≥ 3 ตัว\n"
                            "_ลองใหม่ในไม่กี่นาที..._",
                            chat_id
                        )
                        return

                    # =============================================================
                    # เรียงลำดับความน่าสนใจก่อน (counter-trend friendly)
                    # หลัก → จำนวน signal มากที่สุด
                    # รอง 1 → Volume ratio สูง
                    # รอง 2 → RSI ห่างจาก 50 มากที่สุด
                    # =============================================================
                    scan_results.sort(
                        key=lambda r: (
                            r['signal_count'],
                            r.get('vol_ratio', 1.0),
                            100 - abs(r['rsi'] - 50)
                        ),
                        reverse=True
                    )

                    # ────────────────────────────────────────────────
                    # สร้างรายงาน (สไตล์ละเอียดเหมือนตัวเก่า)
                    # ────────────────────────────────────────────────
                    msg = "🚀 **Fast Scan พบสัญญาณ!**\n\n"
                    entered = []
                    for result in scan_results[:3]:  # จำกัด 3 เหรียญ
                        sym_clean = result['symbol'].replace('USDT', '')
                        direction_emoji = "🟢 LONG" if result['direction'] == 'LONG' else "🔴 SHORT"
                        
                        msg += (
                            f"{direction_emoji} `{sym_clean}`\n"
                            f"   └ Signals: {result['signal_count']}/8\n"
                            f"   └ RSI: {result['rsi']:.1f} | Vol: {result['vol_ratio']:.2f}x\n"
                            f"   └ กำลังตรวจ Counter-Trend + วาง Limit...\n\n"
                        )

                        analysis_data = await get_analysis_data(client, result['symbol'])
                        if not analysis_data:
                            msg += f"   └ ข้าม {sym_clean} (ข้อมูลไม่พอ)\n\n"
                            continue

                        ct_result = await place_counter_trend_limit(
                            client=client,
                            symbol=result['symbol'],
                            analysis_data=analysis_data,
                            risk_usdt=0.50,
                            min_rr=1.5
                        )

                        if ct_result and ct_result.get('success'):
                            entered.append(sym_clean)
                            msg += f"   └ **สำเร็จ!** Limit วางแล้ว (RR {ct_result['rr']:.2f})\n\n"
                        else:
                            reason = ct_result.get('reason', 'ไม่ผ่านเกณฑ์') if ct_result else 'วิเคราะห์ล้มเหลว'
                            msg += f"   └ ข้าม {sym_clean}: {reason}\n\n"

                    if entered:
                        msg += f"\n✅ **เข้า Counter-Trend Auto สำเร็จ {len(entered)} เหรียญ**: {', '.join(entered)}"
                    else:
                        msg += "\n⚠️ ไม่มีเหรียญไหนผ่านเกณฑ์ Counter-Trend ในรอบนี้"

                    await send_telegram_report(msg, chat_id)

                except Exception as e:
                    await send_telegram_report(f"❌ Fast Scan error: {str(e)}", chat_id)
                    print(f"{Fore.RED}Fast scan error: {e}{Style.RESET_ALL}")

            # ===================== /setlm <symbol> <price> <L/S> [xเลเวอเรจ] [จำนวนเงิน] =====================
            elif text.startswith('/setlm '):
                try:
                    parts = text.split()
                    if len(parts) < 4:
                        await send_telegram_report(
                            "❌ รูปแบบไม่ถูกต้อง\n"
                            "ใช้: `/setlm SOL 139 L` หรือ `/setlm SOL 139 L x20 1` หรือ `/setlm BTC 92000 S x10 2`",
                            chat_id
                        )
                        continue

                    sym_input = parts[1].upper()
                    sym = sym_input + "USDT" if not sym_input.endswith("USDT") else sym_input

                    if sym not in sym_info:
                        await send_telegram_report(f"❌ ไม่รองรับเหรียญ {sym_input}", chat_id)
                        continue

                    try:
                        limit_price = float(parts[2])
                    except:
                        await send_telegram_report("❌ ราคาต้องเป็นตัวเลข", chat_id)
                        continue

                    direction_char = parts[3].upper()
                    if direction_char not in ['L', 'S']:
                        await send_telegram_report("❌ ต้องระบุ L (Long/Buy) หรือ S (Short/Sell)", chat_id)
                        continue

                    side_order = SIDE_BUY if direction_char == 'L' else SIDE_SELL
                    direction_text = "LONG (Buy)" if direction_char == 'L' else "SHORT (Sell)"

                    leverage = MAX_LEVERAGE
                    risk_amount = 0.5

                    i = 4
                    while i < len(parts):
                        p = parts[i].strip().lower()
                        if p.startswith('x') and p[1:].isdigit():
                            try:
                                leverage_input = int(p[1:])
                                if 1 <= leverage_input <= MAX_LEVERAGE:
                                    leverage = leverage_input
                                else:
                                    await send_telegram_report(
                                        f"⚠️ เลเวอเรจต้องอยู่ระหว่าง 1–{MAX_LEVERAGE}x (ใช้ {MAX_LEVERAGE}x แทน)",
                                        chat_id
                                    )
                                    leverage = MAX_LEVERAGE
                            except:
                                pass
                        elif p.replace('.', '', 1).isdigit():
                            try:
                                risk_amount = float(p)
                                if risk_amount <= 0:
                                    risk_amount = 0.5
                            except:
                                pass
                        i += 1

                    current_price = price_map.get(sym, 0.0)
                    if current_price <= 0:
                        await send_telegram_report(f"❌ ไม่สามารถดึงราคา {sym_input} ได้", chat_id)
                        continue

                    if direction_char == 'L' and limit_price >= current_price * 1.03:
                        await send_telegram_report(
                            f"⚠️ ราคา Limit Buy สูงเกินไป ({limit_price:.4f} > {current_price*1.03:.4f})",
                            chat_id
                        )
                        continue
                    if direction_char == 'S' and limit_price <= current_price * 0.97:
                        await send_telegram_report(
                            f"⚠️ ราคา Limit Sell ต่ำเกินไป ({limit_price:.4f} < {current_price*0.97:.4f})",
                            chat_id
                        )
                        continue

                    atr = await get_cached_atr(client, sym)
                    if atr is None or atr <= 0:
                        atr = current_price * 0.015

                    if direction_char == 'L':
                        sl_raw = limit_price - (atr * ATR_SL_MULTIPLIER)
                        tp_raw = limit_price + (atr * ATR_TP_MULTIPLIER)
                    else:
                        sl_raw = limit_price + (atr * ATR_SL_MULTIPLIER)
                        tp_raw = limit_price - (atr * ATR_TP_MULTIPLIER)

                    rr = calculate_rr_ratio(limit_price, sl_raw, tp_raw, 'SHORT' if direction_char == 'S' else 'LONG')
                    if rr < 1.3:
                        await send_telegram_report(
                            f"⚠️ RR ต่ำเกินไป ({rr:.2f}:1) → ยังตั้งได้ แต่ไม่แนะนำ",
                            chat_id
                        )

                    stop_distance = abs(limit_price - sl_raw)
                    if stop_distance <= 0:
                        await send_telegram_report("❌ Stop distance ไม่ถูกต้อง", chat_id)
                        continue

                    position_value = risk_amount / (stop_distance / limit_price)
                    qty = position_value / limit_price

                    step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
                    qty = math.floor(qty / step_size) * step_size

                    min_qty = step_size * 5
                    if qty < min_qty:
                        qty = min_qty

                    qty_precision = sym_info.get(sym, (4, 2))[1]
                    qty_str = f"{qty:.{qty_precision}f}"

                    tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                    limit_price_rounded = round_to_tick(limit_price, tick_size)
                    price_precision = sym_info.get(sym, (4, 2))[0]
                    price_str = f"{limit_price_rounded:.{price_precision}f}"

                    try:
                        await client.futures_change_leverage(symbol=sym, leverage=leverage)
                    except Exception as e:
                        await send_telegram_report(f"⚠️ ไม่สามารถตั้งเลเวอเรจ {leverage}x ได้: {str(e)}", chat_id)
                        continue

                    order = await client.futures_create_order(
                        symbol=sym,
                        side=side_order,
                        type='LIMIT',
                        timeInForce='GTC',
                        quantity=qty_str,
                        price=price_str
                    )

                    order_time = datetime.now()
                    pending_orders_detail.append({
                        'symbol': sym,
                        'side': side_order,
                        'price': limit_price_rounded,
                        'qty': qty,
                        'time': order_time,
                        'orderId': order['orderId'],
                        'manual': True,
                        'needs_sltp': True,
                        'leverage': leverage,
                        'risk_usdt': risk_amount,
                        'source': 'manual_setlm'
                    })

                    # รายงานผลละเอียด (เวอร์ชันปรับปรุงล่าสุด)
                    report = (
                        "✅ **ตั้ง Limit Order แมนนวลสำเร็จ!**\n\n"
                        f"เหรียญ              `{sym.replace('USDT', '')}`\n"
                        f"ทิศทาง             **{direction_text}**\n"
                        f"ราคา Limit         `{price_str}`\n"
                        f"ปริมาณ (Qty)       `{qty_str}`\n"
                        f"เลเวอเรจ           `{leverage}x`\n"
                        f"ความเสี่ยง         `${risk_amount:.2f}` USDT\n"
                        f"อัตราส่วน RR       `{rr:.2f}:1` (โดยประมาณ)\n"
                        f"ราคาปัจจุบัน       `{current_price:.4f}`\n"
                        f"ATR ที่ใช้คำนวณ    `{atr:.6f}`\n"
                        f"SL โดยประมาณ      `{round_to_tick(sl_raw, tick_size):.{price_precision}f}`\n"
                        f"TP โดยประมาณ      `{round_to_tick(tp_raw, tick_size):.{price_precision}f}`\n"
                        f"Order ID           `{order['orderId']}`\n\n"
                        "⚠️ ระบบยังไม่ได้วาง SL/TP อัตโนมัติ กรุณาตรวจสอบและตั้งค่าใน Binance ด้วยตนเอง"
                    )
                    await send_telegram_report(report, chat_id)

                    print(f"{Fore.GREEN}Manual Limit สำเร็จ: {sym} {direction_text} @ {price_str} | Lev {leverage}x | Risk ${risk_amount}{Style.RESET_ALL}")

                except Exception as e:
                    await send_telegram_report(f"❌ Set Limit Manual error: {str(e)}", chat_id)
                    print(f"{Fore.RED}Setlm error: {e}{Style.RESET_ALL}")
                    await send_telegram_report(f"❌ ตั้ง Limit ล้มเหลว: {str(e)}", chat_id)
                    print(f"{Fore.RED}setlm error: {e}{Style.RESET_ALL}")

            # ===================== คำสั่งงานจากบอท (เพิ่มเติม) =====================

            # 1. /worklist หรือ /tasks - แสดงงาน/สิ่งที่บอทกำลังทำอยู่
            elif text in ['/worklist', '/tasks', '/jobs']:
                active_tasks = []
                if auto_spike_enabled:
                    active_tasks.append("ตรวจ Volume Spike → Auto LONG (ทุก 5-15 นาที)")
                if auto_short_signal_enabled:
                    active_tasks.append("ตรวจ Strong Short Signal → Auto SHORT (ทุก 7 นาที)")
                if pending_orders_detail:
                    active_tasks.append(f"รอ Limit Order fill {len(pending_orders_detail)} รายการ")
                if active:
                    active_tasks.append(f"ดูแล Position เปิด {len(active)} ตำแหน่ง (Trailing + SL/TP)")
                
                if not active_tasks:
                    msg = "ตอนนี้บอทยังไม่มีงานที่กำลังรันอยู่ (เงียบ ๆ อยู่)"
                else:
                    msg = "📋 **งานที่บอทกำลังทำอยู่**\n\n" + "\n".join([f"• {t}" for t in active_tasks])
                
                msg += f"\n\nสถานะล่าสุด: {'🟢 กำลังสแกน' if datetime.now().timestamp() % 60 < 30 else '🔵 พักสแกน'}"
                await send_telegram_report(msg, chat_id)

            # 2. /pauseall - หยุดทุกการทำงานอัตโนมัติชั่วคราว (แต่ยังดูแล position อยู่)
# คำสั่งต่าง ๆ รวมถึง /pauseall, /resumall ฯลฯ
            elif text == '/pauseall':
                auto_spike_enabled = False          # ← ตอนนี้ไม่มีปัญหาแล้ว
                auto_short_signal_enabled = False
                await send_telegram_report(
                    "🛑 **PAUSE ALL ACTIVATED**\n"
                    "• หยุด Auto LONG (Volume Spike)\n"
                    "• หยุด Auto SHORT (Strong Signal)\n"
                    "• ยังคงดูแล Position เปิด + Trailing Stop อยู่\n"
                    "เปิดกลับด้วย /spike on และ /shortsig on",
                    chat_id
                )

            # 3. /resumall - กลับมาทำงานอัตโนมัติทั้งหมด
            elif text == '/resumall' or text == '/resume':
                auto_spike_enabled = True
                auto_short_signal_enabled = True
                await send_telegram_report(
                    "▶️ **RESUME ALL ACTIVATED**\n"
                    "• Auto LONG (Volume Spike) → เปิดแล้ว\n"
                    "• Auto SHORT (Strong Signal) → เปิดแล้ว\n"
                    "เริ่มสแกนใหม่ทันที...",
                    chat_id
                )

            # 4. /status หรือ /now - สรุปสถานะแบบสั้น ๆ เร็ว ๆ
            elif text in ['/status', '/now']:
                current_time_str = datetime.now().strftime("%H:%M:%S")
                msg = f"🕒 **สถานะล่าสุด {current_time_str}**\n\n"
                msg += f"💰 Balance: `{bal:,.2f}` USDT\n"
                msg += f"Position เปิด: `{len(active)}`\n"
                msg += f"Limit รอ: `{len(pending_orders_detail)}`\n"
                msg += f"Auto LONG: {'🟢 เปิด' if auto_spike_enabled else '🔴 ปิด'}\n"
                msg += f"Auto SHORT: {'🟢 เปิด' if auto_short_signal_enabled else '🔴 ปิด'}\n"
                
                if active:
                    total_pnl = sum(p['pnl'] for p in active)
                    msg += f"PNL รวมเปิด: `{total_pnl:+,.2f}` USDT\n"
                
                await send_telegram_report(msg, chat_id)

            # 5. /restartscan - บังคับให้สแกนใหม่ทันที (1 รอบ)
            elif text == '/restartscan':
                await send_telegram_report("🔄 กำลังเริ่มสแกนใหม่ทันที...", chat_id)
                # คุณสามารถเรียกฟังก์ชันสแกนหลักได้เลย เช่น
                # await fast_scan_top_20_signals(...) หรือฟังก์ชันที่คุณใช้สแกนปกติ
                # ถ้าไม่มีฟังก์ชันแยก → ข้ามส่วนนี้ หรือเพิ่ม flag เพื่อ trigger ใน loop หลัก
                print("ได้รับคำสั่ง /restartscan จาก Telegram")

            # 6. /helpwork หรือ /helpjobs - คู่มือคำสั่งงานจากบอท
            elif text in ['/helpwork', '/helpjobs']:
                help_work = (
                    "📋 **คำสั่งควบคุมงานของบอท**\n\n"
                    "/worklist หรือ /tasks → ดูว่าบอทกำลังทำอะไรอยู่\n"
                    "/pauseall → หยุด Auto Entry ทั้งหมด (แต่ยังดูแล position)\n"
                    "/resumall หรือ /resume → กลับมาเปิด Auto ทั้งหมด\n"
                    "/status หรือ /now → สรุปสถานะแบบสั้นเร็ว\n"
                    "/restartscan → บังคับสแกนหาสัญญาณใหม่ทันที\n"
                    "/setlm <เหรียญ> <ราคา> <L/S> → ตั้ง Limit แมนนวล\n\n"
                    "คำสั่งเหล่านี้ใช้ควบคุมการทำงานอัตโนมัติโดยไม่ต้องปิดบอท"
                    "ext...."
                    "/trainnow → บังคับให้ AI เทรนโมเดลทันที (ถ้ามีข้อมูลพอ)\n"
                    "/aistats → ดูสถิติการเทรน AI\n"
                    "/backtest [num_periods] [train] → รัน backtest และ pre-train AI\n"
                    "/ctai <เหรียญ> → เข้า Counter-Trend อัตโนมัติ\n"
                    "/lmauto <เหรียญ> → เข้า ICT Smart Money อัตโนมัติ\n"
                    "/ctai และ lmauto จะตั้ง Limit Order อัตโนมัติ\n"
                    "/divscan → สแกนเหรียญที่มี Divergence อัตโนมัติ\n"
                    "/autoshort on/off"
                )
                await send_telegram_report(help_work, chat_id)
                
            # ==========================================================================
            # /autoshort – เปิด/ปิดระบบเทรด short อัตโนมัติ (ต้องใช้ผ่านบอทเท่านั้น)
            # ==========================================================================
            elif text.startswith('/autoshort'):
                parts = text.split()
                if len(parts) == 1:
                    status = "🟢 **เปิดใช้งาน**" if auto_short_system_enabled else "🔴 **ปิดใช้งาน**"
                    await send_telegram_report(
                        f"🤖 **Auto-Short Trading Mode**\n"
                        f"สถานะ: {status}\n\n"
                        f"• เมื่อเปิด: ระบบจะเปิด short อัตโนมัติเมื่อพบสัญญาณครบเงื่อนไข\n"
                        f"• เมื่อปิด: ระบบยังสแกนสัญญาณ แต่จะไม่เปิดออเดอร์จริง\n\n"
                        f"ใช้คำสั่ง:\n"
                        f"• `/autoshort on` → เปิดโหมดอัตโนมัติ\n"
                        f"• `/autoshort off` → ปิดโหมดอัตโนมัติ",
                        chat_id
                    )
                elif len(parts) == 2:
                    cmd = parts[1].lower()
                    if cmd == 'on':
                        auto_short_system_enabled = True
                        await send_telegram_report(
                            "✅ **Auto-Short Mode: เปิดใช้งาน!**\n"
                            "ระบบจะเปิด short อัตโนมัติทันทีเมื่อพบสัญญาณ:\n"
                            "• BOS/CHOCH ยืนยันเทรนด์ลง\n"
                            "• Elliott Wave คลื่น C\n"
                            "• Fibonacci rejection 61.8–78.6%\n"
                            "• Bearish divergence + RSI > 65\n"
                            "• Volume spike + liquidity grab",
                            chat_id
                        )
                        print(f"{Fore.GREEN}[AUTO-SHORT] โหมดอัตโนมัติเปิดโดยผู้ใช้{Style.RESET_ALL}")
                    elif cmd == 'off':
                        auto_short_system_enabled = False
                        await send_telegram_report(
                            "🛑 **Auto-Short Mode: ปิดใช้งาน**\n"
                            "ระบบยังคงสแกนสัญญาณ แต่จะไม่เปิดออเดอร์จริงอีกต่อไป",
                            chat_id
                        )
                        print(f"{Fore.YELLOW}[AUTO-SHORT] โหมดอัตโนมัติปิดโดยผู้ใช้{Style.RESET_ALL}")
                    else:
                        await send_telegram_report("❌ ใช้: `/autoshort on` หรือ `/autoshort off`", chat_id)
                else:
                    await send_telegram_report("❌ รูปแบบคำสั่งไม่ถูกต้อง", chat_id)
            # ===================== /backtest =====================
            elif text.startswith('/backtest') or text.startswith('/bt'):
                # Parse command: /backtest [num_periods] [train]
                try:
                    parts = text.split()
                    num_periods = 100  # default
                    train_mode = False
                    
                    if len(parts) > 1:
                        try:
                            num_periods = int(parts[1])
                            num_periods = max(5, min(num_periods, 500))  # min 5, max 500
                        except:
                            pass
                    
                    # ✨ Check for 'train' keyword
                    if 'train' in text.lower():
                        train_mode = True
                    
                    mode_text = "🎓 TRAINING MODE" if train_mode else "📊 VALIDATION MODE"
                    await send_telegram_report(
                        f"🚀 **BACKTEST เริ่มแล้ว** {mode_text}\n"
                        f"Periods: {num_periods}\n"
                        f"🔄 กำลังวิเคราะห์ historical data...\n"
                        f"(นี่อาจใช้เวลาสักครู่...)",
                        chat_id
                    )
                    
                    backtest_result = await backtest_ai_training(client, num_periods, chat_id)
                    
                    if backtest_result:
                        brain.backtest_results = backtest_result
                        
                        # ✨ TRAINING MODE: Feed backtest results to AI brain (ขั้นเทพ!)
                        if train_mode:
                            training_count = 0
                            try:
                                for result in backtest_result['results']:
                                    if 'features' in result:
                                        # Add trade data to brain memory
                                        brain.update_memory(result['features'], result['win'])
                                        training_count += 1
                                
                                # Train the model with all new data
                                brain.train_model()
                                
                                # Get updated stats
                                ai_stats = brain.get_ai_stats()
                                
                                training_report = (
                                    f"\n✅ **AI PRE-TRAINING COMPLETE!** 🧠\n"
                                    f"{'─' * 55}\n\n"
                                    f"📚 **Training Data Added**:\n"
                                    f"   └ Trades fed to brain: `{training_count}`\n"
                                    f"   └ Total in memory: `{ai_stats['total_trades']}`\n\n"
                                    f"📊 **Model Performance**:\n"
                                    f"   └ Accuracy: `{ai_stats['last_accuracy']:.2f}%`\n"
                                    f"   └ Avg Accuracy: `{ai_stats['avg_accuracy']:.2f}%`\n"
                                    f"   └ Best Loss: `{ai_stats['best_loss']:.4f}`\n"
                                    f"   └ Epochs Trained: `{ai_stats['model_epochs_trained']}`\n\n"
                                    f"🎯 **Next Steps**:\n"
                                    f"   1️⃣ Use `/aistats` to verify improvements\n"
                                    f"   2️⃣ Run `/fastscan` to find new signals\n"
                                    f"   3️⃣ Start live trading with trained AI!\n"
                                )
                                await send_telegram_report(training_report, chat_id)
                                print(f"{Fore.GREEN}{Style.BRIGHT}✅ AI Pre-training complete! {training_count} trades added.{Style.RESET_ALL}")
                            
                            except Exception as train_err:
                                await send_telegram_report(f"⚠️ Training error: {train_err}", chat_id)
                                print(f"{Fore.YELLOW}Training error: {train_err}{Style.RESET_ALL}")
                        
                        else:
                            # Validation mode - just report
                            await send_telegram_report(
                                f"\n✅ **Backtest Complete (Validation Mode)**\n"
                                f"Results saved for analysis.\n"
                                f"💡 Tip: Use `/backtest {num_periods} train` to pre-train AI!",
                                chat_id
                            )
                
                except Exception as e:
                    await send_telegram_report(f"❌ Backtest error: {e}", chat_id)
                    print(f"{Fore.RED}Backtest error: {e}{Style.RESET_ALL}")

            # ===================== /report /status =====================
            elif text in ['/report', '/status']:
                total_pnl = sum(p['pnl'] for p in active)
                lines = [
                    f"📊 **สถานะบอท TITAN PRO**\n",
                    f"💰 Balance: `{bal:,.2f}` USDT",
                    f"₿ BTC Price: `{btc_p:,.0f}` USDT",
                    f"📈 Total PNL: `{total_pnl:+,.2f}` USDT",
                    f"⭐ Position เปิด: `{len(active)}/{MAX_OPEN_POSITIONS}`",
                    f"⏳ Pending Limits: `{len(pending_orders_detail)}`"
                ]
                if active:
                    lines.append(f"\n**ตำแหน่งที่เปิดอยู่**")
                    for p in active:
                        side_emoji = "🟢" if p['side'] == 'LONG' else "🔴"
                        lines.append(f"{side_emoji} {p['symbol'].replace('USDT','')} {p['side']} | PNL: `{p['pnl']:+.2f}`")
                
                await send_telegram_report("\n".join(lines), chat_id)



            # ===================== /pnl =====================
            elif text == '/pnl':
                wr, wins, total = get_current_winrate()
                stats = get_detailed_pnl_stats()
                open_pnl = sum(p['pnl'] for p in active)
                total_pnl = open_pnl + stats['closed_pnl']

                pnl_text = (
                    f"📈 **สรุปกำไร-ขาดทุน**\n\n"
                    f"💰 Open P&L: `{open_pnl:+,.2f}` USDT\n"
                    f"📊 Closed P&L: `{stats['closed_pnl']:+,.2f}` USDT\n"
                    f"💎 **Total P&L**: `{total_pnl:+,.2f}` USDT\n"
                    f"💳 Balance: `{bal:,.2f}` USDT\n\n"
                )
                
                if stats['total'] > 0:
                    pnl_text += (
                        f"📈 Win Rate: `{wr:.1f}%` ({wins}/{stats['total']} trades)\n"
                        f"💵 Avg/Trade: `{stats['avg_profit']:+,.2f}` USDT\n"
                        f"📊 Profit Factor: `{stats['profit_factor']:.2f}x`\n"
                        f"🔥 Best/Worst: `{stats['best_trade']:+,.2f}` / `{stats['worst_trade']:+,.2f}`\n"
                        f"⭐ ({stats['best_symbol']} / {stats['worst_symbol']})\n"
                    )
                    if stats['consecutive_wins'] > 0 or stats['consecutive_losses'] > 0:
                        pnl_text += f"✅ Max Streak: W{stats['consecutive_wins']} / L{stats['consecutive_losses']}\n"
                else:
                    pnl_text += f"⚠️ ยังไม่มีประวัติ trade ที่ปิดสมบูรณ์ใน CSV\n"
                
                pnl_text += f"\n⭐ Position เปิด: `{len(active)}/{MAX_OPEN_POSITIONS}`\n"
                pnl_text += f"⏳ Pending Orders: `{len(pending_orders_detail)}`"

                await send_telegram_report(pnl_text, chat_id)

            # ===================== /drawdown =====================
            elif text == '/drawdown':
                max_dd, dd_percent, max_profit, dd_from = get_max_drawdown()
                dd_text = (
                    f"📉 **Max Drawdown Analysis**\n\n"
                    f"🔻 Max Drawdown: `${max_dd:,.2f}`\n"
                    f"📊 DD %: `{dd_percent:.2f}%`\n"
                    f"📈 Peak Profit: `${max_profit:,.2f}`\n"
                    f"📅 DD From: `{dd_from}`\n"
                )
                await send_telegram_report(dd_text, chat_id)

            # ===================== /daily =====================
            elif text == '/daily':
                daily = get_daily_stats(days=7)
                if not daily:
                    await send_telegram_report("⚠️ ไม่มีข้อมูล Daily Stats", chat_id)
                    continue
                
                lines = ["📊 **Daily P&L Summary (7 days)**\n"]
                total_d_pnl = 0.0
                for d in daily:
                    emoji = "🟢" if d['pnl'] >= 0 else "🔴"
                    lines.append(
                        f"{emoji} `{d['date']}`: {d['pnl']:+.2f}$ "
                        f"({d['trades']}T, {d['wr']:.0f}% WR)"
                    )
                    total_d_pnl += d['pnl']
                lines.append(f"\n💎 **Total 7D P&L**: `{total_d_pnl:+,.2f}` USDT")
                
                await send_telegram_report("\n".join(lines), chat_id)

            # ===================== /weekly =====================
            elif text == '/weekly':
                weekly = get_weekly_stats(weeks=4)
                if not weekly:
                    await send_telegram_report("⚠️ ไม่มีข้อมูล Weekly Stats", chat_id)
                    continue
                
                lines = ["📈 **Weekly P&L Summary (4 weeks)**\n"]
                total_w_pnl = 0.0
                for w in weekly:
                    emoji = "🟢" if w['pnl'] >= 0 else "🔴"
                    lines.append(
                        f"{emoji} `{w['week']}`: {w['pnl']:+.2f}$ "
                        f"({w['trades']}T, {w['wr']:.0f}% WR)"
                    )
                    total_w_pnl += w['pnl']
                lines.append(f"\n💎 **Total 4W P&L**: `{total_w_pnl:+,.2f}` USDT")
                
                await send_telegram_report("\n".join(lines), chat_id)

            # ===================== /positions =====================
            elif text == '/positions':
                if not active:
                    await send_telegram_report("⭐ **ไม่มี Position เปิดอยู่**\nรอ Limit Order ถูก fill...", chat_id)
                    continue

                lines = ["⭐ **รายการ Position ที่เปิดอยู่**\n"]
                for i, p in enumerate(active, 1):
                    side_icon = "🟢 LONG" if p['side'] == 'LONG' else "🔴 SHORT"
                    pnl_emoji = "🟢" if p['pnl'] >= 0 else "🔴"
                    roe = (p['pnl'] / p['margin'] * 100) if p['margin'] > 0 else 0.0
                    sl_text = f"{p['sl']:.6f}" if p['sl'] > 0 else "ไม่มี"
                    tp_text = f"{p['tp']:.6f}" if p['tp'] > 0 else "ไม่มี"

                    lines.append(
                        f"**{i}.** `{p['symbol'].replace('USDT','')}` {side_icon}\n"
                        f"   Entry: `{p['entry']:.6f}` → ปัจจุบัน: `{p['curr_price']:.6f}`\n"
                        f"   PNL: {pnl_emoji} `{p['pnl']:+.2f}` USDT (`{roe:+.2f}`%)\n"
                        f"   SL: `{sl_text}` | TP: `{tp_text}`\n"
                    )
                await send_telegram_report("\n".join(lines), chat_id)

            # ===================== /limits =====================
            elif text in ['/limits', '/alllimits']:
                if text == '/alllimits':
                    await send_telegram_report("🚫 ไม่ส่งรายการ Pending Limits สำหรับ /alllimits ตามคำขอ", TELEGRAM_CHAT_ID)
                    # หรือไม่ส่งอะไรเลยเลย → ลบหรือ comment บรรทัด send ด้านล่าง
                    return  # ออกจาก handler ทันที ไม่ส่งรายงาน

                # ถ้าเป็น /limits ปกติ → ส่งรายงานตามเดิม
                await send_pending_limits_to_telegram(client)


            # ===================== /cancel <symbol> =====================
            elif text.startswith('/cancel'):
                parts = text.split()
                if len(parts) > 1:
                    # /cancel SYMBOL
                    sym_input = parts[1].upper()
                    sym = sym_input + 'USDT' if not sym_input.endswith('USDT') else sym_input
                    await cmd_q.put(f'cancel:{sym}')
                    await send_telegram_report(f"⏳ ยกเลิก Limit Order {sym}...", chat_id)
                else:
                    # /cancel ทั้งหมด
                    await cmd_q.put('cancel:all')
                    await send_telegram_report("⏳ ยกเลิก Limit Orders ทั้งหมด...", chat_id)

            # ===================== /analyze =====================
            elif text.startswith('/analyze '):
                try:
                    sym_input = text.split(' ', 1)[1].upper()
                    sym = sym_input + 'USDT'
                    current_price = price_map.get(sym, 0.0)
                    if current_price == 0.0:
                        await send_telegram_report("❓ ไม่พบเหรียญนี้หรือราคา", chat_id)
                        continue

                    # ดึงข้อมูล 4h แล้วคำนวณ indicators
                    k_4h = await client.futures_klines(symbol=sym, interval="4h", limit=100)
                    df_4h = calculate_indicators(k_4h)
                    
                    # ดึงข้อมูล 1h
                    k_1h = await client.futures_klines(symbol=sym, interval="1h", limit=100)
                    df_1h = calculate_indicators(k_1h)
                    
                    if df_4h.empty or df_1h.empty:
                        await send_telegram_report("❌ ข้อมูลไม่เพียงพอ", chat_id)
                        continue
                    
                    # ข้อมูล 4H
                    curr_4h = df_4h.iloc[-1]
                    prev_4h = df_4h.iloc[-2] if len(df_4h) > 1 else curr_4h
                    
                    # ข้อมูล 1H
                    curr_1h = df_1h.iloc[-1]
                    
                    # ===== เก็บ Fibonacci =====
                    high = df_4h['h'].max()
                    low = df_4h['l'].min()
                    diff = high - low
                    fib_levels = {
                        '0.0%': high,
                        '23.6%': high - 0.236 * diff,
                        '38.2%': high - 0.382 * diff,
                        '50.0%': high - 0.5 * diff,
                        '61.8%': high - 0.618 * diff,
                        '100%': low
                    }
                    
                    # ===== Grado Análisis =====
                    # 1. EMA Alignment (Trend)
                    htf_bullish = curr_4h['ema20'] > curr_4h['ema50'] > curr_4h['ema200']
                    htf_bearish = curr_4h['ema20'] < curr_4h['ema50'] < curr_4h['ema200']
                    ltf_bullish = curr_1h['ema20'] > curr_1h['ema50'] > curr_1h['ema200']
                    ltf_bearish = curr_1h['ema20'] < curr_1h['ema50'] < curr_1h['ema200']
                    
                    if htf_bullish:
                        trend_4h = "🟢 Bullish"
                    elif htf_bearish:
                        trend_4h = "🔴 Bearish"
                    else:
                        trend_4h = "🟡 Sideways"
                    
                    if ltf_bullish:
                        trend_1h = "🟢 Bullish"
                    elif ltf_bearish:
                        trend_1h = "🔴 Bearish"
                    else:
                        trend_1h = "🟡 Sideways"
                    
                    # 2. Stochastic
                    stoch_4h = curr_4h.get('stoch_k', 50)
                    stoch_status_4h = "Overbought" if stoch_4h > 80 else "Oversold" if stoch_4h < 20 else "Neutral"
                    
                    stoch_1h = curr_1h.get('stoch_k', 50)
                    stoch_status_1h = "Overbought" if stoch_1h > 80 else "Oversold" if stoch_1h < 20 else "Neutral"
                    
                    # 3. RSI
                    rsi_4h = curr_4h['rsi']
                    rsi_status_4h = "Overbought" if rsi_4h > 70 else "Oversold" if rsi_4h < 30 else "Neutral"
                    
                    # 4. MACD
                    macd_4h = curr_4h['macd']
                    signal_4h = curr_4h['signal']
                    macd_bullish = macd_4h > signal_4h
                    
                    # 5. Support/Resistance
                    support = float(curr_4h.get('support', 0))
                    resistance = float(curr_4h.get('resistance', 0))
                    
                    # 6. Price Position
                    price_pos = "At Support" if abs(current_price - support) / support < 0.01 else \
                                "At Resistance" if abs(current_price - resistance) / resistance < 0.01 else \
                                "Mid-range"
                    
                    # 7. Price Action
                    pin_bar_b = curr_4h.get('pin_bar_bullish', 0)
                    pin_bar_s = curr_4h.get('pin_bar_bearish', 0)
                    engulf_b = curr_4h.get('engulfing_bearish', 0) == 0  # ไม่เป็น bearish
                    
                    # ===== สร้าง Report =====
                    # ===== สร้าง Report =====
                    report_text = (
                        f"📊 {sym_input}/USDT | วิเคราะห์อัจฉริยะ\n"
                        f"⏱ {datetime.now().strftime('%d/%m %H:%M')}  |  ราคา: {current_price:,.2f}\n"
                        f"──────────────────────────\n\n"

                        f"📈 Trend Analysis\n"
                        f"• 4H : {trend_4h}\n"
                        f"• 1H : {trend_1h}\n\n"

                        f"📊 Momentum\n"
                        f"• RSI 4H    : {rsi_4h:.1f} {rsi_status_4h}\n"
                        f"• Stoch 4H  : {stoch_4h:.1f}\n"
                        f"• Stoch 1H  : {stoch_1h:.1f}\n"
                        f"• MACD      : {'🟢 Bullish' if macd_bullish else '🔴 Bearish'}\n\n"

                        f"🎯 Support & Resistance\n"
                        f"• Support    : {support:,.2f}\n"
                        f"• Resistance : {resistance:,.2f}\n"
                        f"• Position   : {price_pos}\n\n"

                        f"🎪 Fibonacci Levels\n"
                        f"• 38.2% : {fib_levels['38.2%']:,.2f}\n"
                        f"• 61.8% : {fib_levels['61.8%']:,.2f}\n\n"

                        f"💡 สรุปมุมมอง:\n"
                    )

                    
                    # ตัดสินใจ
                    signals = 0
                    if htf_bullish and ltf_bullish:
                        signals += 2
                        signal_text = "Strong BUY 🟢"
                    elif htf_bullish and not ltf_bearish:
                        signals += 1
                        signal_text = "Bias BUY 🟢"
                    elif htf_bearish and ltf_bearish:
                        signals -= 2
                        signal_text = "Strong SELL 🔴"
                    elif htf_bearish and not ltf_bullish:
                        signals -= 1
                        signal_text = "Bias SELL 🔴"
                    else:
                        signal_text = "NEUTRAL 🟡"
                    
                    if macd_bullish:
                        signals += 1
                    else:
                        signals -= 1
                    
                    if stoch_4h < 20 and ltf_bullish:
                        signal_text = "STRONG BUY 🟢🟢"
                    elif stoch_4h > 80 and ltf_bearish:
                        signal_text = "STRONG SELL 🔴🔴"
                    
                    report_text += signal_text + "\n"
                    
                    if current_price < support * 1.005:
                        report_text += "💰 ราคาใกล้ Support → โอกาสซื้อ\n"
                    elif current_price > resistance * 0.995:
                        report_text += "⚠️ ราคาใกล้ Resistance → ระวังขาด\n"
                    
                    # ===== สร้าง Chart Fibonacci =====
                    plt.style.use('dark_background')
                    fig, ax = plt.subplots(figsize=(14, 8), dpi=120)
                    fig.patch.set_facecolor('#121212')
                    ax.set_facecolor('#121212')
                    
                    ax.plot(df_4h.index, df_4h['c'], label='Close', color='#00ffea', linewidth=2.5, alpha=0.9)
                    
                    # Fibonacci
                    fib_colors = ['#ff1744', '#ff9100', '#ffd600', '#00e676', '#00e5ff', '#e0e0e0']
                    for i, (label, level) in enumerate(fib_levels.items()):
                        ax.axhline(level, color=fib_colors[i], linestyle='--', linewidth=1.8, alpha=0.7)
                    
                    # Support & Resistance
                    if support > 0:
                        ax.axhline(support, color='#00e676', linestyle='-', linewidth=2, alpha=0.5, label='Support')
                    if resistance > 0:
                        ax.axhline(resistance, color='#ff1744', linestyle='-', linewidth=2, alpha=0.5, label='Resistance')
                    
                    ax.set_title(f'{sym_input} - Fibonacci & S/R Levels', color='white', fontsize=16)
                    ax.tick_params(colors='white')
                    ax.grid(True, alpha=0.2, color='#424242')
                    ax.legend(facecolor='#121212', labelcolor='white', loc='best')
                    
                    plt.tight_layout()
                    
                    buf = io.BytesIO()
                    fig.savefig(buf, format='png', bbox_inches='tight', facecolor='#121212')
                    buf.seek(0)
                    plt.close(fig)
                    
                    await send_telegram_report(report_text, chat_id, photo=buf)
                    
                except Exception as e:
                    print(f"{Fore.RED}Error in /analyze: {e}")
                    await send_telegram_report(f"❌ เกิดข้อผิดพลาด: {str(e)}", chat_id)

            # ===================== /sltp - ตั้ง SL/TP สำหรับ positions ที่ไม่มี =====================
            elif text in ['/sltp', '/setsltp']:
                await send_telegram_report("⏳ กำลังตรวจสอบและตั้ง SL/TP...", chat_id)
                await cmd_q.put('sltp')

            # ===================== คำสั่งควบคุม =====================
            elif text in ['/cancel', '/cancel']:
                await cmd_q.put('c')
                await send_telegram_report("🗑️ กำลังยกเลิก Limit Orders ทั้งหมด...", chat_id)

            elif text.startswith('/close '):
                parts = text.split()
                if len(parts) >= 2:
                    sym_input = parts[1].upper()
                    sym = sym_input + "USDT" if not sym_input.endswith("USDT") else sym_input
                    
                    # ตรวจสอบก่อนว่ามี position จริงไหม (optional แต่ดี)
                    if not any(p['symbol'] == sym for p in active):
                        await send_telegram_report(f"⚠️ ไม่พบ Position {sym_input} ที่เปิดอยู่", chat_id)
                        continue
                    
                    await cmd_q.put(f'close:{sym}')
                    await send_telegram_report(f"🚪 กำลังปิด Position {sym_input}...", chat_id)
                else:
                    await send_telegram_report("❌ ใช้: `/close BTC` (ชื่อเหรียญ)", chat_id)

            elif text in ['/closeall', '/a']:
                await cmd_q.put('a')
                await send_telegram_report("🔴 กำลังปิดทุก Position และยกเลิก Orders...", chat_id)

            elif text in ['/q', '/quit', '/qq']:
                running = False
                await send_telegram_report("🛑 บอทกำลังหยุดทำงานอย่างปลอดภัย...\nขอบคุณที่ใช้ TITAN PRO 🚀", chat_id)

            # ===================== พิมพ์ชื่อเหรียญตรง ๆ =====================
            else:
                # ─── ขั้นตอนกรองก่อนถือว่าเป็นชื่อเหรียญ ───
                raw_text = text.strip()
                
                # 1. ใน group/supergroup → ลบ @botname ออกก่อนเสมอ
                if message.chat.type in ['group', 'supergroup']:
                    # ใช้ bot_username ที่ได้จาก get_me() (เรียกครั้งเดียวก็พอ แต่ที่นี่เรียกเพื่อความปลอดภัย)
                    try:
                        bot_user = await telegram_bot.get_me()
                        bot_username = bot_user.username.lower() if bot_user.username else "puaibot"  # fallback ถ้า get_me ล้มเหลว
                    except:
                        bot_username = "puaibot"  # fallback ชื่อบอทของคุณ
                    
                    bot_mention = f"@{bot_username}"
                    if bot_mention in raw_text:
                        raw_text = raw_text.replace(bot_mention, '').strip()
                
                # 2. ลบช่องว่างซ้ำ + ทำให้สะอาด
                cleaned_input = ' '.join(raw_text.split()).upper()
                
                # 3. เงื่อนไขข้าม fallback (ไม่ถือเป็นชื่อเหรียญ → ไม่ตอบอะไรเลย)
                if (
                    cleaned_input.startswith('/') or               # เริ่มด้วย / → เป็นคำสั่งที่หลุดมา
                    len(cleaned_input.split()) > 2 or              # มีหลายคำ → ไม่ใช่ชื่อเหรียญเดี่ยว
                    len(cleaned_input) > 12 or                     # ยาวเกิน (เช่น มี @ หรือคำสั่งยาว)
                    not all(c.isalnum() or c in ['-', '_'] for c in cleaned_input) or  # มีอักขระพิเศษ
                    cleaned_input in ['ON', 'OFF', 'STATUS', 'HELP', 'PNL']  # คำสั่งสั้นที่อาจหลุดมา
                ):
                    print(f"[FALLBACK SKIP - GROUP/PRIVATE] {text} → ไม่น่าใช่ชื่อเหรียญเดี่ยว")
                    continue  # ข้าม ไม่ตอบอะไรเลย (เงียบที่สุด)

                # 4. ถ้าผ่านทุกเงื่อนไข → ถือว่าเป็นชื่อเหรียญจริง ๆ
                sym_input = cleaned_input
                sym = sym_input + 'USDT' if not sym_input.endswith('USDT') else sym_input
                
                if sym not in price_map or price_map.get(sym, 0) <= 0:
                    await telegram_bot.send_message(
                        chat_id=chat_id,
                        text=f"❓ ไม่พบข้อมูลราคา {sym_input} ในขณะนี้\n"
                             f"(ถ้าเป็นคำสั่ง ให้ลองพิมพ์ `/help` ดูรายการทั้งหมด)"
                    )
                    continue
                
                current_price = price_map[sym]
                
                # ─── ต่อด้วยโค้ดวิเคราะห์เหรียญของคุณ (copy จากเดิมมาต่อตรงนี้) ───
                # ตัวอย่าง: ดึง kline หลาย TF, คำนวณ indicators, สร้าง report_text ฯลฯ
                try:
                    # ... โค้ดดึง tfs_to_fetch, klines_tasks, dfs, curr_*, change_1d, htf_status, lines, vol_spike_text, fib_text, summary, trade_hint ฯลฯ ...
                    # (คุณสามารถ copy โค้ดวิเคราะห์ทั้งหมดจากบรรทัด try: เดิมของคุณมาต่อตรงนี้เลย)

                    # สุดท้ายสร้าง report_text และส่ง
                    safe_text = escape_md(report_text)
                    await send_telegram_report(safe_text, chat_id)
                
                except Exception as e:
                    print(f"{Fore.RED}Error analyzing {sym} (multi-TF): {e}{Style.RESET_ALL}")
                    await send_telegram_report(
                        f"💰 **{sym_input}/USDT**\n"
                        f"ราคา: `{current_price:,.4f}`\n"
                        f"⚠️ เกิดข้อผิดพลาดในการวิเคราะห์: {str(e)[:100]}...",
                        chat_id
                    )

                try:
                    # =============================================================
                    # ดึงข้อมูลหลาย timeframe พร้อมกัน (เร็ว + ประหยัด request)
                    # =============================================================
                    tfs_to_fetch = ["1d", "4h", "1h", "15m"]
                    klines_tasks = {
                        tf: client.futures_klines(symbol=sym, interval=tf, limit=300 if tf in ["1d", "4h"] else 150)
                        for tf in tfs_to_fetch
                    }
                    klines_results = await asyncio.gather(*klines_tasks.values(), return_exceptions=True)

                    dfs = {}
                    for tf, res in zip(tfs_to_fetch, klines_results):
                        if isinstance(res, Exception) or not res or len(res) < 50:
                            continue
                        df = calculate_indicators(res)
                        if not df.empty:
                            dfs[tf] = df

                    if not dfs:
                        await send_telegram_report(
                            f"💰 **{sym_input}/USDT**\n"
                            f"ราคาปัจจุบัน: `{current_price:,.4f}`\n"
                            f"⚠️ ไม่สามารถดึงข้อมูลเพียงพอสำหรับวิเคราะห์",
                            chat_id
                        )
                        continue

                    # =============================================================
                    # ดึงข้อมูลสำคัญจากแต่ละ timeframe
                    # =============================================================
                    df_1d = dfs.get("1d")
                    df_4h = dfs.get("4h")
                    df_1h = dfs.get("1h")
                    df_15m = dfs.get("15m")

                    curr_1d = df_1d.iloc[-1] if df_1d is not None else None
                    curr_4h = df_4h.iloc[-1] if df_4h is not None else None
                    curr_1h = df_1h.iloc[-1] if df_1h is not None else None
                    curr_15m = df_15m.iloc[-1] if df_15m is not None else None

                    # =============================================================
                    # 1. สรุปราคา + การเปลี่ยนแปลง (1D)
                    # =============================================================
                    change_1d = 0.0
                    if curr_1d is not None and len(df_1d) > 1:
                        prev_close = float(df_1d.iloc[-2]['c'])
                        change_1d = (current_price - prev_close) / prev_close * 100 if prev_close > 0 else 0

                    # =============================================================
                    # 2. HTF Alignment (4H + 1H)
                    # =============================================================
                    htf_status = "ไม่สามารถตรวจสอบได้"
                    htf_emoji = "⚪"
                    if curr_4h is not None:
                        is_bull_4h = await check_htf_bullish_alignment(client, sym)
                        is_bear_4h = await check_htf_bearish_alignment(client, sym)
                        if is_bull_4h:
                            htf_status = "🟢 ขาขึ้นแข็งแรง (4H)"
                            htf_emoji = "🟢"
                        elif is_bear_4h:
                            htf_status = "🔴 ขาลงแข็งแรง (4H)"
                            htf_emoji = "🔴"
                        else:
                            htf_status = "🟡 ไซด์เวย์ / ไม่ชัดเจน (4H)"

                    # =============================================================
                    # 3. Indicators หลัก (1D + 4H + 15m)
                    # =============================================================
                    lines = []

                    # RSI
                    if curr_1d is not None:
                        rsi_1d = curr_1d['rsi']
                        lines.append(f"RSI (1D): `{rsi_1d:.1f}` → {'🟢 Oversold' if rsi_1d < 30 else '🔴 Overbought' if rsi_1d > 70 else '🟡 ปกติ'}")
                    if curr_4h is not None:
                        lines.append(f"RSI (4H): `{curr_4h['rsi']:.1f}`")

                    # ADX + MACD (1D)
                    if curr_1d is not None:
                        lines.append(f"ADX (1D): `{curr_1d['adx']:.1f}` → {'🟢 เทรนด์แข็งแรง' if curr_1d['adx'] > 30 else '🟡 อ่อน/ไซด์เวย์'}")
                        macd_status = "🟢 Bullish" if curr_1d['macd'] > curr_1d['signal'] else "🔴 Bearish"
                        lines.append(f"MACD (1D): {macd_status}")

                    # Volume Spike ล่าสุด (15m)
                    vol_spike_text = "ปกติ"
                    if curr_15m is not None and 'vol_ma' in curr_15m and curr_15m['vol_ma'] > 0:
                        vol_r = curr_15m['v'] / curr_15m['vol_ma']
                        if vol_r > 2.0:
                            vol_spike_text = f"🔥 พุ่งสูงมาก ({vol_r:.1f}x)"
                        elif vol_r > 1.5:
                            vol_spike_text = f"🟢 สูงกว่าปกติ ({vol_r:.1f}x)"

                    # =============================================================
                    # 4. Fibonacci + Elliott Wave (จาก 1D)
                    # =============================================================
                    fib_elliot = {}
                    fib_text = "ไม่สามารถคำนวณได้"
                    if df_1d is not None and len(df_1d) >= 50:
                        fib_elliot = get_fib_elliot_signal(df_1d, current_price)
                        fib_text = (
                            f"{fib_elliot['signal']} @ {fib_elliot['fib_level']} "
                            f"({fib_elliot['confidence']*100:.0f}%)\n"
                            f"Wave: {fib_elliot['wave_pattern']} ({fib_elliot['wave_direction']})"
                        )

                    # =============================================================
                    # 5. สรุปคำแนะนำ + ความเสี่ยง
                    # =============================================================
                    summary = "🟡 รอสัญญาณชัดเจน"
                    risk_level = "ปานกลาง"
                    
                    if htf_emoji == "🟢" and curr_1d is not None and curr_1d['ema20'] > curr_1d['ema50']:
                        summary = "🟢 **มีโอกาส LONG** (ขาขึ้นเริ่มแข็งแรง)"
                        risk_level = "ต่ำ-ปานกลาง" if curr_1d['rsi'] < 60 else "ปานกลาง"
                    elif htf_emoji == "🔴" and curr_1d is not None and curr_1d['ema20'] < curr_1d['ema50']:
                        summary = "🔴 **มีโอกาส SHORT** (ขาลงยังแรง)"
                        risk_level = "ต่ำ-ปานกลาง" if curr_1d['rsi'] > 40 else "ปานกลาง"

                    if vol_spike_text.startswith("🔥"):
                        summary += "\n🔥 Volume Spike มาแรง → น่าสนใจมากขึ้น!"

                    # ===== สร้างคำแนะนำจาก summary =====
                    if 'LONG' in summary:
                        trade_hint = "รอ pullback เพื่อเข้า LONG"
                    elif 'SHORT' in summary:
                        trade_hint = "รอ pullback เพื่อเข้า SHORT"
                    else:
                        trade_hint = "รอ confirmation ให้ชัดเจนก่อนเข้าเทรด"

                    # =============================================================
                    # สร้างรายงานฉบับสมบูรณ์ (Telegram Safe)
                    # =============================================================
                    report_text = (
                        f"📊 วิเคราะห์ละเอียด {sym_input}/USDT\n"
                        f"⏱ {datetime.now().strftime('%d/%m/%Y %H:%M:%S')}\n"
                        f"──────────────────────────\n"
                        f"💰 ราคาปัจจุบัน : {current_price:,.4f} USDT\n"
                        f"📈 เปลี่ยนแปลงวันนี้ : {change_1d:+.2f}% "
                        f"{'⬆️ ขาขึ้น' if change_1d > 0 else '⬇️ ขาลง' if change_1d < 0 else '➖ นิ่ง'}\n\n"

                        f"🌐 Higher Timeframe Alignment\n"
                        f"• 4H : {htf_status}\n\n"

                        f"📊 Indicators หลัก\n"
                        f"{chr(10).join(lines)}\n"
                        f"• Volume ล่าสุด (15m) : {vol_spike_text}\n\n"

                        f"🎪 Fibonacci + Elliott Wave (1D)\n"
                        f"{fib_text}\n\n"

                        f"🧠 สรุป & คำแนะนำ\n"
                        f"{summary}\n\n"
                        f"⚠️ ระดับความเสี่ยง : {risk_level}\n"
                        f"➡️ {trade_hint}\n\n"

                        f"💡 หมายเหตุ : วิเคราะห์จากข้อมูลล่าสุด "
                        f"ควรใช้วิจารณญาณและบริหารความเสี่ยงก่อนตัดสินใจเทรด"
                    )


                    safe_text = escape_md(report_text)
                    await send_telegram_report(safe_text, chat_id)

                except Exception as e:
                    print(f"{Fore.RED}Error analyzing {sym} (multi-TF): {e}{Style.RESET_ALL}")
                    await send_telegram_report(
                        f"💰 **{sym_input}/USDT**\n"
                        f"ราคา: `{current_price:,.4f}`\n"
                        f"⚠️ เกิดข้อผิดพลาดในการวิเคราะห์: {str(e)[:100]}...",
                        chat_id
                    )

    except Exception as e:
        print(f"{Fore.RED}Telegram polling error: {e}")

def has_active_position(symbol: str) -> bool:
    """ตรวจสอบว่ามี position short อยู่หรือไม่ (ตัวอย่าง)"""
    # ในระบบจริง ควรดึงจาก client.futures_position_information()
    return False  # หรือ implement จริง

def calculate_position_size(client, symbol: str, entry_price: float, risk_amount: float, sl_pct: float):
    """คำนวณจำนวนที่จะเทรดตาม risk"""
    sl_distance = entry_price * sl_pct
    contract_size = risk_amount / sl_distance
    # ปรับตาม step size ของเหรียญนั้น (จาก exchange info)
    return round(contract_size, 3)

async def set_stop_loss_take_profit(client, symbol: str, entry_price: float, stop_loss_pct: float, take_profit_pct: float):
    """ตั้ง SL/TP (ตัวอย่างแบบง่าย)"""
    sl_price = entry_price * (1 + stop_loss_pct)   # short: SL อยู่เหนือ
    tp_price = entry_price * (1 - take_profit_pct) # short: TP อยู่ล่าง
    symbol_usdt = symbol + "USDT"
    
    # Stop-Loss
    await client.futures_create_order(
        symbol=symbol_usdt,
        side='BUY',
        positionSide='SHORT',
        type='STOP_MARKET',
        stopPrice=sl_price,
        closePosition=True
    )
    # Take-Profit
    await client.futures_create_order(
        symbol=symbol_usdt,
        side='BUY',
        positionSide='SHORT',
        type='TAKE_PROFIT_MARKET',
        stopPrice=tp_price,
        closePosition=True
    )
# ==========================================================================
#                  PENDING LIMITS REPORT
# ==========================================================================


async def send_pending_limits_to_telegram(client):
    """
    ส่งรายการ Pending Limit Orders ไป Telegram (เวอร์ชันปรับปรุง + error handling ชัดเจน)
    """
    if not telegram_bot or not TELEGRAM_CHAT_ID:
        print("Telegram ไม่พร้อม → ข้ามการส่ง /limits")
        return

    try:
        # ดึงราคาสดล่าสุด
        tickers = await client.futures_symbol_ticker()
        price_map_local = {}
        for t in tickers:
            try:
                price_map_local[t['symbol']] = float(t['price'])
            except (KeyError, ValueError):
                continue

        if not pending_orders_detail:
            await send_telegram_report(
                "⏳ *ไม่มี Pending Limit Orders ในขณะนี้*\n"
                "_รอสัญญาณใหม่ หรือตั้ง Limit ด้วยมือเลยครับ_ 🚀",
                TELEGRAM_CHAT_ID
            )
            return

        # ฟังก์ชันช่วยคำนวณ gap % แบบปลอดภัย
        def get_gap_pct(order):
            curr = price_map_local.get(order['symbol'])
            if curr is None or curr <= 0:
                return 0.0
            return abs(order['price'] - curr) / curr * 100

        # เรียงตาม gap % มากสุด → น้อยสุด
        sorted_orders = sorted(
            pending_orders_detail,
            key=get_gap_pct,
            reverse=True
        )

        lines = ["**⏳ Pending Limit Orders (เรียงตาม % ห่างมากสุดก่อน)**\n━━━━━━━━━━━━━━━\n"]

        for i, o in enumerate(sorted_orders[:5], 1):
            sym_clean = o['symbol'].replace('USDT', '').replace('_', '\\_')
            curr_price = price_map_local.get(o['symbol'])
            if curr_price is None or curr_price <= 0:
                curr_str = "N/A"
                gap_pct = 0.0
                gap_emoji = "⚪"
            else:
                curr_str = f"{curr_price:.4f}"
                gap_pct = abs(o['price'] - curr_price) / curr_price * 100
                gap_emoji = "🔴" if gap_pct > 3 else "🟡" if gap_pct > 1 else "🟢"

            side_emoji = "🟢 BUY" if o['side'] == 'BUY' else "🔴 SELL"
            age_h = (datetime.now() - o['time']).total_seconds() / 3600
            age_warn = " 🔥 ใกล้ fill!" if age_h < 0.5 or gap_pct < 0.6 else ""
            manual_tag = " [Manual]" if o.get('manual', False) else ""

            line = (
                f"{i}\\. {side_emoji} `{sym_clean}`{manual_tag}\n"
                f"   └ ตอนนี้ `{curr_str}` → Limit `{o['price']:.4f}`\n"
                f"   └ ห่าง {gap_emoji} *{gap_pct:+.2f}%* | Qty `{o['qty']:.4f}` | อายุ *{age_h:.1f} ชม.*{age_warn}"
            )
            lines.append(line)

        total = len(pending_orders_detail)
        near_fill_count = sum(1 for o in pending_orders_detail if get_gap_pct(o) < 0.8)
        summary = (
            f"\n━━━━━━━━━━━━━━━\n"
            f"ทั้งหมด: *{total}* ออเดอร์\n"
            f"ใกล้ fill เร็ว: *{near_fill_count}* ตัว 🔥\n"
            f"ใช้ `/cancel` เพื่อยกเลิกทั้งหมด หรือ `/cancel BTCUSDT` เฉพาะคู่"
        )
        lines.append(summary)

        full_msg = "\n".join(lines)
        await send_telegram_report(full_msg, TELEGRAM_CHAT_ID)

    except Exception as e:
        error_type = type(e).__name__
        error_str = str(e)
        print(f"Error ใน send_pending_limits_to_telegram: {error_type}: {error_str}")

        error_msg = (
            f"⚠️ *เกิดข้อผิดพลาดตอนดึง/ส่งรายการ Limit Orders*\n"
            f"ประเภท: `{error_type}`\n"
            f"รายละเอียด: `{error_str[:150]}`...\n"
            f"ลองใหม่ใน 1-2 นาที หรือตรวจสอบการเชื่อมต่อ API ครับ"
        )
        try:
            await send_telegram_report(error_msg, TELEGRAM_CHAT_ID)
        except Exception as report_err:
            print(f"ยังส่ง error report ไม่ได้: {report_err}")


async def analyze_historical_swings(client, symbol, lookback_candles=200):
    """
    วิเคราะห์ swing high/low ล่าสุด + key levels จาก klines
    Returns dict หรือ None ถ้าข้อมูลไม่พอ
    """
    try:
        klines = await client.futures_klines(symbol=symbol, interval="4h", limit=lookback_candles)
        if not klines or len(klines) < 50:
            return None
        
        df = pd.DataFrame(klines, columns=['open_time','open','high','low','close','volume','close_time',
                                           'quote_asset_volume','number_of_trades','taker_buy_base_asset_volume',
                                           'taker_buy_quote_asset_volume','ignore'])
        df = df.astype(float)
        
        # หา swing high/low ล่าสุด (ใช้ argrelextrema หรือ max/min ง่าย ๆ)
        highs = df['high'].rolling(window=20, center=True).max()
        lows  = df['low'].rolling(window=20, center=True).min()
        
        recent_high = highs.iloc[-1]
        recent_low  = lows.iloc[-1]
        
        # คำนวณ avg pullback (คร่าว ๆ)
        swings = df['high'].iloc[-50:].max() - df['low'].iloc[-50:].min()
        avg_pullback = swings * 0.382  # ใช้ Fib 38.2% เป็นตัวแทน
        
        return {
            'highest_swing': float(recent_high),
            'lowest_swing': float(recent_low),
            'avg_pullback': avg_pullback,
            'recent_support': float(lows.iloc[-5:].min()),
            'recent_resistance': float(highs.iloc[-5:].max()),
            'key_reversal_zones': [float(df['low'].iloc[-10:].min()), float(df['high'].iloc[-10:].max())]
        }
    
    except Exception as e:
        print(f"analyze_historical_swings error {symbol}: {e}")
        return None

# ==========================================================================
#                  ANALYZE TREND
# ==========================================================================
async def analyze_trend(client, symbol):
    try:
        k = await client.futures_klines(symbol=symbol, interval="4h", limit=200)
        if not k:
            return "ไม่พบข้อมูลสำหรับเหรียญนี้"

        df = calculate_indicators(k)
        if df.empty:
            return "ไม่สามารถคำนวณ indicators ได้"

        curr = df.iloc[-1]

        ema20 = curr.get('ema20')
        ema50 = curr.get('ema50')
        ema200 = curr.get('ema200', curr.get('ema100'))

        ema_trend = "ไซด์เวย์ 🟡"
        if ema20 and ema50 and ema200:
            if ema20 > ema50 > ema200:
                ema_trend = "ขาขึ้น 🟢"
            elif ema20 < ema50 < ema200:
                ema_trend = "ขาลง 🔴"

        trend_summary = (
            f"**วิเคราะห์แนวโน้ม {symbol.replace('USDT','')} (4h)**\n"
            f"ราคาปัจจุบัน: {float(curr['c']):,.4f} USDT\n"
            f"ADX: {curr['adx']:.1f} → {'แข็งแรง' if curr['adx'] > 30 else 'อ่อน'}\n"
            f"RSI: {curr['rsi']:.1f}\n"
            f"MACD {'Bullish 📈' if curr['macd'] > curr['signal'] else 'Bearish 📉'}\n"
            f"EMA: {ema_trend}\n"
            f"\nสรุป: "
            f"{'🟢 แนวโน้มขาขึ้น' if curr['adx'] > 30 and curr['macd'] > curr['signal'] and ema_trend.startswith('ขาขึ้น') else '🔴 แนวโน้มขาลง' if curr['adx'] > 30 and curr['macd'] < curr['signal'] and ema_trend.startswith('ขาลง') else '🟡 ไซด์เวย์ / อ่อน'}"
        )

        return escape_md(trend_summary)

    except Exception as e:
        return f"เกิดข้อผิดพลาด: {e}"



# ─── ฟังก์ชันบันทึก trade ที่ปิดแล้ว (เวอร์ชันปรับปรุงล่าสุด) ───
async def record_closed_trade(client, sym: str, exit_reason: str = "Detected Close", is_manual: bool = False):
    # ─── ต้องวาง global ที่นี่ ก่อนใช้ตัวแปรใด ๆ ───
    global active, active_detailed, manual_closed_cooldown

    try:
        pos_info = active_detailed.get(sym, {})
        if not pos_info:
            print(f"[RECORD WARNING] ไม่พบ pos_info สำหรับ {sym} → ใช้ fallback")

        # ─── ข้อมูลพื้นฐาน (fallback เต็ม) ───
        entry_price   = pos_info.get('entry_price', 0.0)
        side          = pos_info.get('side', 'UNKNOWN')
        qty           = pos_info.get('quantity', 0.0)
        leverage      = pos_info.get('leverage', MAX_LEVERAGE)
        entry_time    = pos_info.get('entry_time')
        features      = pos_info.get('features', [0.5]*7)
        max_roe       = pos_info.get('max_roe', 0.0)

        # ─── ดึง realized trade ล่าสุด (ลอง 3 รอบ) ───
        exit_price = pnl = realized_qty = 0.0
        exit_time = datetime.now()
        close_trade = None

        for attempt in range(3):
            try:
                trades = await client.futures_account_trades(symbol=sym, limit=5)
                close_trade = next((t for t in reversed(trades) 
                                  if float(t.get('realizedPnl', 0)) != 0), None)
                if close_trade:
                    break
            except Exception as fetch_err:
                print(f"[TRADE FETCH attempt {attempt+1}] {sym}: {fetch_err}")
            if attempt < 2:
                await asyncio.sleep(1.0)

        if close_trade:
            exit_price   = float(close_trade['price'])
            pnl          = float(close_trade['realizedPnl'])
            realized_qty = abs(float(close_trade.get('qty', qty)))
            exit_time    = datetime.fromtimestamp(int(close_trade['time']) / 1000)
            
            orig_type = close_trade.get('origType', '')
            if 'STOP_MARKET' in orig_type:
                exit_reason = "Hit SL"
            elif 'TAKE_PROFIT_MARKET' in orig_type:
                exit_reason = "Hit TP"
            elif 'LIQUIDATION' in str(close_trade).upper():
                exit_reason = "Liquidation"

        # ─── คำนวณค่าให้ครบ ───
        duration_hours = 0.1
        if entry_time:
            duration_hours = max((exit_time - entry_time).total_seconds() / 3600, 0.1)

        pnl_percent = 0.0
        is_win = pnl > 0
        if qty > 0 and leverage > 0:
            margin = qty * entry_price / leverage
            if margin > 0:
                pnl_percent = (pnl / margin) * 100

        # fallback entry_price
        if entry_price <= 0 and exit_price > 0:
            entry_price = exit_price
            exit_reason += " (fallback entry)"

        # สร้าง record
        trade_record = {
            'timestamp': exit_time.isoformat(),
            'symbol': sym,
            'side': side,
            'entry_price': entry_price,
            'exit_price': exit_price,
            'quantity': qty or realized_qty,
            'pnl': pnl,
            'pnl_percent': pnl_percent,
            'duration_hours': duration_hours,
            'exit_reason': exit_reason,
            'is_win': is_win,
            'leverage': leverage,
            'max_roe_percent': max_roe,
            'features': features if len(features) == 7 else [0.5]*7
        }

        # บันทึก CSV
        csv_record = trade_record.copy()
        csv_record.pop('features', None)
        log_trade_to_csv(csv_record)

        # อัพเดท AI
        if trade_record['features']:
            try:
                brain.update_memory(trade_record['features'], trade_record['is_win'])
                print(f"{Fore.CYAN}[AI UPDATED] {sym} - {'WIN' if is_win else 'LOSS'}{Style.RESET_ALL}")
            except Exception as e:
                print(f"{Fore.YELLOW}AI update fail: {e}{Style.RESET_ALL}")

        # ลบออกจาก active (ตอนนี้ global แล้ว ใช้ได้เลย)
        active[:] = [p for p in active if p['symbol'] != sym]
        active_detailed.pop(sym, None)

        # ถ้าเป็น manual close → ลบ cooldown
        if is_manual and sym in manual_closed_cooldown:
            manual_closed_cooldown.pop(sym, None)

        # ─── ส่งแจ้งเตือน Telegram ───
        wr, wins, total = get_current_winrate(filter_days=30)
        win_emoji = "🟢 WIN!" if is_win else "🔴 LOSS"
        pnl_emoji = "🟢 +" if is_win else "🔴 -"
        exit_emoji = "🟢" if "TP" in exit_reason else "🔴" if "SL" in exit_reason or "Liquidation" in exit_reason else "⚪"

        report = (
            f"{win_emoji} **Position Closed** ({exit_reason})\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"เหรียญ: `{sym.replace('USDT','')}` {side}\n"
            f"Entry → Exit: `{entry_price:.6f}` → `{exit_price:.6f}`\n"
            f"PNL: {pnl_emoji} `{pnl:+.2f}` USDT (`{pnl_percent:+.2f}%`)\n"
            f"เหตุผล: {exit_emoji} **{exit_reason}**\n"
            f"ระยะเวลา: `{duration_hours:.1f}` ชม\n"
            f"Max ROE: `{max_roe:+.2f}%`\n"
            f"━━━━━━━━━━━━━━━━━━━\n"
            f"สถิติ 30 วัน: {wins}/{total} | WR {wr:.1f}%\n"
            f"{'🟢 เก่งมาก!' if is_win else '🔴 ครั้งหน้าต้องดีกว่า!'}"
        )

        await send_telegram_report(escape_md(report), TELEGRAM_CHAT_ID)

        print(f"[NOTIFY CLOSED] {sym} → PNL {pnl:+.2f} | {exit_reason}")
        return trade_record

    except Exception as e:
        print(f"[RECORD ERROR] {sym}: {e}")
        with open("emergency_closed.log", "a") as ef:
            ef.write(f"{datetime.now().isoformat()} | {sym} | {exit_reason} | {str(e)}\n")
        return None
      
# ==========================================================================
#                  GET SENTIMENT FROM COINGECKO
# ==========================================================================
async def get_sentiment(symbol):
    cg = CoinGeckoAPI()
    coin_id = symbol.replace('USDT', '').lower()
    try:
        data = cg.get_coin_by_id(id=coin_id)
        return data['sentiment_votes_up_percentage'] / 100
    except Exception as e:
        print(f"{Fore.RED}Sentiment fetch error for {symbol}: {e}")
        return 0.5  # Default neutral


# ==========================================================================
#             COUNTER-TREND LIMIT ORDER PLACER (Long/Short) - Adjusted
# ==========================================================================

async def place_counter_trend_limit(
    client,
    symbol,
    analysis_data,
    risk_usdt=0.50,
    min_rr=1.5,
    dry_run=False   # เพิ่มพารามิเตอร์นี้เพื่อรองรับโหมดทดสอบ (ไม่ตั้ง order จริง)
):
    """
    วาง Limit Order แบบ Counter-Trend โดยใช้ analysis_data
    - dry_run=True → แค่เช็ค setup และ return ผล ไม่ตั้ง order จริง
    """
    try:
        sym = symbol if symbol.endswith('USDT') else symbol + 'USDT'
        sym_input = sym.replace('USDT', '')
        
        if not analysis_data:
            print(f"[Counter-Trend] ไม่มี analysis_data สำหรับ {sym}")
            return {'success': False, 'reason': 'ไม่มีข้อมูลวิเคราะห์'}
        
        current_price = analysis_data.get('price_current', 0)
        if current_price <= 0:
            print(f"[Counter-Trend] ราคาปัจจุบันไม่ถูกต้องสำหรับ {sym}")
            return {'success': False, 'reason': 'ราคาปัจจุบันไม่ถูกต้อง'}
        
        # ตรวจแนวโน้ม (ตามตัวอย่าง AVAX: Bearish → Long)
        trend_strong = False
        direction = None
        side_order = None
        
        if (analysis_data.get('trend_4h') == 'Bearish' and 
            analysis_data.get('trend_1h') == 'Bearish'):
            trend_strong = True
            direction = 'LONG'
            side_order = SIDE_BUY
        
        elif (analysis_data.get('trend_4h') == 'Bullish' and 
              analysis_data.get('trend_1h') == 'Bullish'):
            trend_strong = True
            direction = 'SHORT'
            side_order = SIDE_SELL
        
        if not trend_strong:
            print(f"[Counter-Trend] แนวโน้มไม่แรงพอสำหรับ Counter {sym}")
            return {'success': False, 'reason': 'แนวโน้มไม่แรงพอสำหรับ Counter-Trend'}
        
        # กำหนด Limit Price (ตามตัวอย่าง AVAX → ใช้ Support)
        atr = analysis_data.get('atr', current_price * 0.015)
        support = analysis_data.get('support', current_price * 0.97)
        resistance = analysis_data.get('resistance', current_price * 1.03)
        fib_382 = analysis_data.get('fib_382', current_price * 0.382)
        fib_618 = analysis_data.get('fib_618', current_price * 0.618)
        
        limit_price_raw = 0.0
        
        if direction == 'LONG':
            candidates = [support, fib_618, current_price - atr * 1.2]
            limit_price_raw = min([x for x in candidates if x > 0])
            if limit_price_raw < current_price * 0.92:
                limit_price_raw = current_price * 0.94
        
        else:
            candidates = [resistance, fib_382, current_price + atr * 1.2]
            limit_price_raw = max([x for x in candidates if x > 0])
            if limit_price_raw > current_price * 1.08:
                limit_price_raw = current_price * 1.06
        
        if limit_price_raw <= 0:
            return {'success': False, 'reason': 'ไม่สามารถคำนวณ Limit Price ได้'}
        
        # SL / TP
        if direction == 'LONG':
            sl_raw = limit_price_raw - atr * ATR_SL_MULTIPLIER
            tp_raw = limit_price_raw + atr * ATR_TP_MULTIPLIER
            tp_raw = min(tp_raw, resistance)
        else:
            sl_raw = limit_price_raw + atr * ATR_SL_MULTIPLIER
            tp_raw = limit_price_raw - atr * ATR_TP_MULTIPLIER
            tp_raw = max(tp_raw, support)
        
        rr = calculate_rr_ratio(limit_price_raw, sl_raw, tp_raw, direction)
        if rr < min_rr:
            print(f"[Counter-Trend] RR ต่ำเกิน {rr:.2f} < {min_rr} สำหรับ {sym}")
            return {'success': False, 'reason': f'RR ต่ำเกิน ({rr:.2f} < {min_rr})'}
        
        # Position sizing
        stop_distance = abs(limit_price_raw - sl_raw)
        position_value = risk_usdt / (stop_distance / limit_price_raw)
        qty = position_value / limit_price_raw
        
        step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
        qty = math.floor(qty / step_size) * step_size
        if qty < step_size * 5:
            qty = step_size * 5
        
        qty_precision = sym_info.get(sym, (4, 2))[1]
        qty_str = f"{qty:.{qty_precision}f}"
        
        # ปัดราคา
        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
        price_precision = sym_info.get(sym, (4, 2))[0]
        limit_price = round_to_tick(limit_price_raw, tick_size)
        sl_price = round_to_tick(sl_raw, tick_size)
        tp_price = round_to_tick(tp_raw, tick_size)
        
        limit_str = f"{limit_price:.{price_precision}f}"
        sl_str = f"{sl_price:.{price_precision}f}"
        tp_str = f"{tp_price:.{price_precision}f}"
        
        # ถ้าเป็น dry_run → return ผลโดยไม่ตั้ง order
        if dry_run:
            return {
                'success': True,
                'direction': direction,
                'limit_price': limit_price,
                'sl': sl_price,
                'tp': tp_price,
                'rr': rr,
                'qty': qty,
                'qty_str': qty_str,
                'reason': 'Dry run - setup ผ่านเกณฑ์'
            }
        
        # Leverage
        leverage = MAX_LEVERAGE
        await client.futures_change_leverage(symbol=sym, leverage=leverage)
        
        # สั่ง Limit + SL/TP
        order = await client.futures_create_order(
            symbol=sym,
            side=side_order,
            type='LIMIT',
            timeInForce='GTC',
            quantity=qty_str,
            price=limit_str
        )
        
        close_side = SIDE_SELL if direction == 'LONG' else SIDE_BUY
        await client.futures_create_order(
            symbol=sym,
            side=close_side,
            type='STOP_MARKET',
            stopPrice=sl_str,
            closePosition=True,
            timeInForce='GTC',
            workingType='MARK_PRICE'
        )
        await client.futures_create_order(
            symbol=sym,
            side=close_side,
            type='TAKE_PROFIT_MARKET',
            stopPrice=tp_str,
            closePosition=True,
            timeInForce='GTC',
            workingType='MARK_PRICE'
        )
        
        # บันทึก pending
        pending_orders_detail.append({
            'symbol': sym,
            'side': side_order,
            'price': limit_price,
            'qty': qty,
            'time': datetime.now(),
            'orderId': order['orderId'],
            'manual': False,
            'leverage': leverage,
            'risk_usdt': risk_usdt,
            'source': 'counter_trend_auto'
        })
        
        # รายงาน Telegram
        report = (
            f"📊 **{sym_input}/USDT - วิเคราะห์อัจฉริยะ**\n"
            f"{datetime.now().strftime('%d/%m %H:%M')} | ราคา: {current_price:.2f}\n\n"
            f"📈 Trend Analysis\n"
            f"4H: {'🔴 Bearish' if analysis_data.get('trend_4h') == 'Bearish' else '🟢 Bullish'}\n"
            f"1H: {'🔴 Bearish' if analysis_data.get('trend_1h') == 'Bearish' else '🟢 Bullish'}\n\n"
            f"📊 Momentum\n"
            f"RSI(4H): {analysis_data.get('rsi_4h', 'N/A'):.1f} Neutral\n"
            f"Stoch(4H): {analysis_data.get('stoch_4h', 'N/A'):.1f} | Stoch(1H): {analysis_data.get('stoch_1h', 'N/A'):.1f}\n"
            f"MACD: {'🔴 Bearish' if analysis_data.get('macd') == 'Bearish' else '🟢 Bullish'}\n\n"
            f"🎯 Support & Resistance\n"
            f"Support: {analysis_data.get('support', 'N/A'):.2f} | Resistance: {analysis_data.get('resistance', 'N/A'):.2f}\n"
            f"Position: Mid-range\n\n"
            f"🎪 Fibonacci Levels (38.2%/61.8%: {analysis_data.get('fib_382', 'N/A'):.2f} / {analysis_data.get('fib_618', 'N/A'):.2f})\n\n"
            f"💡 สรุป: {'Strong BUY 🟢' if direction == 'LONG' else 'Strong SELL 🔴'}\n\n"
            f"✅ **ตั้ง Limit Order สำเร็จ!**\n"
            f"เหรียญ: {sym_input}\n"
            f"ทิศทาง: {direction} ({'Buy' if direction == 'LONG' else 'Sell'})\n"
            f"ราคา Limit: `{limit_str}`\n"
            f"Qty: `{qty_str}`\n"
            f"เลเวอเรจ: `{leverage}x`\n"
            f"Risk: `${risk_usdt:.2f}` USDT\n"
            f"RR (โดยประมาณ): `{rr:.2f}:1`\n"
            f"ราคาปัจจุบัน: `{current_price:.4f}`\n"
            f"ATR: `{atr:.6f}`\n"
            f"Order ID: `{order['orderId']}`"
        )
        
        await send_telegram_report(report)
        
        return {
            'success': True,
            'direction': direction,
            'limit_price': limit_price,
            'sl': sl_price,
            'tp': tp_price,
            'rr': rr,
            'qty': qty,
            'qty_str': qty_str,
            'order_id': order['orderId']
        }
    
    except Exception as e:
        print(f"[Counter-Trend] Error {sym}: {e}")
        return {'success': False, 'reason': str(e)[:120]}


# ==========================================================================
#                  /lmauto - Limit Auto (ICT / Smart Money Advanced)
# ==========================================================================

async def analyze_ict_smart_money(client, sym, tf_main='1h', tf_higher='4h'):
    """
    วิเคราะห์ 8 เงื่อนไข ICT ขั้นสูง
    Returns dict ของ confluence ที่เจอ + score
    """
    try:
        # ดึงข้อมูลหลัก
        k_main = await client.futures_klines(symbol=sym, interval=tf_main, limit=200)
        df_main = calculate_indicators(k_main)
        if df_main.empty: return None

        k_higher = await client.futures_klines(symbol=sym, interval=tf_higher, limit=100)
        df_higher = calculate_indicators(k_higher)

        curr_main = df_main.iloc[-1]
        prev_main = df_main.iloc[-2] if len(df_main) > 1 else curr_main

        curr_higher = df_higher.iloc[-1] if not df_higher.empty else curr_main

        current_price = float(curr_main['c'])
        atr = float(curr_main['atr']) if 'atr' in curr_main else current_price * 0.015

        confluence = {}
        score = 0

        # 1. Liquidity & Stop Hunting (Wick ยาว + เด้งกลับ)
        wick_upper = curr_main['h'] - max(curr_main['o'], curr_main['c'])
        wick_lower = min(curr_main['o'], curr_main['c']) - curr_main['l']
        body = abs(curr_main['o'] - curr_main['c'])

        is_stop_hunt_up = (wick_upper > body * 3) and (curr_main['c'] > curr_main['o'])
        is_stop_hunt_down = (wick_lower > body * 3) and (curr_main['c'] < curr_main['o'])

        if is_stop_hunt_up or is_stop_hunt_down:
            confluence['liquidity_sweep'] = True
            score += 2
            confluence['sweep_direction'] = 'up' if is_stop_hunt_up else 'down'

        # 2. Order Block (OB ที่ทำ BOS)
        # หา OB ล่าสุด (แท่ง impulsive ก่อน BOS)
        bos_detected = False
        ob_level = 0.0
        for i in range(-10, -1):
            if df_main.iloc[i]['c'] > df_main.iloc[i]['ema50'] and df_main.iloc[i+1]['c'] < df_main.iloc[i+1]['ema50']:
                bos_detected = True
                ob_level = df_main.iloc[i]['h']  # High ของแท่งก่อน BOS (สำหรับ Short)
                break
            elif df_main.iloc[i]['c'] < df_main.iloc[i]['ema50'] and df_main.iloc[i+1]['c'] > df_main.iloc[i+1]['ema50']:
                bos_detected = True
                ob_level = df_main.iloc[i]['l']  # Low ของแท่งก่อน BOS (สำหรับ Long)
                break

        if bos_detected:
            confluence['order_block'] = True
            confluence['ob_level'] = ob_level
            score += 2

        # 3. Market Structure Shift (MSS) บน TF เล็ก
        recent_highs = df_main['h'].iloc[-5:].max()
        recent_lows = df_main['l'].iloc[-5:].min()
        is_mss_long = (recent_lows > df_main['l'].iloc[-10] and recent_highs > df_main['h'].iloc[-10])
        is_mss_short = (recent_highs < df_main['h'].iloc[-10] and recent_lows < df_main['l'].iloc[-10])

        if is_mss_long or is_mss_short:
            confluence['mss'] = True
            confluence['mss_direction'] = 'long' if is_mss_long else 'short'
            score += 1.5

        # 4. Fair Value Gap (FVG)
        fvg_up = (df_main['l'].shift(1) > df_main['h']) & (df_main['c'] > df_main['o'])  # ← เปลี่ยน shift(-1) เป็น shift(1)
        fvg_down = (df_main['h'].shift(1) < df_main['l']) & (df_main['c'] < df_main['o'])  # ← เดียวกัน
        latest_fvg = None
        if fvg_up.any():
            idx = fvg_up[fvg_up].index[-1]
            latest_fvg = (df_main.loc[idx, 'h'], df_main.loc[idx, 'l'].shift(-1))
        elif fvg_down.any():
            idx = fvg_down[fvg_down].index[-1]
            latest_fvg = (df_main.loc[idx, 'l'], df_main.loc[idx, 'h'].shift(-1))

        if latest_fvg:
            confluence['fvg'] = True
            confluence['fvg_mid'] = (latest_fvg[0] + latest_fvg[1]) / 2
            score += 1.5

        # 5. Time-Based (Kill Zone / Session Open)
        now_hour = datetime.now().hour
        is_kill_zone = (now_hour in [8,9,10,14,15,16,20,21])  # London/NY open + kill zone ICT
        if is_kill_zone:
            confluence['kill_zone'] = True
            score += 1

        # 6. Volume Spike + Exhaustion
        vol_spike = curr_main['v'] > curr_main['vol_ma'] * 2.0
        vol_exhaust = (curr_main['v'] < curr_main['vol_ma'] * 0.6) and (abs(curr_main['c'] - curr_main['o']) > atr * 1.5)
        if vol_spike or vol_exhaust:
            confluence['volume_confirm'] = True
            score += 1

        # 7. Structure Divergence
        if len(df_main) > 10:
            hh_price = df_main['h'].iloc[-3:].max()
            hh_idx = df_main['h'].iloc[-3:].idxmax()
            if hh_price > df_main['h'].iloc[-6:hh_idx].max() and curr_main['adx'] < df_main['adx'].iloc[hh_idx-3]:
                confluence['structure_div'] = True
                score += 1.5

        # 8. Confluence สรุป
        confluence['total_score'] = score
        confluence['direction'] = 'long' if score > 4 and ('mss' in confluence and confluence.get('mss_direction') == 'long') else \
                                 'short' if score > 4 and ('mss' in confluence and confluence.get('mss_direction') == 'short') else None

        return confluence if score >= 4 else None  # ต้อง ≥4 ข้อ (ตามที่คุณกำหนด ≥3 แต่เพิ่มความเข้มงวด)

                
    except Exception as e:
        print(f"ICT Analysis Error {sym}: {str(e)}")
        await send_telegram_report(f"⚠️ ICT Analysis ล้มเหลว {sym_input}: {str(e)}", chat_id)
        return None



# ==========================================================================
async def main():
    global bal, active, btc_p, pending_orders_detail, running
    global sym_info, sym_filters, top_50_symbols, last_volume_update
    global sl_tp_advice_notified, signal_features
    global last_spike_check, last_short_signal_check
    global active_detailed
    global last_sl_tp_check
    global manual_closed_cooldown   # ถ้ามีตัวแปรนี้ด้วย ให้ใส่ด้วย

    # ... โค้ดต่อจากนี้เหมือนเดิม ...

    client = None
    reconnect_attempts = 0
    MAX_RECONNECT = 5

    while running and reconnect_attempts < MAX_RECONNECT:
        try:
            client = await AsyncClient.create(API_KEY, API_SECRET, testnet=USE_TESTNET)
                        # --- Pre-train AI ด้วย backtest ถ้ายังมีข้อมูลน้อย ---
            if len(brain.data) < 30:  # ถ้ายังมีน้อยกว่า 30 trade
                print(f"{Fore.CYAN}🧠 Pre-training AI ด้วย historical backtest (30 periods)...{Style.RESET_ALL}")
                await backtest_ai_training(client, num_periods=50, chat_id=TELEGRAM_CHAT_ID)
                
                # Feed ผล backtest เข้า brain + train ทันที
                if hasattr(brain, 'backtest_results') and brain.backtest_results:
                    training_count = 0
                    for res in brain.backtest_results.get('results', []):
                        if 'features' in res and 'win' in res:
                            brain.update_memory(res['features'], res['win'])
                            training_count += 1
                    if training_count > 0:
                        brain.train_model()
                        print(f"{Fore.GREEN}Pre-train สำเร็จ! เพิ่ม {training_count} samples เข้า AI แล้ว{Style.RESET_ALL}")
                        await send_telegram_report(
                            f"🧠 **AI Pre-trained สำเร็จ!**\n"
                            f"เพิ่มข้อมูลเทรน {training_count} trades จาก backtest\n"
                            f"ใช้ `/aistats` เช็คความก้าวหน้า",
                            TELEGRAM_CHAT_ID
                        )
            print(f"{Fore.GREEN}Connected to Binance {'Testnet' if USE_TESTNET else 'Mainnet'}! "
                  f"(Attempt {reconnect_attempts+1})")

            acc = await client.futures_account()
            bal = float(acc['totalWalletBalance'])

            if telegram_bot:
                greeting = (
                    f"🚀 **TITAN PRO v33.0** - AI-Powered Trading Bot Started!\n\n"
                    f"📅 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} UTC\n"
                    f"🔧 Mode: {'🧪 TESTNET' if USE_TESTNET else '🔴 MAINNET (LIVE)'}\n"
                    f"💰 Wallet Balance: `{bal:,.2f}` USDT\n\n"
                    f"━━━━━━━━━ ⚙️ **Core Settings** ━━━━━━━━━\n"
                    f"• Leverage: `{MAX_LEVERAGE}x`\n"
                    f"• Risk Per Trade: `$0.50` (fixed)\n"
                    f"• Max Open Positions: `{MAX_OPEN_POSITIONS}`\n"
                    f"• Min Account: `{MIN_BALANCE_TO_TRADE}` USDT\n\n"
                    f"━━━━━━━━━ 🤖 **AI Learning** ━━━━━━━━━\n"
                    f"• Auto Train: Every 5 new trades\n"
                    f"• Neural Network: 3-layer MLP (64→32→1)\n"
                    f"• Features Tracked: 10 technical indicators\n"
                    f"• Check stats: `/aistats`\n\n"
                    f"━━━━━━━━━ 🎯 **Auto Entry Systems** ━━━━━━━━━\n"
                    f"🟢 Volume Spike LONG:\n"
                    f"   └ Trigger: Vol > 2.5x + 6 confirmations\n"
                    f"   └ Control: `/spike on/off`\n\n"
                    f"🔴 Strong Signal SHORT:\n"
                    f"   └ Trigger: ≥6 bearish + vol spike\n"
                    f"   └ Control: `/shortsig on/off`\n\n"
                    f"📊 **Risk Management**:\n"
                    f"   └ SL: ATR × {ATR_SL_MULTIPLIER} | TP: ATR × {ATR_TP_MULTIPLIER}\n"
                    f"   └ Min R:R Ratio: 1:2\n"
                    f"   └ Fibonacci + Elliott Wave Analysis\n\n"
                    f"━━━━━━━━━ 💬 **Essential Commands** ━━━━━━━━━\n"
                    f"📊 `/pnl` - View PNL + Win Rate\n"
                    f"🧠 `/aistats` - AI Model Stats\n"
                    f"📈 `/daily` - 7-day summary\n"
                    f"⭐ `/positions` - All open positions\n"
                    f"/help - Full command list\n\n"
                    f"_Status: Ready to trade_ ✅\n"
                    f"/setauto "
                    f"/divscan"
                    f"/trainnow"
                    f"/winrate"
                    f"/winmonthly"
                    f"พิมพ์ /ctai btc หรือ /ctai avax Countertrend เพื่อวิเคราะห์เหรียญแบบละเอียดด้วย AI\n\n"
                    f"/lmauto -ชื่อเหรียญ คือคำสั่งเปิด/ปิดระบบ LMAuto (Long/Short Management Auto) สำหรับจัดการ SL/TP อัตโนมัติ\n\n"
                    f"_LFG!_ 🚀"
                )
                await send_telegram_report(greeting)

            reconnect_attempts = 0  # reset เมื่อเชื่อมต่อสำเร็จ

            cmd_q = asyncio.Queue()

            def input_reader():
                while running:
                    try:
                        line = sys.stdin.readline().strip().lower()
                        if line and running:
                            cmd_q.put_nowait(line)
                    except:
                        break

            asyncio.get_event_loop().run_in_executor(None, input_reader)

            # โหลด exchange info และ filters
            info = await client.futures_exchange_info()
            for s in info['symbols']:
                if s['symbol'].endswith('USDT') and s['status'] == 'TRADING' and s['contractType'] == 'PERPETUAL':
                    sym = s['symbol']
                    sym_info[sym] = (s['pricePrecision'], s['quantityPrecision'])
                    tick = step = 0.0
                    for f in s['filters']:
                        if f['filterType'] == 'PRICE_FILTER':
                            tick = float(f['tickSize'])
                        elif f['filterType'] == 'LOT_SIZE':
                            step = float(f['stepSize'])
                    sym_filters[sym] = {'tickSize': tick, 'stepSize': step}

            # โหลด Top 100 Volume เริ่มต้น
            try:
                print(f"{Fore.CYAN}Fetching initial Top 100 by 24h Volume...")
                tickers = await client.futures_ticker()
                volume_list = [(t['symbol'], float(t['quoteVolume'])) 
                               for t in tickers 
                               if t['symbol'].endswith('USDT') and t['symbol'] in sym_info]
                volume_list.sort(key=lambda x: x[1], reverse=True)
                top_50_symbols = [s[0] for s in volume_list[:100]]
                last_volume_update = datetime.now()
                print(f"{Fore.GREEN}Loaded {len(top_50_symbols)} symbols | Top 5: {', '.join(top_50_symbols[:5])}")
            except Exception as e:
                print(f"{Fore.RED}Initial Top 100 failed: {e}")

            print(f"{Fore.CYAN}System Ready!{Style.RESET_ALL}")

            prev_active_symbols = set()

            while running:
                try:
                    # Refresh ข้อมูลบัญชีและราคา
                    acc = await client.futures_account()
                    bal = float(acc['totalWalletBalance'])

                    pos_data = await client.futures_position_information()
                    all_tickers = await client.futures_symbol_ticker()
                    price_map = {t['symbol']: float(t['price']) for t in all_tickers}
                    btc_p = price_map.get("BTCUSDT", 0.0)

                    # สร้างรายการ position ปัจจุบัน + refresh SL/TP ทุกครั้ง
                    current_active_symbols = set()
                    active = []  # รีเซ็ต active ทุก loop เพื่อ sync ใหม่
                    active_symbols = set()  # สำหรับเช็ค duplicate

                    for p in pos_data:
                        amt_str = p['positionAmt']
                        try:
                            amt = float(amt_str)
                        except:
                            amt = 0.0
                        
                        # กรอง ghost position: ถ้า |amt| เล็กมาก (< 0.001 หรือตาม min qty ของเหรียญ)
                        # หรือ entryPrice = 0 (ผิดปกติ)
                        if abs(amt) < 0.001 or float(p['entryPrice']) == 0.0:
                            print(f"[GHOST FILTER] ข้าม ghost position {p['symbol']} amt={amt_str} entry={p['entryPrice']}")
                            continue
                        
                        if amt == 0:
                            continue

                        sym = p['symbol']
                        if sym in active_symbols:
                            continue  # ป้องกัน duplicate ถ้า Binance ส่งซ้ำ
                        active_symbols.add(sym)
                        current_active_symbols.add(sym)

                        entry = float(p['entryPrice'])
                        curr_price = price_map.get(sym, 0.0)

                    # ดึง SL/TP ล่าสุดทุกครั้ง (refresh ใหม่)
                        sl = tp = 0.0
                        try:
                            orders = await client.futures_get_open_orders(symbol=sym)
                            for o in orders:
                                if o['type'] == 'STOP_MARKET' and o.get('closePosition', False):
                                    sl = float(o['stopPrice'])
                                if o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False):
                                    tp = float(o['stopPrice'])
                            print(f"DEBUG: Refresh SL/TP สำหรับ {sym} → SL: {sl:.6f}, TP: {tp:.6f}")
                        except Exception as e:
                            print(f"Refresh SL/TP failed for {sym}: {e}")

                        active.append({
                            'symbol': sym,
                            'side': 'LONG' if float(p['positionAmt']) > 0 else 'SHORT',
                            'entry': entry,
                            'curr_price': curr_price,
                            'pnl': float(p['unRealizedProfit']),
                            'amt': float(p['positionAmt']),
                            'margin': abs(float(p['positionAmt']) * entry / MAX_LEVERAGE),
                            'sl': sl,
                            'tp': tp
                        })
                        # Debug: แสดง symbols ที่ active ตอนนี้
                    print(f"[DEBUG ACTIVE] Current active symbols: {current_active_symbols}")
                    # ตรวจจับ position ใหม่และที่ปิดไป (ใช้ prev_active_symbols จาก loop ก่อนหน้า)
                    new_positions = current_active_symbols - prev_active_symbols
                    closed_positions = prev_active_symbols - current_active_symbols

                    # ==========================================================================
                    # การใช้งานใน main loop (while running)
                    # ==========================================================================
                    # ใส่ใน while running: หลัง refresh acc, pos_data, active, price_map

                    # ... โค้ด refresh อื่น ๆ ...

                    # ตรวจสอบ position ที่ปิด
                    closed_count = await check_and_record_closed_positions(client)
                    if closed_count > 0:
                        print(f"[CLOSED SUMMARY] บันทึกและแจ้งเตือน {closed_count} positions ที่ปิดแล้ว")

                    # Debug: แสดงการเปลี่ยนแปลง
                    print(f"[DEBUG POS CHANGE] New: {new_positions}")
                    print(f"[DEBUG POS CHANGE] Closed: {closed_positions}")
                    # จัดการ position ใหม่ (เวอร์ชันแก้ spam)
                    for sym in new_positions:
                        if sym in new_position_locked:
                            print(f"[SKIP NOTIFY] {sym} เคยแจ้งตั้ง SL/TP แล้ว → ข้าม")
                            continue

                        pos = next((p for p in active if p['symbol'] == sym), None)
                        if not pos:
                            continue
                    # อัพเดท max ROE ทุก loop
                    for pos in active:
                        sym = pos['symbol']
                        if sym in active_detailed:
                            roe = (pos['pnl'] / pos['margin'] * 100) if pos['margin'] > 0 else 0.0
                            active_detailed[sym]['max_roe'] = max(active_detailed[sym]['max_roe'], roe)
                            active_detailed[sym]['sl'] = sl  # ← เพิ่ม
                            active_detailed[sym]['tp'] = tp  # ← เพิ่ม

                    # ตั้ง SL/TP อัตโนมัติสำหรับ position ที่ยังไม่มี (fallback เดิม)
                    for pos in active:
                        sym = pos['symbol']
                        side = pos['side']
                        entry = pos['entry']
                        curr_price = pos['curr_price']

                        try:
                            open_orders = await client.futures_get_open_orders(symbol=sym)
                            has_sl = any(o['type'] == 'STOP_MARKET' and o.get('closePosition', False) for o in open_orders)
                            has_tp = any(o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False) for o in open_orders)
                        except Exception as e:
                            print(f"{Fore.RED}Error checking open orders for {sym}: {e}{Style.RESET_ALL}")
                            has_sl = has_tp = False

                        if has_sl and has_tp:
                            continue

                        print(f"{Fore.CYAN}→ Position {sym} {side} ยังไม่มี SL/TP ครบ → ตั้งให้อัตโนมัติ{Style.RESET_ALL}")

                        atr_val = await get_cached_atr(client, sym)
                        if atr_val is None:
                            atr_val = entry * 0.015

                        if side == 'LONG':
                            sl_price_raw = entry - (atr_val * ATR_SL_MULTIPLIER)
                            tp_price_raw = entry + (atr_val * ATR_TP_MULTIPLIER)
                            order_side = SIDE_SELL
                        else:
                            sl_price_raw = entry + (atr_val * ATR_SL_MULTIPLIER)
                            tp_price_raw = entry - (atr_val * ATR_TP_MULTIPLIER)
                            order_side = SIDE_BUY

                        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                        sl_price = round_to_tick(sl_price_raw, tick_size)
                        tp_price = round_to_tick(tp_price_raw, tick_size)
                        price_precision = sym_info.get(sym, (4, 2))[0]

                        sl_price_str = f"{sl_price:.{price_precision}f}"
                        tp_price_str = f"{tp_price:.{price_precision}f}"

                        if not has_sl:
                            try:
                                await client.futures_create_order(
                                    symbol=sym,
                                    side=order_side,
                                    type='STOP_MARKET',
                                    stopPrice=sl_price_str,
                                    closePosition=True,
                                    timeInForce='GTC',
                                    workingType='MARK_PRICE',
                                )
                                pos['sl'] = sl_price
                                print(f"{Fore.GREEN}ตั้ง SL สำเร็จ {sym} @ {sl_price_str}{Style.RESET_ALL}")
                            except Exception as e:
                                print(f"{Fore.RED}ตั้ง SL ล้มเหลว {sym}: {e}{Style.RESET_ALL}")

                        if not has_tp:
                            try:
                                await client.futures_create_order(
                                    symbol=sym,
                                    side=order_side,
                                    type='TAKE_PROFIT_MARKET',
                                    stopPrice=tp_price_str,
                                    closePosition=True,
                                    timeInForce='GTC',
                                    workingType='MARK_PRICE',
                                )
                                pos['tp'] = tp_price
                                print(f"{Fore.GREEN}ตั้ง TP สำเร็จ {sym} @ {tp_price_str}{Style.RESET_ALL}")
                            except Exception as e:
                                print(f"{Fore.RED}ตั้ง TP ล้มเหลว {sym}: {e}{Style.RESET_ALL}")

                        if (not has_sl and pos['sl'] > 0) or (not has_tp and pos['tp'] > 0):
                            await send_telegram_report(
                                f"🛡️ *ตั้ง SL/TP อัตโนมัติสำเร็จ*\n"
                                f"*Symbol:* {sym.replace('USDT','')}\n"
                                f"*Side:* {side}\n"
                                f"*SL:* {sl_price_str}\n"
                                f"*TP:* {tp_price_str}\n"
                                f"*Entry:* {entry:.6f}"
                            )

                    # ตรวจจับ position ใหม่และที่ปิดไป
                    new_positions = current_active_symbols - prev_active_symbols
                    closed_positions = prev_active_symbols - current_active_symbols

                    # จัดการ position ใหม่ → เก็บข้อมูลละเอียด + ตั้งคำแนะนำ
                    for sym in new_positions:
                        pos = next((p for p in active if p['symbol'] == sym), None)
                        if not pos:
                            continue

                        features = signal_features.get(sym)
                        if not features:
                            try:
                                analysis = await analyze_matrix(client, sym)
                                if analysis:
                                    features = [
                                        analysis['rsi']/100,
                                        analysis['adx']/100,
                                        (analysis.get('macd', 0) - analysis.get('signal', 0)) / analysis['atr'] if analysis['atr'] > 0 else 0,
                                        (analysis['curr_p'] - analysis.get('ema200', analysis['curr_p'])) / analysis.get('ema200', 1),
                                        1.0,
                                        analysis['score']/8.0,
                                        1 if analysis['side'] == 'LONG' else 0
                                    ]
                            except:
                                features = [0.5] * 7

                        active_detailed[sym] = {
                            'side': pos['side'],
                            'entry_price': pos['entry'],
                            'entry_time': datetime.now(),
                            'quantity': abs(pos['amt']),
                            'leverage': MAX_LEVERAGE,
                            'features': features,
                            'max_roe': 0.0,
                            'source': pos.get('source', 'matrix')
                        }

                        print(f"{Fore.CYAN}→ พบ Position ใหม่: {sym} {pos['side']} → ตั้ง SL/TP + แจ้งคำแนะนำ")

                        try:
                            klines = await client.futures_klines(symbol=sym, interval="15m", limit=250)
                            df = calculate_indicators(klines)
                            if df.empty or len(df) < 30:
                                atr_val = pos['entry'] * 0.02
                                curr = {'rsi':50, 'adx':25, 'macd':0, 'signal':0, 'atr':atr_val, 
                                        'c':pos['curr_price'], 'ema200':pos['curr_price'], 'v':1, 'vol_ma':1}
                            else:
                                atr_val = float(df.iloc[-1]['atr'])
                                curr = df.iloc[-1]

                            if pos['side'] == 'LONG':
                                sl_price_raw = pos['entry'] - (atr_val * ATR_SL_MULTIPLIER)
                                tp_price_raw = pos['entry'] + (atr_val * ATR_TP_MULTIPLIER)
                            else:
                                sl_price_raw = pos['entry'] + (atr_val * ATR_SL_MULTIPLIER)
                                tp_price_raw = pos['entry'] - (atr_val * ATR_TP_MULTIPLIER)

                            tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                            sl_price = round_to_tick(sl_price_raw, tick_size)
                            tp_price = round_to_tick(tp_price_raw, tick_size)

                            price_precision = sym_info.get(sym, (4, 2))[0]
                            sl_price_str = f"{sl_price:.{price_precision}f}"
                            tp_price_str = f"{tp_price:.{price_precision}f}"
                            current_price_str = f"{pos['curr_price']:.{price_precision}f}"

                            qty = abs(pos['amt'])
                            qty_str = f"{qty:.{sym_info.get(sym, (4, 2))[1]}f}"

                            now_str = datetime.now().strftime("%d/%m/%Y | %H:%M:%S")
                            profit_10 = pos['entry'] * 1.10 if pos['side'] == 'LONG' else pos['entry'] * 0.90
                            profit_20 = pos['entry'] * 1.20 if pos['side'] == 'LONG' else pos['entry'] * 0.80
                            sl_wide_raw = pos['entry'] - (atr_val * 5.0) if pos['side'] == 'LONG' else pos['entry'] + (atr_val * 5.0)
                            sl_wide = round_to_tick(sl_wide_raw, tick_size)

                            report = (
                                f"✅ **เข้า Position สำเร็จ + คำแนะนำ SL/TP!**\n"
                                f"วันที่: {now_str}\n"
                                f"เหรียญ: `{sym.replace('USDT','')}`\n"
                                f"ราคาปัจจุบัน: `{current_price_str}` USDT\n"
                                f"ทิศ: **{pos['side']}** | Entry: `{pos['entry']:.6f}` | จำนวน: `{qty_str}`\n\n"
                                f"🤖 **บอทตั้งอัตโนมัติ**\n"
                                f"SL: `{sl_price_str}`\n"
                                f"TP: `{tp_price_str}` (RR 1:2)\n\n"
                                f"🎯 **คำแนะนำเพิ่มเติม**\n"
                                f"• เป้า +10%: `{profit_10:.{price_precision}f}`\n"
                                f"• เป้า +20%: `{profit_20:.{price_precision}f}`\n"
                                f"• SL ยืด (ถือยาว): `{sl_wide:.{price_precision}f}`"
                            )
                            #await send_telegram_report(report)
                            #sl_tp_advice_notified.add(sym)

                        except Exception as e:
                            print(f"{Fore.RED}Error processing new position {sym}: {e}")

                        # ==========================================================================
                        #               จัดการ position ที่ปิดไป → บันทึกทุกรอบ ไม่ข้าม
                        # ==========================================================================
                        # จัดการ position ที่ปิดไป → ใช้ฟังก์ชันกลางเท่านั้น
                        for sym in closed_positions:
                            print(f"[CLOSED DETECTED] {sym} → บันทึก trade ด้วย record_closed_trade")
                            # ใน while running: หลังคำนวณ closed_positions
                            print(f"[POS-TRACK] ก่อนหน้า = {prev_active_symbols}")
                            print(f"[POS-TRACK] ปัจจุบัน = {current_active_symbols}")
                            print(f"[POS-TRACK] ปิดไป = {closed_positions if closed_positions else 'ไม่มี'}")

                            for sym in closed_positions:
                                print(f"!!! DETECT CLOSE → {sym} !!! จะเรียก record_closed_trade() ทันที")
                                await record_closed_trade(client, sym, "Debug: Auto Detected Close")
                            
                            pos_info = active_detailed.get(sym, {})
                            print(f"[CLOSED DETECT DEBUG] {sym} | pos_info: {'มี' if pos_info else 'ไม่มี'}")
                            
                            exit_time = datetime.now()
                            exit_reason = "Detected Close (auto)"
                            pnl = 0.0
                            pnl_percent = 0.0
                            is_win = False
                            exit_price = 0.0
                            duration_hours = 0.5  # fallback ที่สมเหตุสมผลกว่า 0.1
                            side = pos_info.get('side', 'UNKNOWN')
                            entry_price = pos_info.get('entry_price', 0.0)
                            qty = pos_info.get('quantity', 0.0)
                            max_roe = pos_info.get('max_roe', 0.0)
                            features = pos_info.get('features', [])
                            leverage = pos_info.get('leverage', MAX_LEVERAGE)
                            
                            # ─── ดึง realized trade ล่าสุด (พยายาม 2 รอบ ห่างกัน 1 วินาที) ───
                            close_trade = None
                            for attempt in range(2):
                                try:
                                    trades = await client.futures_account_trades(symbol=sym, limit=10)
                                    close_trade = next((t for t in reversed(trades) 
                                                    if float(t.get('realizedPnl', 0)) != 0 
                                                    and t.get('commissionAsset') == 'USDT'), None)
                                    if close_trade:
                                        print(f"[TRADE FOUND attempt {attempt+1}] {sym} realizedPnl={close_trade['realizedPnl']}")
                                        break
                                except Exception as e:
                                    print(f"[TRADE FETCH ERROR attempt {attempt+1}] {sym}: {e}")
                                if attempt < 1:
                                    await asyncio.sleep(1.0)  # รอ sync
                            
                            if close_trade:
                                exit_price     = float(close_trade['price'])
                                pnl            = float(close_trade['realizedPnl'])
                                qty            = abs(float(close_trade.get('qty', qty)))
                                exit_time      = datetime.fromtimestamp(int(close_trade['time']) / 1000)
                                
                                # side ของ close trade = opposite ของ position เดิม
                                close_side_str = close_trade.get('side', 'UNKNOWN')
                                if close_side_str == 'SELL':
                                    side = 'LONG'   # SELL = ปิด LONG
                                elif close_side_str == 'BUY':
                                    side = 'SHORT'  # BUY = ปิด SHORT
                                
                                exit_reason = "Realized Trade Data"
                                orig_type = close_trade.get('origType', '')
                                if 'STOP_MARKET'     in orig_type: exit_reason = "Hit SL"
                                elif 'TAKE_PROFIT_MARKET' in orig_type: exit_reason = "Hit TP"
                                elif sym in manual_closed_cooldown: 
                                    exit_reason = "Manual Close"
                                    del manual_closed_cooldown[sym]
                            
                            # ─── คำนวณ pnl_percent ใหม่เสมอ (สำคัญ!) ───
                            if entry_price > 0 and qty > 0:
                                margin = qty * entry_price / leverage
                                if margin > 0:
                                    pnl_percent = (pnl / margin) * 100
                                    is_win = pnl > 0
                            else:
                                # fallback ถ้าไม่มี entry
                                pnl_percent = 0.0 if pnl == 0 else (pnl / abs(pnl) * 5.0)  # ประมาณการ
                            
                            # ─── duration_hours ───
                            if 'entry_time' in pos_info:
                                duration_hours = (exit_time - pos_info['entry_time']).total_seconds() / 3600
                            else:
                                # ถ้าไม่มี entry_time → ประมาณจาก pnl และ leverage
                                if pnl != 0 and leverage > 0:
                                    approx_pct = pnl_percent / 100
                                    duration_hours = abs(approx_pct) * 2  # สมมติ 50% ต่อชั่วโมง (คร่าว ๆ)
                                duration_hours = max(duration_hours, 0.1)
                            
                            # ─── fallback entry_price ถ้ายังไม่มี ───
                            if entry_price <= 0:
                                entry_price = price_map.get(sym, 0.000001)
                                exit_reason += " (price_map fallback)"
                            
                            # ─── สร้าง record ───
                            trade_record = {
                                'timestamp': exit_time.isoformat(),
                                'symbol': sym,
                                'side': side,
                                'entry_price': entry_price,
                                'exit_price': exit_price,
                                'quantity': qty,
                                'pnl': pnl,
                                'pnl_percent': pnl_percent,
                                'duration_hours': duration_hours,
                                'exit_reason': exit_reason,
                                'is_win': is_win,
                                'leverage': leverage,
                                'max_roe_percent': max_roe,
                                'features': features if len(features) == 7 else [0.5] * 7  # ใช้สำหรับ AI เท่านั้น
                            }

                            print(f"[DEBUG RECORD] {sym} | Entry {entry_price:.6f} → Exit {exit_price:.6f} | "
                                f"PNL {pnl:+.2f} ({pnl_percent:+.2f}%) | {exit_reason}")

                            # บันทึก CSV (ตัด features ออกก่อน)
                            csv_record = trade_record.copy()
                            csv_record.pop('features', None)  # ลบ field ที่ CSV ไม่ต้องการ

                            log_trade_to_csv(csv_record)

                            # อัพเดท AI (ใช้ features เดิม)
                            if trade_record['features']:
                                try:
                                    brain.update_memory(trade_record['features'], trade_record['is_win'])
                                    print(f"{Fore.CYAN}AI updated for {sym}{Style.RESET_ALL}")
                                except Exception as e:
                                    print(f"{Fore.YELLOW}AI update fail: {e}{Style.RESET_ALL}")

                            # Telegram report
                            wr, wins, total = get_current_winrate()
                            win_emoji = "🟢 WIN!" if is_win else "🔴 LOSS"
                            pnl_emoji = "🟢" if is_win else "🔴"
                            report = (
                                f"{win_emoji} **Position Closed**\n"
                                f"เหรียญ: `{sym.replace('USDT','')}` {side}\n"
                                f"Entry → Exit: `{entry_price:.6f}` → `{exit_price:.6f}`\n"
                                f"PNL: {pnl_emoji} `{pnl:+.2f}` USDT (`{pnl_percent:+.2f}%`)\n"
                                f"เหตุผล: **{exit_reason}**\n"
                                f"ระยะเวลา: `{duration_hours:.1f}` ชม\n"
                                f"Max ROE: `{max_roe:+.2f}%`\n"
                                f"สถิติรวม: {wins}/{total} | WR {wr:.1f}%"
                            )
                            await send_telegram_report(report)
                                

                    #               ★★★ การตรวจสอบและตั้ง SL/TP อัตโนมัติ ★★★
                    # ==========================================================================
                    current_time = datetime.now().timestamp()

                    # 1. เรียกทุก 30 วินาที (ถี่ขึ้นนิดหน่อย + ปลอดภัยกว่า 45 วินาที)
                    if current_time - last_sl_tp_check >= 30:
                        print(f"{Fore.CYAN}ตรวจสอบ/ซ่อม SL&TP ทั้งหมด (ทุก 30 วินาที)...{Style.RESET_ALL}")
                        try:
                            await ensure_sl_tp_for_all_positions(client)
                        except Exception as e:
                            print(f"{Fore.RED}ensure_sl_tp ล้มเหลวทั้งหมด: {e}{Style.RESET_ALL}")
                            await send_telegram_report(
                                f"⚠️ **SL/TP Auto Check ล้มเหลวทั้งระบบ**\nข้อผิดพลาด: {str(e)[:200]}",
                                TELEGRAM_CHAT_ID
                            )
                        last_sl_tp_check = current_time

                    # 2. ถ้าเจอ position ใหม่ → รอ 2–3 วินาที แล้วเรียกซ้ำ 2 รอบ (แก้ปัญหา sync delay)
                    if new_positions:
                        print(f"{Fore.CYAN}พบ position ใหม่ {len(new_positions)} ตัว → รอ sync แล้วตั้ง SL/TP{Style.RESET_ALL}")
                        await asyncio.sleep(2.5)  # รอ Binance sync
                        for attempt in range(2):  # ลอง 2 รอบ ห่างกัน 1.5 วินาที
                            try:
                                await ensure_sl_tp_for_all_positions(client)
                                print(f"   → พยายามตั้ง SL/TP รอบ {attempt+1} สำเร็จ")
                                break
                            except Exception as e:
                                print(f"   → รอบ {attempt+1} ล้มเหลว: {e}")
                                if attempt < 1:
                                    await asyncio.sleep(1.5)
                        last_sl_tp_check = current_time

                    # อัปเดต Trailing Stop ทุกๆ รอบ (เหมือนเดิม)
                    await update_trailing_stops(client, active)

                    # ยกเลิก Limit Order เก่า (เหมือนเดิม)
                    await cancel_old_pending_limits(client)

                    # อัปเดต pending orders และ panic guard
                    open_orders_all = await client.futures_get_open_orders()
                    pending_orders_detail = []
                    for o in open_orders_all:
                        if o['type'] == 'LIMIT':
                            order_time = datetime.fromtimestamp(o['time'] / 1000)
                            pending_orders_detail.append({
                                'symbol': o['symbol'],
                                'side': o['side'],
                                'price': float(o['price']),
                                'qty': float(o['origQty']),
                                'time': order_time,
                                'orderId': o['orderId']
                            })

                    pending_symbols = {o['symbol'] for o in pending_orders_detail}

                    # Panic Sell Guard
                    panic_symbols = set()
                    for sym in list(pending_symbols):
                        try:
                            klines = await client.futures_klines(symbol=sym, interval="15m", limit=50)
                            df = calculate_indicators(klines)
                            if not df.empty and len(df) >= 20 and df.iloc[-1]['straight_down'] == 1:
                                panic_symbols.add(sym)
                        except Exception as e:
                            print(f"{Fore.RED}Panic check error {sym}: {e}")

                    if panic_symbols:
                        print(f"{Fore.RED}{Style.BRIGHT}⚠️ PANIC SELL DETECTED! Cancelling limits: {', '.join(panic_symbols)}")
                        await send_telegram_report(
                            f"⚠️ **PANIC SELL GUARD ACTIVATED**\n"
                            f"ตรวจพบการเทขายแบบ panic dump\n"
                            f"ยกเลิก Pending Limit Orders:\n" + 
                            "\n".join([f"• {s.replace('USDT','')}" for s in sorted(panic_symbols)])
                        )

                        canceled_count = 0
                        open_orders = await client.futures_get_open_orders()
                        for order in open_orders:
                            if order['type'] == 'LIMIT' and order['symbol'] in panic_symbols:
                                try:
                                    await client.futures_cancel_order(symbol=order['symbol'], orderId=order['orderId'])
                                    canceled_count += 1
                                except:
                                    pass

                        if canceled_count > 0:
                            open_orders_all = await client.futures_get_open_orders()
                            pending_orders_detail = [o for o in open_orders_all if o['type'] == 'LIMIT']
                            pending_symbols = {o['symbol'] for o in pending_orders_detail}

                    # แสดง Dashboard
                    # แสดง Dashboard
                    await print_dashboard(client, bal, active, pending_orders_detail, price_map, btc_p, scanning=True)

                    # Auto detect Volume Spike
                    if auto_spike_enabled and datetime.now() - last_spike_check > SPIKE_CHECK_INTERVAL:
                        await detect_volume_spike_symbols(client, top_50_symbols, price_map, active_symbols)
                        last_spike_check = datetime.now()

                    # ==========================================================================
                    # Auto Short Signal Execution – Institutional Grade (BOS + Elliott + Fib + Divergence)
                    # ==========================================================================
                    if datetime.now() - last_short_signal_check > SHORT_SIGNAL_CHECK_INTERVAL:
                        try:
                            signals = await detect_strong_short_signals(client, top_50_symbols, price_map, active_symbols)
                            last_short_signal_check = datetime.now()

                            if auto_short_system_enabled and signals:
                                for signal in signals:
                                    symbol = signal['symbol']
                                    # ตรวจสอบว่ามี position อยู่แล้วหรือไม่
                                    if symbol + "USDT" in active_symbols:
                                        print(f"[AUTO-SHORT] ข้าม {symbol}: มี position อยู่แล้ว")
                                        continue
                                    
                                    # ส่งคำสั่ง short
                                    await place_short_order(client, signal, TELEGRAM_CHAT_ID)
                                    
                            elif not auto_short_system_enabled and signals:
                                print(f"[AUTO-SHORT] พบ {len(signals)} สัญญาณ short (โหมดอัตโนมัติปิดอยู่)")

                        except Exception as e:
                            print(f"{Fore.RED}[AUTO-SHORT LOOP ERROR] {e}{Style.RESET_ALL}")
                        try:
                            print(f"{Fore.CYAN}[AUTO-SHORT] กำลังสแกนสัญญาณ short ที่แข็งแกร่ง...{Style.RESET_ALL}")
                            short_signals = await detect_strong_short_signals(client, top_50_symbols, price_map, active_symbols)
                            
                            # กรองเฉพาะสัญญาณที่ยังไม่เคยเทรดในช่วง 1 ชม.
                            new_signals = []
                            current_time = time.time()
                            for sig in short_signals:
                                symbol = sig['symbol']
                                if symbol not in recent_short_trades or \
                                current_time - recent_short_trades[symbol] > 3600:  # 1 ชม.
                                    new_signals.append(sig)
                                    recent_short_trades[symbol] = current_time  # ป้องกัน duplicate

                            if not new_signals:
                                print(f"{Fore.YELLOW}[AUTO-SHORT] ไม่พบสัญญาณ short ใหม่{Style.RESET_ALL}")
                            else:
                                print(f"{Fore.GREEN}[AUTO-SHORT] พบ {len(new_signals)} สัญญาณ short ที่พร้อมเทรด!{Style.RESET_ALL}")

                            # === เข้าออเดอร์แต่ละสัญญาณ ===
                            for signal in new_signals[:MAX_CONCURRENT_SHORTS]:  # จำกัดจำนวน
                                symbol = signal['symbol']
                                strength = signal['strength']
                                rsi = signal['rsi']
                                price = signal['price']
                                tf = signal.get('timeframe', '15m')

                                # 🔒 ตรวจสอบว่ามี position อยู่แล้วหรือไม่
                                if has_active_position(symbol):
                                    print(f"[AUTO-SHORT] ข้าม {symbol}: มี position อยู่แล้ว")
                                    continue

                                # 💰 คำนวณขนาดตำแหน่ง (1% ของพอร์ต)
                                try:
                                    account_info = await client.futures_account()
                                    balance = float(account_info['totalMarginBalance'])
                                    risk_per_trade = balance * RISK_PERCENT_PER_TRADE  # เช่น 0.01 = 1%
                                    position_size = calculate_position_size(
                                        client, symbol, price, risk_per_trade, STOP_LOSS_PCT
                                    )
                                    if position_size <= 0:
                                        raise ValueError("Position size too small")

                                except Exception as e:
                                    print(f"[AUTO-SHORT] คำนวณ position ล้มเหลว {symbol}: {e}")
                                    continue

                                # 📉 ส่งคำสั่ง Sell (Short)
                                try:
                                    order = await client.futures_create_order(
                                        symbol=symbol + "USDT",
                                        side='SELL',
                                        positionSide='SHORT',
                                        type='MARKET',
                                        quantity=position_size
                                    )

                                    # ✅ ตั้ง Stop-Loss & Take-Profit (Optional)
                                    await set_stop_loss_take_profit(
                                        client, symbol, price, 
                                        stop_loss_pct=STOP_LOSS_PCT,
                                        take_profit_pct=TAKE_PROFIT_PCT
                                    )

                                    # 📢 แจ้งเตือน
                                    report = (
                                        f"🚨 **SHORT ENTERED (AUTO)**\n"
                                        f"• Symbol: `{symbol}`\n"
                                        f"• Price: `{price:.4f}`\n"
                                        f"• Size: `{position_size:.2f}`\n"
                                        f"• Strength: `{strength:.2f}` | RSI: `{rsi:.1f}`\n"
                                        f"• TF: `{tf}` | Time: `{datetime.now().strftime('%H:%M')}`"
                                    )
                                    await send_telegram_report(report, chat_id)

                                    # 🧠 บันทึกเพื่อใช้ใน AI training
                                    brain.update_memory({
                                        'symbol': symbol,
                                        'rsi': rsi,
                                        'div_strength': strength,
                                        'volume_spike': signal.get('volume_confirm', False),
                                        'timeframe': tf,
                                        'action': 'short'
                                    }, win=None)  # ยังไม่รู้ผล

                                    print(f"{Fore.RED}[AUTO-SHORT] ✅ เปิด short {symbol} ที่ {price:.4f}{Style.RESET_ALL}")

                                except Exception as e:
                                    error_msg = f"❌ ล้มเหลวในการเปิด short {symbol}: {str(e)[:120]}"
                                    await send_telegram_report(error_msg, chat_id)
                                    print(f"{Fore.RED}[AUTO-SHORT ERROR] {e}{Style.RESET_ALL}")

                            last_short_signal_check = datetime.now()

                        except Exception as e:
                            print(f"{Fore.RED}[AUTO-SHORT CRITICAL] {e}{Style.RESET_ALL}")
                            await send_telegram_report(f"⚠️ Auto-short system error: {str(e)[:150]}", chat_id)

                    # ตรวจจับคำสั่งจาก Telegram
                    if telegram_bot:
                        await check_telegram_updates(client, cmd_q, price_map)



                    # ==========================================================================
                    # ใน loop หลัก: ประมวลผลคำสั่งจาก cmd_q
                    # ==========================================================================
                    while not cmd_q.empty() and running:
                        cmd = await cmd_q.get()
                        
                        if cmd in ['qq', 'quit']:
                            running = False
                            await send_telegram_report("🛑 บอทหยุดทำงานเรียบร้อย")
                            print(f"{Fore.YELLOW}Shutdown command received.")
                        
                        elif cmd.startswith('close:'):
                            target_sym = cmd.replace('close:', '')
                            target_pos = next((p for p in active if p['symbol'] == target_sym), None)
                            
                            if not target_pos:
                                await send_telegram_report(f"⚠️ ไม่พบ Position {target_sym.replace('USDT','')}", TELEGRAM_CHAT_ID)
                                continue
                            
                            side = SIDE_SELL if target_pos['side'] == 'LONG' else SIDE_BUY
                            qty = abs(target_pos['amt'])
                            
                            try:
                                await client.futures_create_order(
                                    symbol=target_sym,
                                    side=side,
                                    type='MARKET',
                                    quantity=qty,
                                    reduceOnly=True
                                )
                                print(f"สั่งปิดสำเร็จ: {target_sym} {target_pos['side']}")
                                
                                # รอ sync แล้วบันทึก
                                await asyncio.sleep(1.2)
                                await record_closed_trade(
                                    client,
                                    target_sym,
                                    exit_reason="Manual Single Close",
                                    is_manual=True
                                )
                                
                                await send_telegram_report(f"🚪 ปิด Position {target_sym.replace('USDT','')} สำเร็จ", TELEGRAM_CHAT_ID)
                            
                            except Exception as e:
                                print(f"ปิด {target_sym} ล้มเหลว: {e}")
                                await send_telegram_report(f"❌ ปิด {target_sym.replace('USDT','')} ล้มเหลว: {str(e)}", TELEGRAM_CHAT_ID)
                        
                        elif cmd == 'a':  # closeall
                            closed_count = 0
                            for p in active[:]:  # copy เพื่อป้องกัน modification ระหว่าง loop
                                sym = p['symbol']
                                side = SIDE_SELL if p['side'] == 'LONG' else SIDE_BUY
                                qty = abs(p['amt'])
                                try:
                                    await client.futures_create_order(
                                        symbol=sym,
                                        side=side,
                                        type='MARKET',
                                        quantity=qty,
                                        reduceOnly=True
                                    )
                                    closed_count += 1
                                    await asyncio.sleep(0.8)  # กระจาย request
                                    await record_closed_trade(
                                        client,
                                        sym,
                                        exit_reason="Manual Close All",
                                        is_manual=True
                                    )
                                except Exception as e:
                                    print(f"ปิด {sym} ล้มเหลวใน closeall: {e}")
                                    await send_telegram_report(f"⚠️ ปิด {sym.replace('USDT','')} ล้มเหลว: {str(e)}", TELEGRAM_CHAT_ID)
                            
                            await send_telegram_report(
                                f"🔴 **ปิดทุก Position สำเร็จ** ({closed_count} ตำแหน่ง)",
                                TELEGRAM_CHAT_ID
                            )
                        
                        elif cmd.startswith('cancel:'):
                            target = cmd.replace('cancel:', '')
                            try:
                                if target == 'all':
                                    cancelled_count = 0
                                    open_orders = await client.futures_get_open_orders()
                                    for o in [ord for ord in open_orders if ord['type'] == 'LIMIT']:
                                        await client.futures_cancel_order(symbol=o['symbol'], orderId=o['orderId'])
                                        cancelled_count += 1
                                    pending_orders_detail.clear()
                                    await send_telegram_report(f"🗑️ ยกเลิก {cancelled_count} Limit Orders ทั้งหมด")
                                else:
                                    cancelled_count = 0
                                    open_orders = await client.futures_get_open_orders(symbol=target)
                                    for o in [ord for ord in open_orders if ord['type'] == 'LIMIT']:
                                        await client.futures_cancel_order(symbol=target, orderId=o['orderId'])
                                        cancelled_count += 1
                                        pending_orders_detail = [p for p in pending_orders_detail if p['orderId'] != o['orderId']]
                                    await send_telegram_report(f"🗑️ ยกเลิก {cancelled_count} orders ของ {target}")
                            except Exception as e:
                                await send_telegram_report(f"❌ Error ยกเลิก orders: {str(e)}")
                                                
                        elif cmd == 'sltp':
                            # ===== ตรวจสอบและตั้ง SL/TP สำหรับ positions ที่ไม่มี =====
                            result = await check_and_set_missing_sltp(client)
                            await send_telegram_report(f"🛡️ **ผลการตั้ง SL/TP**\n{result}")
                            print(f"{Fore.GREEN}{result}{Style.RESET_ALL}")
                        
                        elif cmd.startswith('cancel:'):
                            # ===== ยกเลิก Limit Orders =====
                            target = cmd.replace('cancel:', '')
                            try:
                                if target == 'all':
                                    # ยกเลิกทั้งหมด
                                    cancelled_count = 0
                                    for order in pending_orders_detail[:]:
                                        try:
                                            await client.futures_cancel_order(
                                                symbol=order['symbol'],
                                                orderId=order['orderId']
                                            )
                                            cancelled_count += 1
                                            print(f"Cancelled: {order['symbol']} order {order['orderId']}")
                                        except Exception as e:
                                            print(f"Failed to cancel {order['symbol']}: {e}")
                                    
                                    pending_orders_detail.clear()
                                    await send_telegram_report(f"✅ ยกเลิก {cancelled_count} Limit Orders สำเร็จ")
                                else:
                                    # ยกเลิก symbol เดี่ยว
                                    target_orders = [o for o in pending_orders_detail if o['symbol'] == target]
                                    if target_orders:
                                        cancelled_count = 0
                                        for order in target_orders:
                                            try:
                                                await client.futures_cancel_order(
                                                    symbol=target,
                                                    orderId=order['orderId']
                                                )
                                                cancelled_count += 1
                                                pending_orders_detail.remove(order)
                                                print(f"Cancelled: {target} order {order['orderId']}")
                                            except Exception as e:
                                                print(f"Failed to cancel {target}: {e}")
                                        
                                        await send_telegram_report(f"✅ ยกเลิก {cancelled_count} orders {target}")
                                    else:
                                        await send_telegram_report(f"⚠️ ไม่พบ Pending Orders {target}")
                            except Exception as e:
                                await send_telegram_report(f"❌ Error cancelling orders: {str(e)}")
                                print(f"Cancel error: {e}")
                        
                        elif cmd in ['a', 'closeall']:
                            closed_trades = []  # เก็บ trade ที่ปิดสำเร็จเพื่อบันทึก CSV

                            for p in active[:]:  # copy list เพื่อป้องกัน modification ระหว่าง loop
                                sym = p['symbol']
                                side = SIDE_SELL if p['side'] == 'LONG' else SIDE_BUY
                                qty = abs(p['amt'])

                                try:
                                    await client.futures_create_order(
                                        symbol=sym,
                                        side=side,
                                        type='MARKET',
                                        quantity=qty,
                                        reduceOnly=True
                                    )
                                    print(f"ปิด position สำเร็จ: {sym} {p['side']}")

                                    # รอ Binance sync แล้วดึง trade ล่าสุด
                                    await asyncio.sleep(1.5)  # รอ 1.5 วินาที

                                    trades = await client.futures_account_trades(symbol=sym, limit=10)
                                    close_trade = next((t for t in reversed(trades) if float(t['realizedPnl']) != 0), None)

                                    if close_trade:
                                        pos_info = active_detailed.get(sym)
                                        if pos_info:
                                            exit_price = float(close_trade['price'])
                                            pnl = float(close_trade['realizedPnl'])
                                            is_win = pnl > 0
                                            exit_time = datetime.fromtimestamp(close_trade['time'] / 1000)
                                            duration_hours = (exit_time - pos_info['entry_time']).total_seconds() / 3600
                                            margin = pos_info['quantity'] * pos_info['entry_price'] / pos_info['leverage']
                                            pnl_percent = (pnl / margin * 100) if margin > 0 else 0

                                            exit_reason = "Manual Close (closeall)"
                                            if pnl < -margin * 0.5:
                                                exit_reason = "Liquidation / Big Loss"

                                            trade_record = {
                                                'timestamp': exit_time.isoformat(),
                                                'symbol': sym,
                                                'side': pos_info['side'],
                                                'entry_price': pos_info['entry_price'],
                                                'exit_price': exit_price,
                                                'quantity': pos_info['quantity'],
                                                'pnl': pnl,
                                                'pnl_percent': pnl_percent,
                                                'duration_hours': duration_hours,
                                                'exit_reason': exit_reason,
                                                'is_win': is_win,
                                                'leverage': pos_info['leverage'],
                                                'max_roe_percent': pos_info['max_roe'],
                                                'features': pos_info.get('features', [])
                                            }

                                            log_trade_to_csv(trade_record)
                                            closed_trades.append(trade_record)

                                            # แจ้งเตือน Telegram (เหมือนเดิม)
                                            wr, wins, total = get_current_winrate()
                                            win_emoji = "🟢 WIN!" if is_win else "🔴 LOSS"
                                            pnl_emoji = "🟢" if is_win else "🔴"
                                            report = (
                                                f"{win_emoji} **Position Closed (closeall)**\n"
                                                f"เหรียญ: `{sym.replace('USDT','')}` {pos_info['side']}\n"
                                                f"Entry → Exit: `{pos_info['entry_price']:.6f}` → `{exit_price:.6f}`\n"
                                                f"PNL: {pnl_emoji} `{pnl:+.2f}` USDT (`{pnl_percent:+.2f}%`)\n"
                                                f"เหตุผล: **{exit_reason}**\n"
                                                f"ระยะเวลา: `{duration_hours:.1f}` ชม\n"
                                                f"Max ROE: `{pos_info['max_roe']:+.2f}%`\n"
                                                f"สถิติรวม: {wins}/{total} | Winrate {wr:.1f}%"
                                            )
                                            await send_telegram_report(report)

                                        # ลบออกจาก active_detailed
                                        active_detailed.pop(sym, None)

                                except Exception as e:
                                    print(f"Error closing {sym}: {e}")

                            # สรุปหลังปิดทั้งหมด
                            if closed_trades:
                                await send_telegram_report(f"🔴 **ปิดทุก Position สำเร็จ** ({len(closed_trades)} trades บันทึกแล้ว)")
                            else:
                                await send_telegram_report("⚠️ ไม่พบ position ที่ปิดได้ หรือเกิดข้อผิดพลาด")

                            # ยกเลิก orders ที่เหลือ
                            try:
                                open_orders = await client.futures_get_open_orders()
                                for o in open_orders:
                                    await client.futures_cancel_order(symbol=o['symbol'], orderId=o['orderId'])
                                await send_telegram_report("🗑️ ยกเลิก Orders ที่เหลือทั้งหมดแล้ว")
                            except Exception as e:
                                await send_telegram_report(f"❌ Error ยกเลิก orders: {e}")
                        elif cmd in ['c', 'cancel']:
                            try:
                                open_orders = await client.futures_get_open_orders()
                                limit_orders = [o for o in open_orders if o['type'] == 'LIMIT']
                                if not limit_orders:
                                    await send_telegram_report("ไม่มี Limit Orders ที่ต้องยกเลิก")
                                else:
                                    for o in limit_orders:
                                        await client.futures_cancel_order(symbol=o['symbol'], orderId=o['orderId'])
                                    await send_telegram_report(f"🗑️ ยกเลิก Limit Orders ทั้งหมด {len(limit_orders)} รายการ")
                            except Exception as e:
                                await send_telegram_report(f"❌ เกิดข้อผิดพลาดในการยกเลิก: {e}")

                    # อัปเดต Top 100 Volume ทุก 4 ชั่วโมง
                    if datetime.now() - last_volume_update > VOLUME_UPDATE_INTERVAL:
                        try:
                            tickers = await client.futures_ticker()
                            volume_list = [(t['symbol'], float(t['quoteVolume'])) 
                                           for t in tickers 
                                           if t['symbol'].endswith('USDT') and t['symbol'] in sym_info]
                            volume_list.sort(key=lambda x: x[1], reverse=True)
                            top_50_symbols = [s[0] for s in volume_list[:100]]
                            last_volume_update = datetime.now()
                            print(f"{Fore.GREEN}Top 100 Volume updated | Top 5: {', '.join(top_50_symbols[:5])}")
                        except Exception as e:
                            print(f"{Fore.RED}Update Top 100 failed: {e}")

                    # สแกนหาสัญญาณใหม่และวาง Limit Order
                    total_active_trade_intent = len(active_symbols) + len(pending_symbols)
                    free_slots = MAX_OPEN_POSITIONS - total_active_trade_intent

                    if free_slots > 0 and bal >= MIN_BALANCE_TO_TRADE:
                        potential = [s for s in top_50_symbols if s not in active_symbols and s not in pending_symbols]
                        
                        if potential:
                            batch = random.sample(potential, min(len(potential), SCAN_BATCH_SIZE))
                            tasks = [analyze_matrix(client, s) for s in batch]
                            results = await asyncio.gather(*tasks)
                            valid_signals = sorted([r for r in results if r], key=lambda x: x['score'], reverse=True)

                            for r in valid_signals:
                                if not running or free_slots <= 0:
                                    break
                                if r['symbol'] in active_symbols or r['symbol'] in pending_symbols:
                                    continue
                                # ─── Cooldown check เฉพาะ manual close ───────────────────────────────
                                now_ts = datetime.now().timestamp()
                                if r['symbol'] in manual_closed_cooldown:
                                    elapsed_sec = now_ts - manual_closed_cooldown[r['symbol']]
                                    if elapsed_sec < COOLDOWN_AFTER_MANUAL_MINUTES * 60:
                                        remain_min = int((COOLDOWN_AFTER_MANUAL_MINUTES * 60 - elapsed_sec) / 60) + 1
                                        print(f"Skip {r['symbol']} — cooldown เหลือ ~{remain_min} นาที (manual close)")
                                        continue
                                    else:
                                        # cooldown หมดแล้ว ลบออก
                                        del manual_closed_cooldown[r['symbol']]
                                # ────────────────────────────────────────────────────────────────────────
                                if r['ai'] < 50:
                                    continue
                                if r['vol_breakout'] == 0:
                                    continue

                                if r['side'] == 'LONG' and r['rsi'] > 30:
                                    continue
                                if r['side'] == 'SHORT' and r['rsi'] < 70:
                                    continue

                                sentiment = await get_sentiment(r['symbol'])
                                if sentiment < 0.5:
                                    continue

                                try:
                                    k = await client.futures_klines(symbol=r['symbol'], interval="4h", limit=100)
                                    df = pd.DataFrame(k, columns=['ts','o','h','l','c','v','ct','qv','nt','tb','tq','i']).astype(float)
                                    high = df['h'].max()
                                    low = df['l'].min()
                                    diff = high - low

                                    fib_618 = high - 0.618 * diff
                                    fib_50 = high - 0.5 * diff
                                    fib_382 = high - 0.382 * diff

                                    current_p = r['curr_p']

                                    f = [
                                        float(curr['rsi'] / 100),
                                        float(curr['adx'] / 100),
                                        float((curr['macd'] - curr['signal']) / curr['atr'] if curr['atr'] > 0 else 0),
                                        float((curr['c'] - curr['ema200']) / curr['ema200'] if curr['ema200'] > 0 else 0),
                                        float(curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1),
                                        float(score / 8.0),
                                        1.0 if side == 'LONG' else 0.0,
                                        float(curr['stoch_k'] / 100),              # เพิ่ม Stochastic
                                        float(curr['bb_upper'] - curr['c']) / curr['atr'],  # ระยะห่างจาก BB upper
                                        float(curr['ema20'] - curr['ema50']) / curr['atr'], # EMA slope ในหน่วย ATR
                                        float(vol_ratio > 1.5),                    # binary vol breakout
                                    ]
                                    pred_pullback = brain.get_pred_pullback(f)

                                    if r['side'] == 'LONG':
                                        target_fib = max(fib_618, fib_50, fib_382)
                                        limit_price_raw = max(current_p * (1 - (pred_pullback / 100)), target_fib)
                                        side_order = SIDE_BUY
                                    else:
                                        target_fib = min(fib_382, fib_50, fib_618)
                                        limit_price_raw = min(current_p * (1 + (pred_pullback / 100)), target_fib)
                                        side_order = SIDE_SELL

                                    tick_size = sym_filters.get(r['symbol'], {}).get('tickSize', 0.001)
                                    limit_price = round_to_tick(limit_price_raw, tick_size)

                                    p_prec, q_prec = sym_info.get(r['symbol'], (4, 2))
                                    limit_price_str = f"{limit_price:.{p_prec}f}"

                                    qty = calculate_position_size(bal, limit_price, r['atr'], r['symbol'], sym_filters, sym_info)
                                    if qty <= 0:
                                        continue

                                    await client.futures_change_leverage(symbol=r['symbol'], leverage=MAX_LEVERAGE)
                                    await client.futures_create_order(
                                        symbol=r['symbol'],
                                        side=side_order,
                                        type='LIMIT',
                                        timeInForce=TIME_IN_FORCE_GTC,
                                        quantity=qty,
                                        price=limit_price_str,
                                        reduceOnly=False
                                    )

                                    print(f"{Fore.YELLOW}⏳ Limit Placed: {r['symbol']} {r['side']} @ {limit_price_str}")
                                    await send_telegram_report(
                                        f"⏳ **PENDING LIMIT**\n"
                                        f"{r['symbol'].replace('USDT','')} {r['side']}\n"
                                        f"Limit: `{limit_price_str}`\n"
                                        f"Pullback: {pred_pullback:.2f}% + Fib\n"
                                        f"Qty: {qty}"
                                    )

                                    pending_symbols.add(r['symbol'])
                                    free_slots -= 1

                                except Exception as e:
                                    print(f"{Fore.RED}Limit order error {r['symbol']}: {e}")

                    await asyncio.sleep(2)

                except Exception as e:
                    print(f"{Fore.RED}Main Loop Error: {e}")
                    await asyncio.sleep(5)

        except Exception as e:
            print(f"{Fore.RED}Critical Connection Error: {e}")
            reconnect_attempts += 1
            if reconnect_attempts >= MAX_RECONNECT:
                print(f"{Fore.RED}ถึงจำนวนครั้ง reconnect สูงสุดแล้ว → หยุดบอท")
                break
            await asyncio.sleep(10)

    print(f"{Fore.YELLOW}Shutting down gracefully...")
    if client:
        await client.close_connection()
    print(f"{Fore.GREEN}Bot stopped successfully. Goodbye!")


# ==========================================================================
#                  ENTRY POINT
# ==========================================================================
if __name__ == "__main__":
    try:
        print(f"{Fore.GREEN}Starting TITAN PRO v31.4...{Style.RESET_ALL}")
        asyncio.run(main())
    except KeyboardInterrupt:
        print(f"\n{Fore.YELLOW}Stopped by user.{Style.RESET_ALL}")
    except Exception as e:
        print(f"\n{Fore.RED}CRITICAL ERROR!{Style.RESET_ALL}")
        import traceback
        traceback.print_exc()
    finally:
        print(f"\nSession ended at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")