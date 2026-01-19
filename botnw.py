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

# --- LOAD ENV FIRST ---
load_dotenv()

# --- INITIALIZE ---
init(autoreset=True)
warnings.filterwarnings("ignore")

# ==========================================================================
#                          TELEGRAM CONFIG
# ==========================================================================
TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID")

telegram_bot = None
update_offset = None
running = True

# ==========================================================================
# เพิ่มตัวแปร global สำหรับ cooldown (เฉพาะ manual close)
# ==========================================================================
manual_closed_cooldown = {}           # sym → timestamp ที่ปิดด้วยมือล่าสุด
COOLDOWN_AFTER_MANUAL_MINUTES = 90    # 90 นาที = 1.5 ชม. (ปรับได้ตามต้องการ)

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
prev_prices = {}
ticker_offset = 0
ticker_direction = 1

last_sl_tp_check = 0.0   # หรือ datetime.min.timestamp()

bal = 0.0
active = []                 # สำหรับแสดง dashboard (เหมือนเดิม)
active_detailed = {}        # ข้อมูล position เปิดแบบละเอียด (สำคัญ!)
btc_p = 0.0
pending_orders_detail = []
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

TRAILING_ACTIVATION_MULTIPLIER = 1.8
TRAILING_DELTA_MULTIPLIER = 1.3

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

MAX_LEVERAGE = 15
RISK_PER_TRADE_PERCENT = 0.02
MAX_OPEN_POSITIONS = 5
SIGNAL_THRESHOLD_LONG = 8
SIGNAL_THRESHOLD_SHORT = 9
ADX_THRESHOLD = 28
SCAN_BATCH_SIZE = 40
MIN_NOTIONAL_USDT = 5
MIN_BALANCE_TO_TRADE = 20.0

ENTRY_PULLBACK_PERCENT = 25.0
LIMIT_ORDER_TIMEOUT_HOURS = 2

ATR_SL_MULTIPLIER = 2.0
ATR_TP_MULTIPLIER = 4.0

MAJOR_TICKER_SYMBOLS = [
    'BTCUSDT', 'ETHUSDT', 'SOLUSDT', 'BNBUSDT', 'XRPUSDT', 'ADAUSDT',
    'DOGEUSDT', 'AVAXUSDT', 'LINKUSDT', 'DOTUSDT', 'TRXUSDT', 'MATICUSDT',
    'LTCUSDT', 'BCHUSDT', 'NEARUSDT', 'UNIUSDT', 'SUIUSDT', 'APTUSDT'
]

prev_prices = {sym: 0.0 for sym in MAJOR_TICKER_SYMBOLS}

# ==========================================================================
def log_trade_to_csv(trade_data: dict):
    """บันทึก trade ลง CSV และอัพเดท brain memory (เวอร์ชันสมบูรณ์)"""
    try:
        # ถ้า timestamp เป็น datetime → แปลงเป็น ISO string
        if isinstance(trade_data.get('timestamp'), datetime):
            trade_data['timestamp'] = trade_data['timestamp'].isoformat()

        row = {k: trade_data.get(k, '') for k in TRADE_HISTORY_FIELDS}

        with open(TRADE_HISTORY_FILE, 'a', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=TRADE_HISTORY_FIELDS)
            writer.writerow(row)

        print(f"{Fore.GREEN}บันทึก trade → {trade_data.get('symbol','?')} | PNL {trade_data.get('pnl',0):+.2f}{Style.RESET_ALL}")

        # อัพเดท AI brain
        features = trade_data.get('features', [])
        if features and isinstance(features, (list, tuple)):
            try:
                brain.update_memory(features, trade_data['is_win'])
            except Exception as brain_err:
                print(f"{Fore.YELLOW}AI memory update ล้มเหลว: {brain_err}{Style.RESET_ALL}")

    except Exception as e:
        print(f"{Fore.RED}Error logging trade to CSV: {e}{Style.RESET_ALL}")
    try:
        with open(TRADE_HISTORY_FILE, 'a', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=TRADE_HISTORY_FIELDS)
            writer.writerow(trade_data)
        
        features = trade_data.get('features', [])
        if features:
            brain.update_memory(features, trade_data['is_win'])
    except Exception as e:
        print(f"{Fore.RED}Error logging trade: {e}")

# แก้ในฟังก์ชัน get_current_winrate() ให้แข็งแรงขึ้นหน่อย
def get_current_winrate():
    try:
        df = pd.read_csv(TRADE_HISTORY_FILE)
        if df.empty:
            return 0.0, 0, 0
        
        # กรองเฉพาะ trade ที่มี exit_price และ pnl ชัดเจน
        df_valid = df.dropna(subset=['exit_price', 'pnl'])
        
        total = len(df_valid)
        wins = len(df_valid[df_valid['is_win'] == True])
        winrate = (wins / total * 100) if total > 0 else 0.0
        
        return winrate, wins, total
    except FileNotFoundError:
        print("⚠️ ไม่พบไฟล์ trade history → winrate = 0%")
        return 0.0, 0, 0
    except Exception as e:
        print(f"Error reading trade history: {e}")
        return 0.0, 0, 0

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
#          MULTI-TIMEFRAME CONFIRMATION
# ==========================================================================
async def check_htf_bearish_alignment(client, symbol):
    """ตรวจสอบ 4H ว่าเป็น bearish alignment (สำหรับ SHORT)"""
    try:
        htf_klines = await client.futures_klines(symbol=symbol, interval="4h", limit=100)
        df_htf = calculate_indicators(htf_klines)
        if df_htf.empty:
            return False
        
        curr = df_htf.iloc[-1]
        # ต้อง: EMA20 < EMA50 < EMA200 เท่านั้น
        return curr['ema20'] < curr['ema50'] < curr['ema200']
    except Exception as e:
        print(f"HTF check error {symbol}: {e}")
        return False

async def check_htf_bullish_alignment(client, symbol):
    """ตรวจสอบ 4H ว่าเป็น bullish alignment (สำหรับ LONG)"""
    try:
        htf_klines = await client.futures_klines(symbol=symbol, interval="4h", limit=100)
        df_htf = calculate_indicators(htf_klines)
        if df_htf.empty:
            return False
        
        curr = df_htf.iloc[-1]
        # ต้อง: EMA20 > EMA50 > EMA200 เท่านั้น
        return curr['ema20'] > curr['ema50'] > curr['ema200']
    except Exception as e:
        print(f"HTF check error {symbol}: {e}")
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
async def ensure_sl_tp_for_all_positions(client):
    """
    ตรวจสอบและสร้าง/ซ่อม SL & TP สำหรับทุก position ที่เปิดอยู่
    พร้อม debug log ละเอียด + จัดการ error ที่พบบ่อย (เช่น -4130)
    """
    try:
        print(f"{Fore.CYAN}=== เริ่มตรวจสอบและตั้ง SL/TP อัตโนมัติทั้งหมด ==={Style.RESET_ALL}")
        print(f"{Fore.CYAN}เวลาเริ่ม: {datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')}{Style.RESET_ALL}")

        positions = await client.futures_position_information()
        active_positions = [p for p in positions if float(p['positionAmt']) != 0]

        print(f"{Fore.CYAN}พบ position เปิดอยู่: {len(active_positions)} ตำแหน่ง{Style.RESET_ALL}")

        if not active_positions:
            print(f"{Fore.LIGHTBLACK_EX}ไม่มี position เปิด → จบการตรวจสอบ{Style.RESET_ALL}")
            return

        for pos in active_positions:
            sym = pos['symbol']
            amt = float(pos['positionAmt'])
            if amt == 0:
                continue

            position_side = 'LONG' if amt > 0 else 'SHORT'
            close_side = SIDE_SELL if position_side == 'LONG' else SIDE_BUY
            entry_price = float(pos['entryPrice'])

            print(f"\n{Fore.MAGENTA}=== ตรวจสอบ {sym} ({position_side}) ==={Style.RESET_ALL}")
            print(f"   จำนวน: {amt}")
            print(f"   Entry Price: {entry_price:.6f}")

            # ดึงราคาปัจจุบัน (fallback ถ้า markPrice ไม่มี)
            current_price = float(pos.get('markPrice', 0))
            if current_price <= 0:
                try:
                    ticker = await client.futures_symbol_ticker(symbol=sym)
                    current_price = float(ticker['price'])
                    print(f"   ราคาปัจจุบัน (จาก ticker): {current_price:.6f}")
                except Exception as e:
                    print(f"   ไม่สามารถดึงราคาปัจจุบันได้ → ข้าม: {e}")
                    continue

            # ดึง ATR
            atr = await get_cached_atr(client, sym)
            if atr is None or atr <= 0:
                atr = entry_price * 0.015  # fallback
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

            print(f"   SL คำนวณ: {sl_raw:.6f} → ปัดเป็น {sl_str}")
            print(f"   TP คำนวณ: {tp_raw:.6f} → ปัดเป็น {tp_str}")

            # ตรวจสอบ orders ที่มีอยู่
            try:
                orders = await client.futures_get_open_orders(symbol=sym)
                print(f"   พบ open orders: {len(orders)} รายการ")
            except Exception as e:
                print(f"   ดึง open orders ล้มเหลว: {e}")
                continue

            has_sl = any(o['type'] == 'STOP_MARKET' and o.get('closePosition', False) for o in orders)
            has_tp = any(o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False) for o in orders)

            print(f"   สถานะปัจจุบัน → SL: {'มี' if has_sl else 'ไม่มี'}, TP: {'มี' if has_tp else 'ไม่มี'}")

            if has_sl and has_tp:
                print(f"   มี SL และ TP ครบแล้ว → ข้าม {sym}")
                continue

            actions_taken = []

            # ตั้ง SL
            if not has_sl:
                print(f"   กำลังตั้ง SL ใหม่ @ {sl_str}")
                for attempt in range(3):
                    try:
                        await client.futures_create_order(
                            symbol=sym,
                            side=close_side,
                            type='STOP_MARKET',
                            stopPrice=sl_str,
                            closePosition=True,
                            timeInForce='GTC',
                            workingType='MARK_PRICE'
                        )
                        actions_taken.append(f"SL ใหม่ @ {sl_str}")
                        print(f"   {Fore.GREEN}ตั้ง SL สำเร็จ (attempt {attempt+1}){Style.RESET_ALL}")
                        break

                    except BinanceAPIException as e:
                        print(f"   ตั้ง SL ล้มเหลว (attempt {attempt+1}): code={e.code} - {e.message}")
                        
                        if e.code in [-2022, -1106, -2019, -4130]:
                            print(f"   {Fore.YELLOW}พบว่ามี SL อยู่แล้ว (code {e.code}) → ถือว่าสำเร็จ{Style.RESET_ALL}")
                            actions_taken.append(f"SL มีอยู่แล้ว @ {sl_str}")
                            break
                        
                        elif attempt < 2:
                            await asyncio.sleep(1.5)
                            continue
                        
                        else:
                            print(f"   {Fore.RED}ตั้ง SL ล้มเหลวถาวร{Style.RESET_ALL}")

            # ตั้ง TP
            if not has_tp:
                print(f"   กำลังตั้ง TP ใหม่ @ {tp_str}")
                for attempt in range(3):
                    try:
                        await client.futures_create_order(
                            symbol=sym,
                            side=close_side,
                            type='TAKE_PROFIT_MARKET',
                            stopPrice=tp_str,
                            closePosition=True,
                            timeInForce='GTC',
                            workingType='MARK_PRICE'
                        )
                        actions_taken.append(f"TP ใหม่ @ {tp_str}")
                        print(f"   {Fore.GREEN}ตั้ง TP สำเร็จ (attempt {attempt+1}){Style.RESET_ALL}")
                        break

                    except BinanceAPIException as e:
                        print(f"   ตั้ง TP ล้มเหลว (attempt {attempt+1}): code={e.code} - {e.message}")
                        
                        if e.code in [-2022, -1106, -2019, -4130]:
                            print(f"   {Fore.YELLOW}พบว่ามี TP อยู่แล้ว (code {e.code}) → ถือว่าสำเร็จ{Style.RESET_ALL}")
                            actions_taken.append(f"TP มีอยู่แล้ว @ {tp_str}")
                            break
                        
                        elif attempt < 2:
                            await asyncio.sleep(1.5)
                            continue
                        
                        else:
                            print(f"   {Fore.RED}ตั้ง TP ล้มเหลวถาวร{Style.RESET_ALL}")

                # สรุปผล + แจ้งเตือน Telegram
                if actions_taken:
                    print(f"   ดำเนินการเรียบร้อย: {' + '.join(actions_taken)}")

                    updated = False  # ✅ ต้องประกาศก่อน

                    # อัพเดท active dict ทันทีเพื่อให้ /positions เห็นค่า SL/TP ล่าสุด
                    for pos in active:
                        if pos['symbol'] == sym:
                            try:
                                # ดึง orders ล่าสุดหลังตั้ง (เพื่อความแน่นอน)
                                orders = await client.futures_get_open_orders(symbol=sym)

                                sl = tp = 0.0
                                for o in orders:
                                    if o['type'] == 'STOP_MARKET' and o.get('closePosition', False):
                                        sl = float(o['stopPrice'])
                                    elif o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False):
                                        tp = float(o['stopPrice'])

                                pos['sl'] = sl
                                pos['tp'] = tp

                                updated = True  # ✅ อัพเดทสำเร็จ
                                print(f"   อัพเดท active สำหรับ {sym}: SL={sl:.6f}, TP={tp:.6f}")

                            except Exception as e:
                                print(f"   อัพเดท active ล้มเหลว {sym}: {e}")

                            break  # เจอ symbol แล้ว ไม่ต้อง loop ต่อ

                    if not updated:
                        print(f"   ⚠️ ไม่พบ {sym} ใน active list เพื่ออัพเดท SL/TP")

                # แจ้งเตือนเฉพาะเมื่อมีการตั้งใหม่จริง หรือเป็นครั้งแรก
                if sym not in sl_tp_advice_notified or any("ใหม่" in a for a in actions_taken):
                    status_text = "ตั้งใหม่สำเร็จบางส่วน" if any("ใหม่" in a for a in actions_taken) else "ตรวจพบว่ามีอยู่แล้ว"
                    msg = (
                        f"🛡️ **การตั้ง SL/TP อัตโนมัติ - {sym.replace('USDT','')}**\n"
                        f"• ทิศทาง: **{position_side}**\n"
                        f"• ราคาเข้า: `{entry_price:.6f}`\n"
                        f"• ดำเนินการ: {' + '.join(actions_taken)}\n"
                        f"• ATR ที่ใช้: `{atr:.6f}`\n"
                        f"• สถานะ: {status_text}"
                    )
                    await send_telegram_report(msg)
                    sl_tp_advice_notified.add(sym)  # บล็อกไม่ให้แจ้งซ้ำอีก

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
                reduceOnly=True
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
        self.batch_norm1 = nn.BatchNorm1d(hidden_size)
        self.batch_norm2 = nn.BatchNorm1d(hidden_size // 2)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = self.batch_norm1(x)
        x = self.dropout1(x)
        x = torch.relu(self.fc2(x))
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
        
        # ★ ตรวจสอบ input size จริงจาก data
        if self.data:
            input_size = len(self.data[0][0])  # Get actual feature count
            print(f"{Fore.CYAN}🧠 Loading AI: detected {input_size} features from {len(self.data)} trades{Style.RESET_ALL}")
        else:
            input_size = 10  # Default if empty
            print(f"{Fore.YELLOW}⚠️  No trade data yet, using default 10 features{Style.RESET_ALL}")
        
        self.model = SimpleMLP(input_size, hidden_size=64)
        self.best_loss = float('inf')
        self.training_history = []
        self.accuracy_history = []
        self.load_stats()
        
        # Load model dengan error handling
        if os.path.exists(self.model_file):
            try:
                state_dict = torch.load(self.model_file)
                self.model.load_state_dict(state_dict)
                print(f"{Fore.GREEN}✅ โหลด AI Model สำเร็จ{Style.RESET_ALL}")
            except Exception as e:
                print(f"{Fore.YELLOW}⚠️ โหลด Model ล้มเหลว ({e}) → สร้างใหม่{Style.RESET_ALL}")
                # Reinitialize model
                self.model = SimpleMLP(input_size, hidden_size=64)
        
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
        if len(self.data) < 10:
            return
        
        optimizer = optim.Adam(self.model.parameters(), lr=0.001)
        loss_fn = nn.BCELoss()
        epochs = 150
        batch_size = min(16, len(self.data) // 2)
        
        self.model.train()
        epoch_losses = []
        
        for epoch in range(epochs):
            indices = list(range(len(self.data)))
            np.random.shuffle(indices)
            batch_loss = 0.0
            
            for i in range(0, len(self.data), batch_size):
                batch_indices = indices[i:i+batch_size]
                batch = [self.data[idx] for idx in batch_indices]
                X_batch = torch.stack([x for x, y in batch])
                y_batch = torch.tensor([[y] for x, y in batch], dtype=torch.float32)
                
                pred = self.model(X_batch)
                loss = loss_fn(pred, y_batch)
                optimizer.zero_grad()
                loss.backward()
                torch.nn.utils.clip_grad_norm_(self.model.parameters(), 1.0)
                optimizer.step()
                
                batch_loss += loss.item()
            
            epoch_losses.append(batch_loss / max(1, len(self.data) // batch_size))
            
            # Early stopping
            if epoch_losses[-1] < self.best_loss:
                self.best_loss = epoch_losses[-1]
        
        self.training_history.append(epoch_losses[-1])
        self.calculate_accuracy()
        self.save_memory()

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
        """ดึง AI training statistics"""
        return {
            'total_trades': len(self.data),
            'last_accuracy': self.accuracy_history[-1] if self.accuracy_history else 0.0,
            'avg_accuracy': sum(self.accuracy_history) / len(self.accuracy_history) if self.accuracy_history else 0.0,
            'best_loss': self.best_loss,
            'last_loss': self.training_history[-1] if self.training_history else 0.0,
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
        if photo:
            await telegram_bot.send_photo(chat_id=target, photo=photo, caption=text, parse_mode="Markdown")
        else:
            await telegram_bot.send_message(chat_id=target, text=text, parse_mode="Markdown")
    except TelegramError as e:
        print(f"{Fore.RED}Telegram send error: {e}")

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
            
            gap_price = abs(o['price'] - curr_p)
            gap_pct = (gap_price / curr_p * 100) if curr_p > 0 else 0.0
            gap_color = Fore.GREEN if gap_pct < 1.0 else Fore.YELLOW if gap_pct < 3.0 else Fore.RED
            
            age_h = (datetime.now() - o['time']).total_seconds() / 3600
            age_str = f"{Fore.RED}{Style.BRIGHT}OLD! {age_h:.1f}h{Style.NORMAL}" if age_h > LIMIT_ORDER_TIMEOUT_HOURS else f"{Fore.WHITE}{age_h:.1f}h"
            status = f"{Fore.RED}{Style.BRIGHT}⚠️ จะถูกยกเลิก!{Style.NORMAL}" if age_h > LIMIT_ORDER_TIMEOUT_HOURS else ""

            print(f" {Fore.YELLOW}{Style.BRIGHT}{i:<4}{Style.NORMAL} "
                  f"{Fore.WHITE}{sym_no_usdt:<12} "
                  f"{side_color}{side_label:<12}{Fore.WHITE} "
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
async def detect_volume_spike_symbols(client, symbols, price_map, active_symbols):
    tfs = ['3m', '15m', '30m', '1h', '4h']
    results = []
    for sym in symbols:
        spike_data = {}
        max_ratio = 0
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
                vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 0
                
                if vol_ratio > 2.5:  # เพิ่ม threshold นิดนึงเพราะเข้า auto
                    spike_data[tf] = vol_ratio
                    if vol_ratio > max_ratio:
                        max_ratio = vol_ratio
                        best_tf = tf
                        best_atr = curr['atr']
                        best_price = curr['c']
                        best_support = float(curr.get('support', 0))
                        best_resistance = float(curr.get('resistance', 0))
                        
            except Exception as e:
                print(f"{Fore.RED}Spike detect error {sym} {tf}: {e}")
        
        if best_tf and sym not in active_symbols:  # ไม่เข้าใหม่ถ้ามี position แล้ว
            # ===== Get Full DF for confirmation checks =====
            try:
                full_klines = await client.futures_klines(symbol=sym, interval=best_tf, limit=50)
                df_full = calculate_indicators(full_klines)
            except:
                continue
            
            if df_full.empty:
                continue
            
            curr = df_full.iloc[-1]
            
            # ===== NEW FILTERS FOR LONG =====
            # 1. Stochastic Confirmation (Stoch < 20 = Oversold for LONG bullish)
            stoch_oversold = curr.get('stoch_k', 50) < 20
            
            # 2. Price Action Confirmation (Bullish Pin Bar atau Engulfing)
            # Check if we have bullish pin bar (wick ที่ bottom ยาว)
            body = (curr['o'] - curr['c']) if curr['c'] < curr['o'] else (curr['c'] - curr['o'])
            lower_wick = curr['o'].astype(float) if curr['c'] < curr['o'] else curr['c'].astype(float)
            lower_wick = lower_wick - curr['l']
            upper_wick = curr['h'] - (curr['c'] if curr['c'] > curr['o'] else curr['o'])
            
            pin_bar_bullish = (lower_wick > body * 2.0) and (upper_wick < body * 0.5)
            
            # Bullish Engulfing
            if len(df_full) > 1:
                prev = df_full.iloc[-2]
                engulfing_bullish = (
                    (curr['o'] < prev['c']) and 
                    (curr['c'] > prev['o']) and
                    (curr['c'] > prev['c'])
                )
            else:
                engulfing_bullish = False
            
            price_action_ok = pin_bar_bullish or engulfing_bullish
            
            # 3. Support/Resistance Check (ราคา ต้องอยู่เหนือ Support)
            support = float(curr.get('support', 0))
            resistance = float(curr.get('resistance', 0))
            price_above_support = curr['c'] > support * 1.005 if support > 0 else True
            price_below_resistance = curr['c'] < resistance * 0.995 if resistance > 0 else True
            
            # 4. Trend alignment (EMA alignment)
            ema_aligned = curr['ema20'] > curr['ema50'] > curr['ema200']
            
            # Skip if no good setup
            if not (price_above_support and price_below_resistance and ema_aligned):
                print(f"{Fore.YELLOW}Skip {sym}: Trend/Price not aligned for LONG{Style.RESET_ALL}")
                continue
            
            sl = best_price - (best_atr * ATR_SL_MULTIPLIER)
            tp = best_price + (best_atr * ATR_TP_MULTIPLIER)
            
            # Adjust TP to Resistance level
            if best_resistance > 0 and tp > best_resistance:
                tp = best_resistance * 0.98
            
            # ===== Risk:Reward Check (ต้อง >= 1:2) =====
            rr_ratio = calculate_rr_ratio(best_price, sl, tp, 'LONG')
            if rr_ratio < 2.0:
                print(f"{Fore.YELLOW}Skip {sym}: RR {rr_ratio:.2f}:1 < 2:1 threshold{Style.RESET_ALL}")
                continue
            
            # ===== Multi-Timeframe Confirmation =====
            htf_bullish = await check_htf_bullish_alignment(client, sym)
            if not htf_bullish:
                print(f"{Fore.YELLOW}Skip {sym}: HTF not bullish aligned{Style.RESET_ALL}")
                continue
            
            # คำนวณ qty จาก risk $0.5
            risk_amount = 0.5
            stop_distance = best_atr * ATR_SL_MULTIPLIER
            if stop_distance > 0:
                position_value = risk_amount / (stop_distance / best_price)
                qty = position_value / best_price
            else:
                qty = 0.001  # fallback
            
            # ปัดตาม step size
            step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
            qty = math.floor(qty / step_size) * step_size
            if qty < step_size * 10: qty = step_size * 10  # ขั้นต่ำนิดนึง
            
            qty_precision = sym_info.get(sym, (4, 2))[1]
            qty_str = f"{qty:.{qty_precision}f}"
            
            # ===== Elliott Wave + Fibonacci Analysis =====
            fib_elliot = get_fib_elliot_signal(df_full, best_price)
            fib_levels = calculate_fibonacci_levels(best_support * 1.05, best_resistance * 0.95) if best_support > 0 else {}
            
            try:
                # เข้า Market LONG ทันที
                await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)
                order = await client.futures_create_order(
                    symbol=sym,
                    side=SIDE_BUY,
                    type='MARKET',
                    quantity=qty
                )
                
                # ตั้ง SL/TP อัตโนมัติ
                tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                sl_price = round_to_tick(sl, tick_size)
                tp_price = round_to_tick(tp, tick_size)
                p_prec = sym_info.get(sym, (4, 2))[0]
                
                await client.futures_algo_new_order(
                    symbol=sym,
                    side=SIDE_SELL,
                    type='STOP_MARKET',
                    stopPrice=f"{sl_price:.{p_prec}f}",
                    closePosition=True,
                    timeInForce='GTC',
                    workingType='MARK_PRICE'
                )
                await client.futures_algo_new_order(
                    symbol=sym,
                    side=SIDE_SELL,
                    type='TAKE_PROFIT_MARKET',
                    stopPrice=f"{tp_price:.{p_prec}f}",
                    closePosition=True,
                    timeInForce='GTC',
                    workingType='MARK_PRICE'
                )
                
                report = (
                    f"🚀 *AUTO ENTERED LONG (Enhanced Confirmation)*\n"
                    f"*Symbol:* {sym.replace('USDT','')}\n"
                    f"*Price:* {best_price:.4f}\n"
                    f"*Risk:* $0.5 | *Qty:* {qty_str}\n"
                    f"*SL:* {sl_price:.4f} | *TP:* {tp_price:.4f}\n"
                    f"\n*Confirmations:* ✅\n"
                    f"  • Stoch: {curr.get('stoch_k', 50):.1f} (<20)\n"
                    f"  • Price Action: {'✅' if price_action_ok else '❌'}\n"
                    f"  • EMA Aligned: ✅ (20>50>200)\n"
                    f"  • HTF Align: ✅ (4H bullish)\n"
                    f"  • RR Ratio: {rr_ratio:.2f}:1\n"
                    f"  • Support: {best_support:.4f}\n"
                    f"  • Resistance: {best_resistance:.4f}\n"
                    f"*Elliott Wave:* {fib_elliot['wave_pattern']} ({fib_elliot['wave_direction']}) [{fib_elliot['wave_confidence']:.0%}]\n"
                    f"*Fib Signal:* {fib_elliot['signal']} @ {fib_elliot['fib_level']} [{fib_elliot['confidence']:.0%}]\n"
                    f"*Vol Spike:* {max_ratio:.2f}x in {best_tf}"
                )
                await send_telegram_report(report)
                print(f"{Fore.GREEN}{Style.BRIGHT}{report}{Style.RESET_ALL}")
                
            except Exception as e:
                await send_telegram_report(f"❌ Auto enter failed {sym}: {e}")
                print(f"{Fore.RED}Auto enter error {sym}: {e}")
    
    return results
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
#                  TELEGRAM COMMAND LISTENER (รวมทุกคำสั่งล่าสุด - แก้ Indentation แล้ว)
# ==========================================================================
async def check_telegram_updates(client, cmd_q, price_map):
    global update_offset, running, bal, active, btc_p, pending_orders_detail
    try:
        updates = await telegram_bot.get_updates(offset=update_offset, timeout=5)
        for update in updates:
            if update_offset is None or update.update_id >= update_offset:
                update_offset = update.update_id + 1

            if not update.message or not update.message.text:
                continue

            text = update.message.text.strip().lower()
            chat_id = update.message.chat_id

            # ตรวจสอบสิทธิ์การเข้าถึง
            if TELEGRAM_CHAT_ID and str(chat_id) != TELEGRAM_CHAT_ID:
                await telegram_bot.send_message(chat_id=chat_id, text="❌ ไม่ได้รับอนุญาต")
                continue

            print(f"{Fore.MAGENTA}Telegram command: {text} from {chat_id}")

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
                    "💰 พิมพ์ชื่อเหรียญ เช่น `BTC`, `ETH`, `SOL` → วิเคราะห์แนวโน้ม 1D\n\n"
                    "━━━━━━━ 🤖 AUTO ENTRY & AI ━━━━━━━\n"
                    "🔄 `/spike on/off` → เปิด/ปิด Auto LONG (Volume Spike Detected)\n"
                    "   └ Auto-enter when volume > 2.5x + 6 confirmations\n"
                    "🔄 `/shortsig on/off` → เปิด/ปิด Auto SHORT (Strong Signal)\n"
                    "   └ Auto-enter when ≥ 6 bearish conditions met\n"
                    "📡 `/autostatus` → สถานะ Auto Entry + ตั้งค่าปัจจุบัน\n"
                    "🧠 `/aistats` → AI Model Training Statistics + Accuracy + Confidence\n"
                    "   └ ดูการเรียนรู้ของ AI จากการเทรด\n\n"
                    "━━━━━━━━━ 🛑 SYSTEM CONTROL ━━━━━━━━━\n"
                    "🚪 `/q` หรือ `/quit` → หยุดบอทอย่างปลอดภัย\n"
                    "   └ ปิด WebSocket ทั้งหมด + ออกจาก program\n"
                    "   └ Positions จะเหลือไว้ run ต่อ (ไม่ปิด)\n\n"
                    "_⚡ TITAN PRO v33.0 - AI-Powered Advanced Trading Bot_\n"
                    "_LFG!_ 🚀"
                )
                await send_telegram_report(help_text, chat_id)

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

            # ===================== /aistats =====================
            elif text == '/aistats':
                ai_stats = brain.get_ai_stats()
                ai_text = (
                    f"🧠 **AI Model Training Stats**\n\n"
                    f"📊 **Data**:\n"
                    f"   └ Total Trades Learned: `{ai_stats['total_trades']}`\n"
                    f"   └ Epochs Trained: `{ai_stats['model_epochs_trained']}`\n\n"
                    f"🎯 **Accuracy**:\n"
                    f"   └ Current: `{ai_stats['last_accuracy']:.2f}%`\n"
                    f"   └ Average: `{ai_stats['avg_accuracy']:.2f}%`\n\n"
                    f"📉 **Loss**:\n"
                    f"   └ Best Loss: `{ai_stats['best_loss']:.6f}`\n"
                    f"   └ Latest Loss: `{ai_stats['last_loss']:.6f}`\n\n"
                    f"💡 **Status**:\n"
                    f"   └ Model Ready: {'✅ Yes' if ai_stats['total_trades'] >= 10 else '⏳ Training (need 10+ trades)'}\n"
                    f"   └ Confidence: `{brain.get_ai_confidence([0.5]*10):.1f}%` (avg)\n\n"
                    f"_บอท AI ยิ่งเล่นมากเท่าไร ยิ่งฉลาด_ 🚀"
                )
                await send_telegram_report(ai_text, chat_id)

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
            elif text == '/limits':
                report = get_pending_limits_report(pending_orders_detail, price_map)
                await send_telegram_report(report, chat_id)

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
                    report_text = (
                        f"📊 **{sym_input}/USDT - วิเคราะห์อัจฉริยะ**\n"
                        f"`{datetime.now().strftime('%d/%m %H:%M')}` | ราคา: `{current_price:,.2f}`\n\n"
                        
                        f"**📈 Trend Analysis**\n"
                        f"4H: {trend_4h}\n"
                        f"1H: {trend_1h}\n\n"
                        
                        f"**📊 Momentum**\n"
                        f"RSI(4H): {rsi_4h:.1f} {rsi_status_4h}\n"
                        f"Stoch(4H): {stoch_4h:.1f} | Stoch(1H): {stoch_1h:.1f}\n"
                        f"MACD: {'🟢 Bullish' if macd_bullish else '🔴 Bearish'}\n\n"
                        
                        f"**🎯 Support & Resistance**\n"
                        f"Support: `{support:,.2f}` | Resistance: `{resistance:,.2f}`\n"
                        f"Position: {price_pos}\n\n"
                        
                        f"**🎪 Fibonacci Levels** (38.2%/61.8%: `{fib_levels['38.2%']:,.2f}` / `{fib_levels['61.8%']:,.2f}`)\n\n"
                        
                        f"**💡 สรุป**: "
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
                    sym = sym_input + "USDT"
                    await cmd_q.put(f'close:{sym}')
                    await send_telegram_report(f"🚪 กำลังปิด {sym_input} Position...", chat_id)
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
                sym_input = text.upper()
                sym = sym_input + "USDT"
                if sym not in price_map:
                    await send_telegram_report("❓ ไม่พบเหรียญนี้หรือยังไม่มีข้อมูล", chat_id)
                    continue

                current_price = price_map[sym]

                try:
                    k = await client.futures_klines(symbol=sym, interval="1d", limit=500)
                    if not k or len(k) < 50:
                        await send_telegram_report(
                            f"💰 **{sym_input}**\nราคา: {current_price:,.1f} USDT\n⚠️ ข้อมูลไม่เพียงพอสำหรับการวิเคราะห์ 1D",
                            chat_id
                        )
                        continue

                    df = calculate_indicators(k)
                    if df.empty:
                        raise Exception("Calculate indicators failed")

                    curr = df.iloc[-1]
                    prev = df.iloc[-2] if len(df) > 1 else curr

                    change_pct = (current_price - float(prev['c'])) / float(prev['c']) * 100 if prev['c'] > 0 else 0
                    rsi_val = curr['rsi']
                    adx_val = curr['adx']
                    macd_val = curr['macd']
                    signal_val = curr['signal']
                    vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1

                    report_text = (
                        f"📊 วิเคราะห์ {sym_input}/USDT (กรอบวัน – 1D)\n\n"
                        f"💰 ราคาตอนนี้: `{current_price:,.8f}` USDT\n"
                        f"📈📉 วันนี้: `{change_pct:+.2f}%`\n"
                        f"→ {'ราคาแทบไม่ขยับ ถือว่านิ่ง/พักตัว' if abs(change_pct) < 1 else 'ราคาขยับขึ้นชัด' if change_pct > 0 else 'ราคากดลงแรง'}\n\n"

                        f"🔍 ตัวชี้วัดทางเทคนิค\n\n"
                        f"🔹 RSI (14): `{rsi_val:.1f}` → {'🟢 Oversold' if rsi_val < 30 else '🔴 Overbought' if rsi_val > 70 else '🟡 ปกติ'}\n"
                        f"🔹 ADX (14): `{adx_val:.1f}` → {'🟢 เทรนด์แข็งแรง' if adx_val > 30 else '🟡 เทรนด์อ่อน/ไซด์เวย์'}\n"
                        f"🔹 MACD: {'🟢 Bullish' if macd_val > signal_val else '🔴 Bearish'}\n"
                        f"🔹 Volume: {'🔥 สูงมาก' if vol_ratio > 2.0 else '🟢 สูง' if vol_ratio > 1.5 else 'ปกติ'}\n\n"

                        f"⚠️ โครงสร้างแนวโน้ม\n"
                        f"EMA Alignment: {'🟢 ขาขึ้นแข็งแรง' if curr['ema20'] > curr['ema50'] > curr['ema200'] else '🔴 ขาลงแข็งแรง' if curr['ema20'] < curr['ema50'] < curr['ema200'] else '🟡 ไซด์เวย์'}\n\n"

                        f"🧠 **สรุปสั้น**: {'🟢 เริ่มมีโอกาสกลับตัวขึ้น' if curr['ema20'] > curr['ema50'] else '🔴 โครงสร้างยังลงอยู่'}\n"
                        f"{'🟢 โมเมนตัมบวก' if macd_val > signal_val else '🔴 โมเมนตัมลบ'}\n"
                        f"Volume {'มาแล้ว → น่าเชื่อถือ' if vol_ratio > 1.5 else 'ยังเบา → รอ confirmation'}\n\n"

                        f"_{datetime.now().strftime('%d/%m/%Y %H:%M:%S')}_"
                    )

                    await send_telegram_report(report_text, chat_id)

                except Exception as e:
                    print(f"{Fore.RED}Error analyzing {sym} (1D): {e}")
                    await send_telegram_report(
                        f"💰 **{sym_input}**\nราคา: {current_price:,.1f} USDT\n⚠️ ไม่สามารถวิเคราะห์ได้ในขณะนี้",
                        chat_id
                    )

    except Exception as e:
        print(f"{Fore.RED}Telegram polling error: {e}")

# ==========================================================================
#                  PENDING LIMITS REPORT
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
        lines.append(f"  ห่าง: {diff:+.4f} ({pct:+.2f}%) | จำนวน: {o['qty']:.4f} | อายุ: {age:.1f}ชั่วโมง")
    return "\n".join(lines)

# ==========================================================================
#                  ANALYZE TREND
# ==========================================================================
async def analyze_trend(client, symbol):
    try:
        k = await client.futures_klines(symbol=symbol, interval="4h", limit=200)
        if not k: return "ไม่พบข้อมูลสำหรับเหรียญนี้"
        
        df = calculate_indicators(k)
        if df.empty: return "ไม่สามารถคำนวณ indicators ได้"
        
        curr = df.iloc[-1]
        
        trend_summary = f"**วิเคราะห์แนวโน้ม {symbol.replace('USDT','')} (4h)**\n"
        trend_summary += f"ราคาปัจจุบัน: {float(curr['c']):,.4f} USDT\n"
        trend_summary += f"ADX: {curr['adx']:.1f} → {'แข็งแรง' if curr['adx'] > 30 else 'อ่อน'}\n"
        trend_summary += f"RSI: {curr['rsi']:.1f} → {'Overbought' if curr['rsi'] > 70 else 'Oversold' if curr['rsi'] < 30 else 'ปกติ'}\n"
        trend_summary += f"MACD {'Bullish 📈' if curr['macd'] > curr['signal'] else 'Bearish 📉'}\n"
        trend_summary += f"EMA: {'ขาขึ้น 🟢' if curr['ema20'] > curr['ema50'] > curr['ema200'] else 'ขาลง 🔴' if curr['ema20'] < curr['ema50'] < curr['ema200'] else 'ไซด์เวย์ 🟡'}\n"
        trend_summary += f"BB: {'ทะลุบน (Breakout)' if curr['c'] > curr['bb_upper'] else 'ทะลุล่าง (Oversold)' if curr['c'] < curr['bb_lower'] else 'กลาง (Range)'}\n"
        trend_summary += f"\n**สรุป**: {'🟢 แนวโน้มขาขึ้นแข็งแรง' if curr['adx'] > 30 and curr['macd'] > curr['signal'] and curr['ema20'] > curr['ema50'] else '🔴 แนวโน้มขาลงแข็งแรง' if curr['adx'] > 30 and curr['macd'] < curr['signal'] and curr['ema20'] < curr['ema50'] else '🟡 ไซด์เวย์ / อ่อน'}"
        
        return trend_summary
    except Exception as e:
        return f"เกิดข้อผิดพลาด: {e}"

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
async def main():
    global bal, active, btc_p, pending_orders_detail, running
    global sym_info, sym_filters, top_50_symbols, last_volume_update
    global sl_tp_advice_notified, signal_features
    global last_spike_check, last_short_signal_check
    global active_detailed
    global last_sl_tp_check   # เพิ่มบรรทัดนี้เพื่อให้แก้ไขตัวแปร global ได้

    client = None
    reconnect_attempts = 0
    MAX_RECONNECT = 5

    while running and reconnect_attempts < MAX_RECONNECT:
        try:
            client = await AsyncClient.create(API_KEY, API_SECRET, testnet=USE_TESTNET)
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
                    active_symbols = set()

                    active = []
                    for p in pos_data:
                        amt = float(p['positionAmt'])
                        if amt == 0:
                            continue

                        sym = p['symbol']
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
                            'side': 'LONG' if amt > 0 else 'SHORT',
                            'entry': entry,
                            'curr_price': curr_price,
                            'pnl': float(p['unRealizedProfit']),
                            'amt': amt,
                            'margin': abs(amt * entry / MAX_LEVERAGE),
                            'sl': sl,
                            'tp': tp
                        })

                    # อัพเดท max ROE ทุก loop
                    for pos in active:
                        sym = pos['symbol']
                        if sym in active_detailed:
                            roe = (pos['pnl'] / pos['margin'] * 100) if pos['margin'] > 0 else 0.0
                            active_detailed[sym]['max_roe'] = max(active_detailed[sym]['max_roe'], roe)

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
                                    reduceOnly=True
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
                                    reduceOnly=True
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
                            await send_telegram_report(report)
                            sl_tp_advice_notified.add(sym)

                        except Exception as e:
                            print(f"{Fore.RED}Error processing new position {sym}: {e}")

                    # จัดการ position ที่ปิดไป → บันทึก trade ลง CSV + แจ้งเตือน
                    # ==========================================================================
                    # จัดการ position ที่ปิดไป
                    # ==========================================================================
                    for sym in closed_positions:
                        pos_info = active_detailed.pop(sym, None)
                        if not pos_info:
                            print(f"{Fore.YELLOW}Closed {sym} but no detailed info found")
                            continue

                        try:
                            close_trades = []
                            for retry in range(4):
                                trades = await client.futures_account_trades(symbol=sym, limit=50)
                                close_trades = [t for t in trades if float(t.get('realizedPnl', 0)) != 0]
                                if close_trades:
                                    break
                                await asyncio.sleep(2.0)

                            if not close_trades:
                                print(f"{Fore.YELLOW}ไม่พบ realized PnL สำหรับ {sym} → ข้ามบันทึก")
                                continue

                            last_trade = max(close_trades, key=lambda t: int(t['time']))
                            exit_price = float(last_trade['price'])
                            pnl = float(last_trade['realizedPnl'])
                            is_win = pnl > 0

                            exit_time = datetime.fromtimestamp(int(last_trade['time']) / 1000)
                            duration_hours = (exit_time - pos_info['entry_time']).total_seconds() / 3600

                            margin = abs(pos_info['quantity'] * pos_info['entry_price'] / pos_info['leverage'])
                            pnl_percent = (pnl / margin * 100) if margin > 1e-8 else 0.0

                            exit_reason = "Manual / Other"
                            orig_type = last_trade.get('origType', '')
                            if 'STOP_MARKET' in orig_type:
                                exit_reason = "Hit SL"
                            elif 'TAKE_PROFIT_MARKET' in orig_type:
                                exit_reason = "Hit TP"
                            elif pnl < -margin * 0.7:
                                exit_reason = "Liquidation / Big Loss"

                            # ถ้าเป็นการปิดด้วยมือ หรือ closeall → ใส่ cooldown
                            if exit_reason in ["Manual / Other", "Manual Close (closeall)"]:
                                manual_closed_cooldown[sym] = datetime.now().timestamp()
                                print(f"{Fore.MAGENTA}Manual/closeall detected → cooldown {sym} {COOLDOWN_AFTER_MANUAL_MINUTES} นาที{Style.RESET_ALL}")

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
                                'max_roe_percent': pos_info.get('max_roe', 0.0),
                                'features': pos_info.get('features', [])
                            }

                            log_trade_to_csv(trade_record)
                            print(f"{Fore.GREEN}บันทึก trade สำเร็จ: {sym} PNL {pnl:+.2f}{Style.RESET_ALL}")

                            wr, wins, total = get_current_winrate()
                            win_emoji = "🟢 WIN!" if is_win else "🔴 LOSS"
                            pnl_emoji = "🟢" if is_win else "🔴"

                            report = (
                                f"{win_emoji} **Position Closed**\n"
                                f"เหรียญ: `{sym.replace('USDT','')}` {pos_info['side']}\n"
                                f"Entry → Exit: `{pos_info['entry_price']:.6f}` → `{exit_price:.6f}`\n"
                                f"PNL: {pnl_emoji} `{pnl:+.2f}` USDT (`{pnl_percent:+.2f}%`)\n"
                                f"เหตุผล: **{exit_reason}**\n"
                                f"ระยะเวลา: `{duration_hours:.1f}` ชม\n"
                                f"Max ROE: `{pos_info.get('max_roe', 0.0):+.2f}%`\n"
                                f"สถิติรวม: {wins}/{total} | Winrate {wr:.1f}%"
                            )
                            await send_telegram_report(report)

                        except Exception as e:
                            print(f"{Fore.RED}Error logging closed position {sym}: {e}")
                            await send_telegram_report(f"⚠️ Error บันทึก trade {sym}: {str(e)}")

                    prev_active_symbols = current_active_symbols.copy()

                    # ==========================================================================
                    #               ★★★ การตรวจสอบและตั้ง SL/TP อัตโนมัติ ★★★
                    # ==========================================================================
                    current_time = datetime.now().timestamp()

                    # 1. เรียกทุก 45 วินาที (ป้องกัน order หาย/ถูกลบโดย manual)
                    if current_time - last_sl_tp_check >= 45:
                        print(f"{Fore.CYAN}ตรวจสอบ/ซ่อม SL&TP ทั้งหมด (ทุก 45 วินาที)...{Style.RESET_ALL}")
                        await ensure_sl_tp_for_all_positions(client)
                        last_sl_tp_check = current_time

                    # 2. ถ้าเจอ position ใหม่ → เรียกทันที (ความปลอดภัยสูงสุด)
                    if new_positions:
                        print(f"{Fore.CYAN}พบ position ใหม่ {len(new_positions)} ตัว → ตรวจ/ตั้ง SL&TP ทันที{Style.RESET_ALL}")
                        await ensure_sl_tp_for_all_positions(client)
                        last_sl_tp_check = current_time

                    # อัปเดต Trailing Stop ทุกๆ รอบ loop
                    await update_trailing_stops(client, active)

                    # ยกเลิก Limit Order เก่า
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

                    # Auto detect Strong Short
                    if auto_short_signal_enabled and datetime.now() - last_short_signal_check > SHORT_SIGNAL_CHECK_INTERVAL:
                        await detect_strong_short_signals(client, top_50_symbols, price_map, active_symbols)
                        last_short_signal_check = datetime.now()

                    # ตรวจจับคำสั่งจาก Telegram
                    if telegram_bot:
                        await check_telegram_updates(client, cmd_q, price_map)

                    # ประมวลผลคำสั่งจากคิว
                    while not cmd_q.empty() and running:
                        cmd = await cmd_q.get()
                        if cmd in ['qq', 'quit']:
                            running = False
                            await send_telegram_report("🛑 บอทหยุดทำงานเรียบร้อย")
                            print(f"{Fore.YELLOW}Shutdown command received.")
                        elif cmd.startswith('close:'):
                            # ===== ปิด Position เดี่ยว =====
                            target_sym = cmd.replace('close:', '')
                            target_pos = next((p for p in active if p['symbol'] == target_sym), None)
                            
                            if target_pos:
                                sym = target_pos['symbol']
                                side = SIDE_SELL if target_pos['side'] == 'LONG' else SIDE_BUY
                                qty = abs(target_pos['amt'])
                                
                                try:
                                    await client.futures_create_order(
                                        symbol=sym,
                                        side=side,
                                        type='MARKET',
                                        quantity=qty,
                                        reduceOnly=True
                                    )
                                    print(f"ปิด position สำเร็จ: {sym} {target_pos['side']}")
                                    
                                    # รอ Binance sync แล้วดึง trade ล่าสุด
                                    await asyncio.sleep(1.5)
                                    
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
                                            
                                            exit_reason = "Manual Close"
                                            
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
                                            
                                            wr, wins, total = get_current_winrate()
                                            win_emoji = "🟢 WIN!" if is_win else "🔴 LOSS"
                                            pnl_emoji = "🟢" if is_win else "🔴"
                                            report = (
                                                f"{win_emoji} **Position Closed**\\n"
                                                f"เหรียญ: `{sym.replace('USDT','')}` {pos_info['side']}\\n"
                                                f"Entry → Exit: `{pos_info['entry_price']:.6f}` → `{exit_price:.6f}`\\n"
                                                f"PNL: {pnl_emoji} `{pnl:+.2f}` USDT (`{pnl_percent:+.2f}%`)\\n"
                                                f"ระยะเวลา: `{duration_hours:.1f}` ชม\\n"
                                                f"Max ROE: `{pos_info['max_roe']:+.2f}%`\\n"
                                                f"สถิติรวม: {wins}/{total} | Winrate {wr:.1f}%"
                                            )
                                            await send_telegram_report(report)
                                            
                                            # ลบออกจาก active
                                            active[:] = [p for p in active if p['symbol'] != sym]
                                            active_detailed.pop(sym, None)
                                            manual_closed_cooldown[sym] = datetime.now()
                                            print(f"{Fore.MAGENTA}Manual close detected → cooldown {sym} {COOLDOWN_AFTER_MANUAL_MINUTES} นาที{Style.RESET_ALL}")
                                except Exception as e:
                                    print(f"{Fore.RED}Error closing {target_sym}: {e}")
                                    await send_telegram_report(f"❌ ไม่สามารถปิด {target_sym}: {str(e)}")
                            else:
                                await send_telegram_report(f"⚠️ ไม่พบ Position {target_sym}")
                        
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
                                        r['rsi']/100,
                                        r['adx']/100,
                                        (r.get('macd', 0) - r.get('signal', 0)) / r['atr'] if r['atr'] > 0 else 0,
                                        (current_p - r.get('ema200', current_p)) / r.get('ema200', current_p) if r.get('ema200', 0) != 0 else 0,
                                        r.get('vol_ratio', 1),
                                        r['score']/8.0,
                                        1 if r['side'] == 'LONG' else 0
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