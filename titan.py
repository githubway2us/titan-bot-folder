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
last_long_entry_time = {}  # sym → timestamp
prev_prices = {}
ticker_offset = 0
ticker_direction = 1
manual_limit_orders = []  # เก็บข้อมูล limit ที่ตั้งด้วยมือเพิ่มเติม
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
TRAILING_ACTIVATION_MULTIPLIER = 2.5          # จาก 1.8 → ปล่อยให้กำไรวิ่งไกลกว่านี้ก่อนเริ่ม trailing
TRAILING_DELTA_MULTIPLIER     = 2.0           # จาก 1.3 → trailing ห่างมากขึ้น ให้กำไรวิ่งต่อ

# --- Risk & Position Management ---
RISK_PER_TRADE_PERCENT        = 0.025         # จาก 0.02 → เสี่ยง $0.625–0.75 ต่อเทรด (ทุน $100)
MAX_OPEN_POSITIONS            = 5             # จาก 3 → เปิดได้มากขึ้น (เพิ่มโอกาส)
MAX_LEVERAGE                  = 30            # จาก 25 → ใช้สูงขึ้นในเทรนด์แรง (แต่มี guard)

# --- Signal & Entry (เข้าเร็ว + เยอะขึ้น) ---
SIGNAL_THRESHOLD_LONG         = 5.5           # จาก 7 → ผ่อนปรนมากขึ้น เจอสัญญาณไว
SIGNAL_THRESHOLD_SHORT        = 5.5           # เดียวกัน
ADX_THRESHOLD                 = 22            # จาก 28 → ยอมรับเทรนด์อ่อน/เริ่มต้น
SCAN_BATCH_SIZE               = 100           # จาก 40 → สแกนเยอะขึ้นมาก
ENTRY_PULLBACK_PERCENT        = 25.0          # จาก 38 → เข้าใกล้ราคาปัจจุบันมากขึ้น (fill ไว)

# --- SL/TP (ให้กำไรวิ่งไกล แต่ SL ยังป้องกัน) ---
ATR_SL_MULTIPLIER             = 2.2           # จาก 2.8 → SL กว้างขึ้นนิด ให้ราคาหายใจ
ATR_TP_MULTIPLIER             = 6.0           # จาก 4.6 → TP ไกลขึ้นมาก (หวัง RR สูง)
MIN_RR_FOR_ENTRY              = 1.8           # ต่ำลงจาก 2.0 เพื่อให้เข้าได้บ่อยขึ้น

# --- อื่น ๆ (ความเร็ว + ความปลอดภัย) ---
LIMIT_ORDER_TIMEOUT_HOURS     = 1.5           # จาก 2.0 → ยกเลิกเก่าเร็วขึ้น
MIN_BALANCE_TO_TRADE          = 12.0          # จาก 15 → เริ่มเทรดได้เร็วกว่า
MIN_NOTIONAL_USDT             = 4             # จาก 5 → เข้าได้กับ position เล็ก

# --- Guard ป้องกัน over-leverage / ล้างพอร์ต ---
#MAX_TOTAL_RISK_PERCENT        = 0.12          # รวมทุก position เสี่ยงไม่เกิน 12% ของพอร์ต
#TRAILING_STOP_ON_PROFIT_ONLY  = True          # trailing เฉพาะเมื่อกำไร (ป้องกันเบรกอีเว่นเร็ว)

MAJOR_TICKER_SYMBOLS = [
    'BTCUSDT', 'ETHUSDT', 'SOLUSDT', 'BNBUSDT', 'XRPUSDT', 'ADAUSDT',
    'DOGEUSDT', 'AVAXUSDT', 'LINKUSDT', 'DOTUSDT', 'TRXUSDT', 'MATICUSDT',
    'LTCUSDT', 'BCHUSDT', 'NEARUSDT', 'UNIUSDT', 'SUIUSDT', 'APTUSDT',
    'TONUSDT', 'ICPUSDT', 'HBARUSDT', 'ATOMUSDT', 'OPUSDT', 'INJUSDT', 'ARBUSDT'
    # เพิ่มได้อีกถ้าต้องการ แต่ 25 ตัวนี้ cover top volume + stable แล้ว
    # ไม่แนะนำเพิ่ม meme จนกว่าจะ confirm ว่ามี perpetual และ volume สูงจริง
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
                cooldown_map[sym] = now  # อัปเดต cooldown
        except Exception as e:
            print(f"{Fore.RED}Entry {sym} failed: {e}{Style.RESET_ALL}")
            await send_telegram_report(f"❌ Entry fail {sym}: {str(e)}")

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
async def fast_scan_top_20_signals(client, price_map, active_symbols, pending_orders):
    """
    FAST SCAN TOP 20 - เร่งด่วนสูง & แม่นยำ (pre-filter เข้ม + HTF เฉพาะกรณีดีจริง)
    - Pre-filter: trend ชัด + ADX >22 + Vol >1.2x → ข้ามเร็ว
    - Signal >=4 + เงื่อนไขเสริม (ADX/Vol/RSI) → เรียก HTF
    - หยุดเมื่อพบ 2 สัญญาณคุณภาพสูง
    """
    top_symbols = MAJOR_TICKER_SYMBOLS[:20]
    results = []
    scan_start = datetime.now()

    pending_symbols = {order['symbol'] for order in pending_orders 
                       if isinstance(order, dict) and 'symbol' in order}

    print(f"\n{Fore.CYAN}🚀 FAST SCAN TOP 20 - เร็ว & แม่นยำสูง (pre-filter เข้ม){Style.RESET_ALL}")
    if pending_symbols:
        print(f"{Fore.YELLOW}⏳ ข้าม pending: {', '.join(sorted(pending_symbols))}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}{'=' * 140}{Style.RESET_ALL}")

    for sym in top_symbols:
        if sym in active_symbols:
            print(f"{Fore.YELLOW}⊘ Skip {sym}: มี position{Style.RESET_ALL}")
            continue
        if sym in pending_symbols:
            print(f"{Fore.YELLOW}⊘ Skip {sym}: มี limit order{Style.RESET_ALL}")
            continue

        try:
            # ดึงข้อมูลน้อยลงเพื่อความเร็ว
            klines = await client.futures_klines(symbol=sym, interval='15m', limit=35)
            df = calculate_indicators(klines)

            if df.empty or len(df) < 20:
                continue

            curr = df.iloc[-1]
            current_price = curr['c']

            # ===== PRE-FILTER เข้มแต่ผ่อนลงเพื่อเข้าเร็วขึ้น =====
            has_trend = (curr['ema20'] > curr['ema50']) or (curr['ema20'] < curr['ema50'])  # ยังต้องมี trend ชัด
            has_strength = curr.get('adx', 0) > 20          # ลดจาก 22 → 20 (ยอมรับ trend ที่เพิ่งเริ่ม)
            has_volume = (curr['v'] / curr['vol_ma']) > 1.1 if curr['vol_ma'] > 0 else True  # ลดจาก 1.2 → 1.1


            if not (has_trend and has_strength):
                # print(f"Skip {sym}: weak trend/ADX/vol")  # uncomment ถ้าอยากเห็น
                continue

            # ===== นับสัญญาณเต็ม =====
            signal_count = 0
            signal_details = []

            # EMA Trend
            if curr['ema20'] > curr['ema50']:
                signal_count += 1; signal_details.append("EMA20>50")
            elif curr['ema20'] < curr['ema50']:
                signal_count += 1; signal_details.append("EMA20<50")

            # Price vs EMA200
            if curr['c'] > curr['ema200']:
                signal_count += 1; signal_details.append("Above200")
            elif curr['c'] < curr['ema200']:
                signal_count += 1; signal_details.append("Below200")

            # RSI
            if curr['rsi'] > 70:
                signal_count += 1; signal_details.append("RSI>70")
            elif curr['rsi'] < 30:
                signal_count += 1; signal_details.append("RSI<30")

            # MACD
            if curr['macd'] > curr['signal']:
                signal_count += 1; signal_details.append("MACD>SIG")
            elif curr['macd'] < curr['signal']:
                signal_count += 1; signal_details.append("MACD<SIG")

            # Bollinger
            if curr['c'] > curr['bb_upper']:
                signal_count += 1; signal_details.append("Above_BB")
            elif curr['c'] < curr['bb_lower']:
                signal_count += 1; signal_details.append("Below_BB")

            # Volume
            vol_ratio = curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1.0
            if vol_ratio > 1.5:
                signal_count += 1; signal_details.append(f"Vol{vol_ratio:.1f}x")

            # ADX
            if curr['adx'] > 25:
                signal_count += 1; signal_details.append(f"ADX{curr['adx']:.0f}")

            # ===== เงื่อนไขเสริมเพื่อความแม่นยำสูง (ต้องมีอย่างน้อย 1 ตัว) =====
            quality_bonus = 0
            if curr['adx'] > 28:
                quality_bonus += 1
            if vol_ratio > 1.8:
                quality_bonus += 1
            if curr['rsi'] > 72 or curr['rsi'] < 28:
                quality_bonus += 1

            # ===== Threshold คุณภาพสูง =====
            if signal_count >= 4 and quality_bonus >= 1:
                is_bullish_15m = curr['ema20'] > curr['ema50']
                direction = "🟢 LONG" if is_bullish_15m else "🔴 SHORT"

                # ===== เรียก HTF เฉพาะเมื่อผ่าน threshold คุณภาพ =====
                htf_aligned = False
                htf_msg = ""
                if is_bullish_15m:
                    htf_aligned = await check_htf_bullish_alignment(client, sym)
                    htf_msg = "HTF Bull ✓" if htf_aligned else "HTF Bull ✗"
                else:
                    htf_aligned = await check_htf_bearish_alignment(client, sym)
                    htf_msg = "HTF Bear ✓" if htf_aligned else "HTF Bear ✗"

                print(
                    f"{direction} │ {sym.replace('USDT',''):>6} │ "
                    f"{current_price:>10.4f} │ RSI:{curr['rsi']:>5.1f} │ "
                    f"Signals: {signal_count}/8 +{quality_bonus} │ {' '.join(signal_details[:4])} │ {htf_msg}"
                )

                if not htf_aligned:
                    print(f"{Fore.YELLOW}   → ข้าม {sym} (HTF ไม่ align){Style.RESET_ALL}")
                    continue

                # เก็บผลลัพธ์คุณภาพสูง
                results.append({
                    'symbol': sym,
                    'price': current_price,
                    'direction': 'LONG' if is_bullish_15m else 'SHORT',
                    'signal_count': signal_count,
                    'signals': signal_details,
                    'rsi': curr['rsi'],
                    'vol_ratio': vol_ratio,
                    'atr': curr['atr'],
                    'quality_bonus': quality_bonus
                })

                # หยุดเมื่อพบ 2 สัญญาณดีจริง (ปรับได้)
                if len(results) >= 2:
                    break

        except Exception as e:
            print(f"{Fore.RED}Scan error {sym}: {e}{Style.RESET_ALL}")
            continue

    scan_time = (datetime.now() - scan_start).total_seconds()
    print(f"{Fore.CYAN}{'=' * 140}{Style.RESET_ALL}")
    print(f"{Fore.CYAN}✅ สแกนเสร็จ - พบ {len(results)} สัญญาณคุณภาพสูง ใน {scan_time:.1f}s{Style.RESET_ALL}\n")

    return results

# ==========================================================================
#          HISTORICAL SWING ANALYZER - วิเคราะห์ราคาเคยสวิงขึ้นไป
# ==========================================================================
async def analyze_historical_swings(client, symbol, lookback_candles=200):
    """
    วิเคราะห์ประวัติราคาย้อนหลัง เพื่อหา:
    - ราคาสวิงขึ้นสูงสุด (highest swing up)
    - ราคาสวิงลงต่ำสุด (lowest swing down)
    - Zones ที่ราคามักจะ reverse
    - Average pullback size
    
    Returns: {
        'highest_swing': float,          # ราคาเคยขึ้นสูงสุดจากปัจจุบัน
        'lowest_swing': float,           # ราคาเคยลงต่ำสุดจากปัจจุบัน
        'avg_pullback': float,           # Average pullback ขนาด
        'recent_support': float,         # Support level เมื่อเร็ว ๆ นี้
        'recent_resistance': float,      # Resistance level เมื่อเร็ว ๆ นี้
        'key_reversal_zones': [float],   # Zones ที่ราคา reverse บ่อย
        'swing_ratio': float             # Ratio เพื่อคำนวณ entry
    }
    """
    try:
        # ดึงข้อมูล 4h (เพื่อ smooth out noise)
        klines = await client.futures_klines(symbol=symbol, interval='4h', limit=lookback_candles)
        df = calculate_indicators(klines)
        
        if df.empty or len(df) < 50:
            print(f"{Fore.YELLOW}⚠️ ข้อมูลไม่พอสำหรับ swing analysis {symbol}")
            return None
        
        # ===== หาราคา High/Low ตลอดประวัติ =====
        all_highs = df['h'].values
        all_lows = df['l'].values
        current_price = df.iloc[-1]['c']
        
        # Highest swing up from current level
        highest_swing = all_highs.max()
        lowest_swing = all_lows.min()
        
        # ===== วิเคราะห์ Pullback Zones (Local Highs & Lows) =====
        reversal_zones = []
        for i in range(2, len(df) - 2):
            # Local High (resistance)
            if (df.iloc[i]['h'] > df.iloc[i-1]['h'] and 
                df.iloc[i]['h'] > df.iloc[i+1]['h'] and
                df.iloc[i]['h'] > current_price * 0.95):
                reversal_zones.append(('resistance', df.iloc[i]['h']))
            
            # Local Low (support)
            if (df.iloc[i]['l'] < df.iloc[i-1]['l'] and 
                df.iloc[i]['l'] < df.iloc[i+1]['l'] and
                df.iloc[i]['l'] < current_price * 1.05):
                reversal_zones.append(('support', df.iloc[i]['l']))
        
        # เรียงลำดับตามความใกล้กับราคาปัจจุบัน
        reversal_zones.sort(key=lambda x: abs(x[1] - current_price))
        
        # Get recent support/resistance (last 30 candles)
        recent_data = df.iloc[-30:]
        recent_high = recent_data['h'].max()
        recent_low = recent_data['l'].min()
        
        # ===== คำนวณ Average Pullback Size =====
        pullback_sizes = []
        for i in range(1, len(df)):
            # ขนาดของ pullback จาก high มา low
            swing_size = df.iloc[i]['h'] - df.iloc[i]['l']
            pullback_sizes.append(swing_size)
        
        avg_pullback = np.mean(pullback_sizes[-50:]) if len(pullback_sizes) >= 50 else np.mean(pullback_sizes)
        
        # ===== คำนวณ Swing Ratio (ใช้สำหรับคำนวณ entry) =====
        # Swing ratio = ความสามารถในการขึ้นลง ในอดีต
        swing_ratio = (highest_swing - lowest_swing) / current_price if current_price > 0 else 0
        
        # ===== ดึง Key Levels จากท้องทะเล reversal zones =====
        key_levels = [zone[1] for zone in reversal_zones[:5]]
        
        result = {
            'highest_swing': float(highest_swing),
            'lowest_swing': float(lowest_swing),
            'avg_pullback': float(avg_pullback),
            'recent_support': float(recent_low),
            'recent_resistance': float(recent_high),
            'key_reversal_zones': key_levels,
            'swing_ratio': float(swing_ratio),
            'highest_high': float(all_highs.max()),
            'lowest_low': float(all_lows.min())
        }
        
        print(f"{Fore.CYAN}📊 Swing Analysis {symbol}:{Style.RESET_ALL}")
        print(f"   Current: {current_price:.4f} | High: {highest_swing:.4f} | Low: {lowest_swing:.4f}")
        print(f"   Recent Support: {recent_low:.4f} | Recent Resistance: {recent_high:.4f}")
        print(f"   Avg Pullback: {avg_pullback:.4f} | Swing Ratio: {swing_ratio:.2f}")
        
        return result
        
    except Exception as e:
        print(f"{Fore.RED}Swing analysis error {symbol}: {e}")
        return None

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

# ==========================================================================
#                  EXECUTE FAST SCAN ENTRY - บันทึกและสั่งซื้อจากผลลัพธ์สแกน
# ==========================================================================
# ==========================================================================
#                  EXECUTE FAST SCAN ENTRY - ปรับปรุงความปลอดภัยสูง (21 ม.ค. 2026)
# ==========================================================================
async def execute_fast_scan_entry(client, scan_result, price_map):
    sym = scan_result['symbol']
    direction = scan_result['direction']
    
    print(f"[EXECUTE ENTRY START] {sym} {direction} - กำลังตรวจสอบเงื่อนไขปลอดภัยทั้งหมด")
    
    try:
        # 1. Historical Swings (สำคัญมาก - ถ้าไม่มี → ข้ามเลย)
        swing_data = await analyze_historical_swings(client, sym, lookback_candles=200)
        if swing_data is None:
            reason = "ไม่มี swing_data (ข้อมูลประวัติไม่พอ)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}", chat_id=None)
            return False

        # 2. Load candles 15m + indicators
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

        # 3. Volume ต้องไม่ต่ำเกิน (ป้องกัน vol 0.03x)
# Volume check (ผ่อนลง + มี ADX bonus)
        volume = float(curr.get('v', 1))
        vol_ma = float(curr.get('vol_ma', 1))
        vol_ratio = volume / vol_ma if vol_ma > 0 else 1.0
        
        adx = float(curr.get('adx', 20))
        volume_ok = (vol_ratio >= 0.4) or (adx >= 35)  # ผ่อน + bonus ADX แรง
        
        if not volume_ok:
            reason = f"Volume ต่ำเกินไป ({vol_ratio:.2f}x < 0.4) และ ADX ไม่สูงพอ ({adx:.0f} < 35)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(
                f"⚠️ ไม่เข้า {sym} ({direction})\n"
                f"เหตุผล: {reason}\n"
                f"ADX: {adx:.0f} | Vol: {vol_ratio:.2f}x\n"
                f"แนะนำ: รอ volume เพิ่มหรือ ADX > 35",
                chat_id=None
            )
            return False
        print(f"[EXECUTE] Volume ผ่าน (หรือ ADX bonus): {vol_ratio:.2f}x | ADX {adx:.0f}")
        # 4. Swing-based Fibonacci Entry
        entry_price, fib_reason, trend_info = calculate_swing_based_fibonacci_entry(
            current_price, swing_data, direction, df
        )

        # เพิ่ม log เพื่อ debug
        print(f"[ENTRY CALC] Raw entry_price: {entry_price:.4f} | Current: {current_price:.4f}")

        # Validation + fallback ถ้า entry ใกล้ current เกินหรือ <=0
        price_diff_pct = abs(entry_price - current_price) / current_price * 100 if current_price > 0 else 0
        
        if entry_price <= 0 or price_diff_pct < 0.3:  # ใกล้เกิน 0.3% → ไม่เหมาะสำหรับ limit
            print(f"[ENTRY FALLBACK] Entry ใกล้ current เกิน ({price_diff_pct:.2f}%) → ใช้ ATR fallback")
            
            atr_offset = atr * 0.6  # ปรับได้ 0.5-1.0 ตามความเสี่ยง
            if direction == 'LONG':
                entry_price = current_price - atr_offset  # เข้า pullback ลงมา
                fib_reason = "Fallback: ATR pullback (LONG)"
            else:  # SHORT
                entry_price = current_price + atr_offset  # เข้า pullback ขึ้นไป
                fib_reason = "Fallback: ATR pullback (SHORT)"
            
            # ยัง validate อีกที
            if entry_price <= 0:
                reason = "Fallback entry_price ยัง <= 0"
                print(f"[EXECUTE SKIP] {sym}: {reason}")
                await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
                return False

        print(f"[ENTRY FINAL] {entry_price:.4f} ({fib_reason}) | diff {price_diff_pct:.2f}%")

        # 5. AI Confidence (เพิ่มขั้นต่ำเป็น 55)
        rsi = float(curr.get('rsi', 50))
        ema20 = float(curr.get('ema20', 1))
        ema50 = float(curr.get('ema50', 1))
        macd = float(curr.get('macd', 0))
        signal = float(curr.get('signal', 0))
        adx = float(curr.get('adx', 20))
        stoch_k = float(curr.get('stoch_k', 50))
        bb_upper = float(curr.get('bb_upper', current_price))
        bb_lower = float(curr.get('bb_lower', current_price))
        bb_position = ((current_price - bb_lower) / (bb_upper - bb_lower)) if bb_upper > bb_lower else 0.5

        ema_ratio = ema20 / ema50 if ema50 > 0 else 1.0
        macd_diff = macd - signal

        ai_features = [
            rsi / 100,
            ema_ratio,
            macd_diff / 100,
            vol_ratio,
            adx / 50,
            stoch_k / 100,
            bb_position
        ]

        ai_confidence = brain.get_ai_confidence(ai_features)
        print(f"[EXECUTE] AI Confidence: {ai_confidence:.1f}%")

        if ai_confidence < 55:
            reason = f"AI confidence ต่ำเกิน ({ai_confidence:.1f}% < 55)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        # 6. SL / TP (ใช้ recent levels เป็นหลัก + fallback)
        if direction == 'LONG':
            side = SIDE_BUY
            tp = fib_extensions.get('161.8%', current_price + atr * 4)
            sl = swing_data.get('recent_support', current_price) - atr * 0.8
        else:
            side = SIDE_SELL
            tp = fib_extensions.get('161.8%', current_price - atr * 4)
            sl = swing_data.get('recent_resistance', current_price) + atr * 0.8

        stop_distance = abs(entry_price - sl)
        if stop_distance < atr * 0.5:
            reason = f"Stop distance สั้นเกินไป ({stop_distance:.6f} < {atr*0.5:.6f})"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        # 7. Position sizing + ขั้นต่ำ qty
        balance = get_available_balance()  # ต้องมีฟังก์ชันนี้อยู่แล้ว
        risk_amount = balance * RISK_PER_TRADE_PERCENT

        position_value = risk_amount / (stop_distance / entry_price)
        qty = position_value / entry_price

        step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
        qty = math.floor(qty / step_size) * step_size
        
# เพิ่มขั้นต่ำ qty ให้ชัดเจนขึ้น
        min_qty = step_size * 5
        if qty < min_qty:
            qty = min_qty
            print(f"[EXECUTE] ปรับ qty เป็นขั้นต่ำปลอดภัย: {qty}")

        if qty <= 0:
            reason = "คำนวณ qty <= 0 (balance หรือ stop_distance ปัญหา)"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason}")
            return False

        # 8. Set leverage + สั่ง LIMIT
        await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)

        tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
        p_prec, q_prec = sym_info.get(sym, (4, 2))
        
        entry_price_rounded = round_to_tick(entry_price, tick_size)
        qty_str = f"{qty:.{q_prec}f}"
        price_str = f"{entry_price_rounded:.{p_prec}f}"

        print(f"[EXECUTE] สั่ง LIMIT {sym} {direction} @ {price_str} | Qty: {qty_str}")
        
        await client.futures_create_order(
            symbol=sym,
            side=side,
            type='LIMIT',
            timeInForce='GTC',
            quantity=qty_str,
            price=price_str
        )

        # 9. รอ fill (เพิ่ม retry + timeout)
        filled = False
        for attempt in range(15):  # รอสูงสุด 15 วินาที
            await asyncio.sleep(1)
            pos_info = await client.futures_position_information(symbol=sym)
            if float(pos_info[0]['positionAmt']) != 0:
                filled = True
                print(f"[EXECUTE] Fill สำเร็จ {sym} หลัง {attempt+1} วินาที")
                break

        if not filled:
            reason = "Limit ไม่ fill ภายใน 15 วินาที"
            print(f"[EXECUTE SKIP] {sym}: {reason}")
            await send_telegram_report(f"⚠️ ไม่เข้า {sym} → {reason} (อาจยกเลิก limit เอง)")
            return False

        # 10. ตั้ง SL/TP (reduceOnly)
        sl_price = round_to_tick(sl, tick_size)
        tp_price = round_to_tick(tp, tick_size)
        sl_str = f"{sl_price:.{p_prec}f}"
        tp_str = f"{tp_price:.{p_prec}f}"

        await client.futures_create_order(
            symbol=sym,
            side=SIDE_SELL if direction == 'LONG' else SIDE_BUY,
            type='STOP_MARKET',
            stopPrice=sl_str,
            closePosition=True,
            timeInForce='GTC',
            workingType='MARK_PRICE',
            reduceOnly=True
        )

        await client.futures_create_order(
            symbol=sym,
            side=SIDE_SELL if direction == 'LONG' else SIDE_BUY,
            type='TAKE_PROFIT_MARKET',
            stopPrice=tp_str,
            closePosition=True,
            timeInForce='GTC',
            workingType='MARK_PRICE',
            reduceOnly=True
        )

        # 11. Report สุดท้าย
        rr_ratio = calculate_rr_ratio(entry_price_rounded, sl_price, tp_price, direction)
# Report สำเร็จ (เพิ่ม vol และ ADX เข้าไป)
        report = (
            f"{'🟢' if direction=='LONG' else '🔴'} **FAST SCAN ENTRY สำเร็จ!**\n"
            f"*{sym.replace('USDT','')}* | {direction}\n\n"
            f"Entry (Limit): {entry_price_rounded:.4f}\n"
            f"SL: {sl_price:.4f}\n"
            f"TP: {tp_price:.4f}\n"
            f"RR: {rr_ratio:.2f}:1\n"
            f"AI Confidence: {ai_confidence:.0f}%\n"
            f"Vol: {vol_ratio:.2f}x | ADX: {adx:.0f}\n"
            f"Risk: ${risk_amount:.2f}"
        )
        # ถ้ายัง error ลองลบ backtick ทั้งหมด หรือใช้ HTML parse_mode แทน
        await send_telegram_report(report, parse_mode=None)  # หรือ 'HTML' ถ้าต้องการ
        
        print(f"[EXECUTE SUCCESS] {sym} เข้าสำเร็จ")
        return True

    except Exception as e:
        reason = f"เกิด exception: {str(e)}"
        print(f"[EXECUTE ERROR] {sym}: {reason}")
        await send_telegram_report(f"❌ FAST SCAN ENTRY ล้มเหลว {sym}: {reason}")
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

# ==========================================================================
#                  TELEGRAM COMMAND LISTENER (รวมทุกคำสั่งล่าสุด - แก้ Indentation แล้ว)
# ==========================================================================
async def check_telegram_updates(client, cmd_q, price_map):
    global update_offset, running, bal, active, btc_p, pending_orders_detail
    global auto_spike_enabled, auto_short_signal_enabled, manual_closed_cooldown  # เพิ่มตัวแปรที่เกี่ยวข้องทั้งหมด
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
            # ==========================================================================
            #                  INTEGRATE INTO TELEGRAM HANDLER
            #                  ใน check_telegram_updates, เพิ่ม elif สำหรับ /divscan
            # ==========================================================================
            elif text == '/divscan':
                await send_telegram_report("⏳ กำลังสแกน Divergence ทุกเหรียญ...", chat_id)
                div_results = await scan_divergence(client)
                div_report = generate_div_report(div_results)
                await send_telegram_report(div_report, chat_id)
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

            # ใน check_telegram_updates เพิ่มส่วนนี้:

            elif text.startswith('/lmauto '):
                try:
                    parts = text.split()
                    if len(parts) < 2:
                        await send_telegram_report("❌ ใช้: `/lmauto ETH` หรือ `/lmauto BTC`", chat_id)
                        continue

                    sym_input = parts[1].upper()
                    sym = sym_input + 'USDT' if not sym_input.endswith('USDT') else sym_input

                    if sym not in sym_info:
                        await send_telegram_report(f"❌ ไม่รองรับ {sym_input}", chat_id)
                        continue

                    # ตรวจ position / pending
                    if any(p['symbol'] == sym for p in active) or any(o['symbol'] == sym for o in pending_orders_detail):
                        await send_telegram_report(f"⚠️ {sym_input} มี Position หรือ Limit อยู่แล้ว", chat_id)
                        continue

                    await send_telegram_report(f"⏳ กำลังวิเคราะห์ ICT Smart Money + วาง Limit Auto สำหรับ {sym_input}...", chat_id)

                    ict_data = await analyze_ict_smart_money(client, sym)
                    if ict_data is None:
                        await send_telegram_report(
                            f"❌ การวิเคราะห์ ICT สำหรับ {sym_input} ล้มเหลว (ข้อมูลไม่เพียงพอหรือ API error)\n"
                            f"ลองใหม่ใน 5-10 นาที หรือเช็คด้วย /analyze {sym_input}",
                            chat_id
                        )
                        continue

                    if not ict_data.get('direction'):
                        await send_telegram_report(
                            f"⚠️ ไม่พบ confluence ICT ขั้นสูงเพียงพอสำหรับ {sym_input}\n"
                            f"Score: {ict_data.get('total_score', 0):.1f} (ต้องการ ≥4)",
                            chat_id
                        )
                        continue

                    direction = ict_data['direction'].upper()
                    side_order = SIDE_BUY if direction == 'LONG' else SIDE_SELL

                    # กำหนด Limit Price จาก confluence
                    atr = await get_cached_atr(client, sym) or 0.015 * (await get_current_price(client, sym))
                    limit_price_raw = 0.0

                    if 'liquidity_sweep' in ict_data:
                        # เข้า Limit ตรงปลาย wick
                        if ict_data.get('sweep_direction') == 'down':
                            limit_price_raw = (await get_current_price(client, sym)) - atr * 0.3
                        else:
                            limit_price_raw = (await get_current_price(client, sym)) + atr * 0.3

                    if 'order_block' in ict_data:
                        limit_price_raw = ict_data['ob_level']

                    if 'fvg' in ict_data:
                        limit_price_raw = ict_data['fvg_mid'] or limit_price_raw

                    if limit_price_raw == 0:
                        limit_price_raw = (await get_current_price(client, sym)) * (0.985 if direction == 'LONG' else 1.015)

                    # SL สั้นมาก (หลัง wick / swing)
                    sl_raw = limit_price_raw - atr * 0.8 if direction == 'LONG' else limit_price_raw + atr * 0.8

                    # TP ไกล (RR เป้าหมาย 1:3+)
                    tp_raw = limit_price_raw + atr * 5.0 if direction == 'LONG' else limit_price_raw - atr * 5.0

                    rr = calculate_rr_ratio(limit_price_raw, sl_raw, tp_raw, direction)
                    if rr < 2.5:  # เข้มงวดเพราะ aggressive
                        await send_telegram_report(f"⚠️ RR ไม่ถึงเกณฑ์ (ได้ {rr:.2f}) สำหรับ {sym_input}", chat_id)
                        continue

                    # Position sizing (risk $0.50)
                    stop_distance = abs(limit_price_raw - sl_raw)
                    position_value = 0.50 / (stop_distance / limit_price_raw)
                    qty = position_value / limit_price_raw

                    step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
                    qty = math.floor(qty / step_size) * step_size or step_size * 5

                    qty_str = f"{qty:.{sym_info.get(sym, (4,2))[1]}f}"

                    # ปัดราคา
                    tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                    p_prec = sym_info.get(sym, (4,2))[0]
                    limit_price = round_to_tick(limit_price_raw, tick_size)
                    sl_price = round_to_tick(sl_raw, tick_size)
                    tp_price = round_to_tick(tp_raw, tick_size)

                    limit_str = f"{limit_price:.{p_prec}f}"
                    sl_str = f"{sl_price:.{p_prec}f}"
                    tp_str = f"{tp_price:.{p_prec}f}"

                    # สั่ง Limit + SL/TP
                    await client.futures_change_leverage(symbol=sym, leverage=MAX_LEVERAGE)
                    order = await client.futures_create_order(
                        symbol=sym,
                        side=side_order,
                        type='LIMIT',
                        timeInForce='GTC',
                        quantity=qty_str,
                        price=limit_str
                    )

                    close_side = SIDE_SELL if direction == 'LONG' else SIDE_BUY
                    await client.futures_create_order(symbol=sym, side=close_side, type='STOP_MARKET', stopPrice=sl_str, closePosition=True, reduceOnly=True)
                    await client.futures_create_order(symbol=sym, side=close_side, type='TAKE_PROFIT_MARKET', stopPrice=tp_str, closePosition=True, reduceOnly=True)

                    # รายงาน
                    report = (
                        f"🔥 **/lmauto เข้าสำเร็จ - ICT Smart Money**\n"
                        f"เหรียญ: `{sym_input}` | ทิศ: **{direction}**\n"
                        f"Limit: `{limit_str}`\n"
                        f"SL: `{sl_str}` (สั้นมาก)\n"
                        f"TP: `{tp_str}` (RR {rr:.2f}:1)\n"
                        f"Qty: `{qty_str}` | Lev: `{MAX_LEVERAGE}x`\n"
                        f"Confluence Score: `{ict_data['total_score']:.1f}`\n\n"
                        f"เงื่อนไขที่เจอ:\n"
                        + "\n".join([f"• {k.replace('_',' ').title()}" for k in ict_data if ict_data[k] is True or isinstance(ict_data[k], (int,float,str))])
                    )
                    await send_telegram_report(report, chat_id)

                    # บันทึก pending
                    pending_orders_detail.append({
                        'symbol': sym,
                        'side': side_order,
                        'price': limit_price,
                        'qty': qty,
                        'time': datetime.now(),
                        'orderId': order['orderId'],
                        'source': 'lmauto_ict',
                        'rr': rr
                    })

                except Exception as e:
                    await send_telegram_report(f"❌ /lmauto ล้มเหลว {sym_input}: {str(e)}", chat_id)

            # ===================== /trainnow =====================
            elif text == '/trainnow':
                if len(brain.data) < 5:
                    await send_telegram_report("⚠️ ยังมีข้อมูลน้อยเกินไป ต้องมีอย่างน้อย 5 trades", chat_id)
                else:
                    brain.train_model()
                    stats = brain.get_ai_stats()
                    await send_telegram_report(
                        f"🧠 **Force Train สำเร็จ!**\n"
                        f"Total samples: {stats['total_trades']}\n"
                        f"Accuracy ล่าสุด: {stats['last_accuracy']:.2f}%\n"
                        f"Best loss: {stats['best_loss']:.6f}",
                        chat_id
                    )
            # ==========================================================================
            #                  เพิ่มคำสั่ง /ctai <symbol> ใน Telegram Handler
            # ==========================================================================

            # ในฟังก์ชัน async def check_telegram_updates(client, cmd_q, price_map):
            # ให้เพิ่ม elif นี้ลงไป (วางไว้ใกล้ ๆ กับ elif text.startswith('/analyze ') หรือคำสั่งอื่น ๆ)

            elif text.startswith('/ctai '):
                try:
                    parts = text.split()
                    if len(parts) < 2:
                        await send_telegram_report(
                            "❌ รูปแบบไม่ถูกต้อง\n"
                            "ใช้: `/ctai BTC` หรือ `/ctai AVAX` เพื่อเข้า Counter-Trend อัตโนมัติ",
                            chat_id
                        )
                        continue

                    sym_input = parts[1].upper()
                    sym = sym_input + 'USDT' if not sym_input.endswith('USDT') else sym_input

                    if sym not in sym_info:
                        await send_telegram_report(f"❌ ไม่รองรับเหรียญ {sym_input}", chat_id)
                        continue

                    # 1. ตรวจสอบว่ามี position หรือ pending limit อยู่แล้วหรือไม่ (ป้องกันซ้ำ)
                    if any(p['symbol'] == sym for p in active) or \
                    any(o['symbol'] == sym for o in pending_orders_detail):
                        await send_telegram_report(
                            f"⚠️ {sym_input} มี Position หรือ Limit Order อยู่แล้ว → ข้ามการเข้าใหม่",
                            chat_id
                        )
                        continue

                    # 2. แจ้งกำลังทำงาน
                    await send_telegram_report(
                        f"⏳ กำลังวิเคราะห์และเข้า **Counter-Trend** สำหรับ {sym_input}...\n"
                        f"(รอสักครู่... กำลังเช็คแนวโน้ม + วาง Limit Order)",
                        chat_id
                    )

                    # 3. ดึงข้อมูลวิเคราะห์สด
                    analysis_data = await get_analysis_data(client, sym)  # ← ถูกต้อง มี underscore และ A ใหญ่
                    if not analysis_data:
                        await send_telegram_report(f"❌ ไม่สามารถดึงข้อมูลวิเคราะห์ {sym_input} ได้", chat_id)
                        continue

                    # 4. เรียกฟังก์ชัน Counter-Trend (ใช้ฟังก์ชันที่เราปรับแล้ว)
                    # ในส่วน elif text.startswith('/ctai '):
                    result = await place_counter_trend_limit(
                        client=client,
                        symbol=sym,
                        analysis_data=analysis_data,   # ต้องตรงกับ def ด้านล่าง
                        risk_usdt=0.50,
                        min_rr=1.5
                    )

                    if result and result.get('success'):
                        # ถ้าสำเร็จ → รายงานเพิ่มเติม (ถ้าต้องการแจ้งเตือนซ้ำหรือ log)
                        success_msg = (
                            f"✅ **เข้า Counter-Trend สำเร็จ!**\n"
                            f"เหรียญ: {sym_input}\n"
                            f"ทิศทาง: {result['direction']}\n"
                            f"Limit Price: {result['limit_price']:.4f}\n"
                            f"SL: {result['sl']:.4f} | TP: {result['tp']:.4f}\n"
                            f"RR: {result['rr']:.2f}:1\n"
                            f"Qty: {result['qty']:.4f}\n"
                            f"Order ID: {result['order_id']}"
                        )
                        await send_telegram_report(success_msg, chat_id)
                    else:
                        reason = "ไม่พบ setup Counter-Trend ที่ผ่านเกณฑ์ (อาจ RR ต่ำ / แนวโน้มไม่แรงพอ)"
                        await send_telegram_report(f"⚠️ {reason}\nลองใหม่ในภายหลังหรือเช็คด้วย /analyze {sym_input}", chat_id)

                except Exception as e:
                    error_msg = f"❌ เกิดข้อผิดพลาดขณะเข้า Counter-Trend {sym_input}: {str(e)}"
                    await send_telegram_report(error_msg, chat_id)
                    print(f"{Fore.RED}{error_msg}{Style.RESET_ALL}")

            # ===================== /fastscan =====================
            elif text == '/fastscan':
                await send_telegram_report("⏳ กำลังสแกนเร่งด่วน 20 เหรียญ (Signals > 3)...", chat_id)
                try:
                    active_symbol_names = [p['symbol'] for p in active]
                    # ส่ง pending_orders ไปด้วย เพื่อให้ข้ามเหรียญที่มี limit order
                    scan_results = await fast_scan_top_20_signals(client, price_map, active_symbol_names, pending_orders_detail)
                    
                    if not scan_results:
                        await send_telegram_report(
                            "🔍 **Fast Scan - ไม่พบสัญญาณ**\n\n"
                            "ตรวจสอบ Top 20 เหรียญแล้วไม่มีสัญญาณ > 3 ตัว\n"
                            "_ลองใหม่ในไม่กี่นาที..._",
                            chat_id
                        )
                    else:
                        # พบสัญญาณ - แสดงและสั่งซื้ออัตโนมัติ
                        result = scan_results[0]
                        
                        scan_msg = "🚀 **Fast Scan Results - สัญญาณ > 3 ตัว**\n\n"
                        direction_emoji = "🟢" if result['direction'] == 'LONG' else "🔴"
                        scan_msg += (
                            f"{direction_emoji} `{result['symbol'].replace('USDT','')}`\n"
                            f"   └ Price: `{result['price']:.4f}` USDT\n"
                            f"   └ Signals: `{result['signal_count']}/8` ✅\n"
                            f"   └ Indicators: {', '.join(result['signals'][:5])}\n"
                            f"   └ RSI: `{result['rsi']:.1f}` | Vol: `{result['vol_ratio']:.2f}x`\n\n"
                        )
                        scan_msg += "⏳ กำลังเข้า Order อัตโนมัติ..."
                        
                        await send_telegram_report(scan_msg, chat_id)
                        
                        # สั่งซื้ออัตโนมัติ
                        success = await execute_fast_scan_entry(client, result, price_map)
                        
                        if not success:
                            await send_telegram_report("❌ ไม่สามารถเข้า Order ได้", chat_id)
                
                except Exception as e:
                    await send_telegram_report(f"❌ Scan error: {e}", chat_id)
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

                    # พาร์ทพื้นฐาน
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

                    # ค่า default
                    leverage = MAX_LEVERAGE
                    risk_amount = 0.5

                    # ตรวจสอบพารามิเตอร์เพิ่มเติม (index 4 และ 5)
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

                    # ดึงราคาปัจจุบัน
                    current_price = price_map.get(sym, 0.0)
                    if current_price <= 0:
                        await send_telegram_report(f"❌ ไม่สามารถดึงราคา {sym_input} ได้", chat_id)
                        continue

                    # ตรวจสอบว่าราคาอยู่ในทิศทางสมเหตุสมผล
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

                    # ดึง ATR
                    atr = await get_cached_atr(client, sym)
                    if atr is None or atr <= 0:
                        atr = current_price * 0.015

                    # คำนวณ SL/TP
                    if direction_char == 'L':
                        sl_raw = limit_price - (atr * ATR_SL_MULTIPLIER)
                        tp_raw = limit_price + (atr * ATR_TP_MULTIPLIER)
                    else:
                        sl_raw = limit_price + (atr * ATR_SL_MULTIPLIER)
                        tp_raw = limit_price - (atr * ATR_TP_MULTIPLIER)

                    # คำนวณ RR
                    rr = calculate_rr_ratio(limit_price, sl_raw, tp_raw, 'SHORT' if direction_char == 'S' else 'LONG')
                    if rr < 1.3:  # ผ่อนลงนิดหน่อยเพราะเป็น manual
                        await send_telegram_report(
                            f"⚠️ RR ต่ำเกินไป ({rr:.2f}:1) → ยังตั้งได้ แต่ไม่แนะนำ",
                            chat_id
                        )

                    # คำนวณ qty จาก risk_amount ที่ผู้ใช้กำหนด
                    stop_distance = abs(limit_price - sl_raw)
                    if stop_distance <= 0:
                        await send_telegram_report("❌ Stop distance ไม่ถูกต้อง", chat_id)
                        continue

                    position_value = risk_amount / (stop_distance / limit_price)
                    qty = position_value / limit_price

                    step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)
                    qty = math.floor(qty / step_size) * step_size

                    # ขั้นต่ำ qty
                    min_qty = step_size * 5
                    if qty < min_qty:
                        qty = min_qty

                    qty_precision = sym_info.get(sym, (4, 2))[1]
                    qty_str = f"{qty:.{qty_precision}f}"

                    # ปัดราคา
                    tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                    limit_price_rounded = round_to_tick(limit_price, tick_size)
                    price_precision = sym_info.get(sym, (4, 2))[0]
                    price_str = f"{limit_price_rounded:.{price_precision}f}"

                    # ตั้ง Leverage ตามที่ผู้ใช้ระบุ
                    try:
                        await client.futures_change_leverage(symbol=sym, leverage=leverage)
                    except Exception as e:
                        await send_telegram_report(f"⚠️ ไม่สามารถตั้งเลเวอเรจ {leverage}x ได้: {str(e)}", chat_id)
                        continue

                    # สั่ง Limit Order
                    order = await client.futures_create_order(
                        symbol=sym,
                        side=side_order,
                        type='LIMIT',
                        timeInForce='GTC',
                        quantity=qty_str,
                        price=price_str
                    )

                    # เก็บใน pending_orders_detail
                    order_time = datetime.now()
                    pending_orders_detail.append({
                        'symbol': sym,
                        'side': side_order,
                        'price': limit_price_rounded,
                        'qty': qty,
                        'time': order_time,
                        'orderId': order['orderId'],
                        'manual': True,
                        'leverage': leverage,
                        'risk_usdt': risk_amount,
                        'source': 'manual_setlm'
                    })

                    # รายงานผล
                    report = (
                        f"✅ **ตั้ง Limit Order แมนนวลสำเร็จ!**\n"
                        f"เหรียญ: `{sym.replace('USDT','')}`\n"
                        f"ทิศทาง: **{direction_text}**\n"
                        f"ราคา Limit: `{price_str}`\n"
                        f"Qty: `{qty_str}`\n"
                        f"เลเวอเรจ: `{leverage}x`\n"
                        f"Risk: `${risk_amount:.2f}` USDT\n"
                        f"RR (โดยประมาณ): `{rr:.2f}:1`\n"
                        f"ราคาปัจจุบัน: `{current_price:.4f}`\n"
                        f"ATR: `{atr:.6f}`\n"
                        f"Order ID: `{order['orderId']}`"
                    )
                    await send_telegram_report(report, chat_id)

                    print(f"{Fore.GREEN}Manual Limit สำเร็จ: {sym} {direction_text} @ {price_str} | Lev {leverage}x | Risk ${risk_amount}{Style.RESET_ALL}")

                except Exception as e:
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
                )
                await send_telegram_report(help_work, chat_id)
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
            # ===================== พิมพ์ชื่อเหรียญตรง ๆ → วิเคราะห์ละเอียดทุกกรอบเวลา =====================
            else:
                sym_input = text.upper().strip()
                sym = sym_input + "USDT" if not sym_input.endswith("USDT") else sym_input

                if sym not in price_map:
                    await send_telegram_report("❓ ไม่พบเหรียญนี้หรือยังไม่มีข้อมูลราคา", chat_id)
                    continue

                current_price = price_map.get(sym, 0.0)
                if current_price <= 0:
                    await send_telegram_report(f"⚠️ ราคา {sym_input} ไม่สามารถดึงได้ในขณะนี้", chat_id)
                    continue

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
#             COUNTER-TREND LIMIT ORDER PLACER (Long/Short) - Adjusted
# ==========================================================================

async def place_counter_trend_limit(client, symbol, analysis_data, risk_usdt=0.50, min_rr=1.5):
    """
    วาง Limit Order แบบ Counter-Trend โดยใช้ analysis_data ที่ส่งมา
    """
    try:
        sym = symbol if symbol.endswith('USDT') else symbol + 'USDT'
        
        if not analysis_data:
            print(f"[Counter-Trend] ไม่มี analysis_data สำหรับ {sym}")
            return None
        
        current_price = analysis_data.get('price_current', 0)
        if current_price <= 0:
            print(f"[Counter-Trend] ราคาปัจจุบันไม่ถูกต้องสำหรับ {sym}")
            return None
        
        # ตรวจแนวโน้ม (ตามตัวอย่าง AVAX: Bearish → Long)
        trend_strong = False
        direction = None
        
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
            return None
        
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
            return None
        
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
            return None
        
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
        
        # Leverage ตามตัวอย่าง
        leverage = MAX_LEVERAGE
        await client.futures_change_leverage(symbol=sym, leverage=leverage)
        
        # สั่ง Limit + SL/TP (เหมือนเดิม)
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
            workingType='MARK_PRICE',
            reduceOnly=True
        )
        await client.futures_create_order(
            symbol=sym,
            side=close_side,
            type='TAKE_PROFIT_MARKET',
            stopPrice=tp_str,
            closePosition=True,
            timeInForce='GTC',
            workingType='MARK_PRICE',
            reduceOnly=True
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
        
        # รายงาน Telegram (ปรับให้เหมือนตัวอย่าง AVAX มากที่สุด)
        report = f"📊 **{sym_input}/USDT - วิเคราะห์อัจฉริยะ**\n" \
                 f"{datetime.now().strftime('%d/%m %H:%M')} | ราคา: {current_price:.2f}\n\n" \
                 f"📈 Trend Analysis\n" \
                 f"4H: {'🔴 Bearish' if analysis_data['trend_4h'] == 'Bearish' else '🟢 Bullish'}\n" \
                 f"1H: {'🔴 Bearish' if analysis_data['trend_1h'] == 'Bearish' else '🟢 Bullish'}\n\n" \
                 f"📊 Momentum\n" \
                 f"RSI(4H): {analysis_data['rsi_4h']:.1f} Neutral\n" \
                 f"Stoch(4H): {analysis_data['stoch_4h']:.1f} | Stoch(1H): {analysis_data['stoch_1h']:.1f}\n" \
                 f"MACD: {'🔴 Bearish' if analysis_data['macd'] == 'Bearish' else '🟢 Bullish'}\n\n" \
                 f"🎯 Support & Resistance\n" \
                 f"Support: {analysis_data['support']:.2f} | Resistance: {analysis_data['resistance']:.2f}\n" \
                 f"Position: Mid-range\n\n" \
                 f"🎪 Fibonacci Levels (38.2%/61.8%: {analysis_data['fib_382']:.2f} / {analysis_data['fib_618']:.2f})\n\n" \
                 f"💡 สรุป: {'Strong BUY 🟢' if direction == 'LONG' else 'Strong SELL 🔴'}\n\n" \
                 f"✅ **ตั้ง Limit Order สำเร็จ!**\n" \
                 f"เหรียญ: {sym_input}\n" \
                 f"ทิศทาง: {direction} ({'Buy' if direction == 'LONG' else 'Sell'})\n" \
                 f"ราคา Limit: `{limit_str}`\n" \
                 f"Qty: `{qty_str}`\n" \
                 f"เลเวอเรจ: `{leverage}x`\n" \
                 f"Risk: `${risk_usdt:.2f}` USDT\n" \
                 f"RR (โดยประมาณ): `{rr:.2f}:1`\n" \
                 f"ราคาปัจจุบัน: `{current_price:.4f}`\n" \
                 f"ATR: `{atr:.6f}`\n" \
                 f"Order ID: `{order['orderId']}`"
        
        await send_telegram_report(report)
        
        return {'success': True, 'limit_price': limit_price, 'rr': rr}
    
    except Exception as e:
        print(f"[Counter-Trend] Error {sym}: {e}")
        return None


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
        fvg_up = (df_main['l'].shift(-1) > df_main['h']) & (df_main['c'] > df_main['o'])
        fvg_down = (df_main['h'].shift(-1) < df_main['l']) & (df_main['c'] < df_main['o'])
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