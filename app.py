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

# Global variables
prev_prices = {}
ticker_offset = 0
ticker_direction = 1

bal = 0.0
active = []
btc_p = 0.0
pending_orders_detail = []
sym_info = {}
sym_filters = {}

top_50_symbols = []
last_volume_update = datetime.min
VOLUME_UPDATE_INTERVAL = timedelta(hours=4)

# เก็บ symbol ที่แจ้งคำแนะนำแล้ว (ไม่แจ้งซ้ำ)
sl_tp_advice_notified = set()

signal_features = {}

if TELEGRAM_BOT_TOKEN:
    try:
        telegram_bot = Bot(token=TELEGRAM_BOT_TOKEN)
        print(f"{Fore.GREEN}Telegram Bot initialized successfully!")
    except Exception as e:
        print(f"{Fore.RED}Telegram initialization failed: {e}")
        telegram_bot = None
else:
    print(f"{Fore.YELLOW}Telegram not configured. Skipping Telegram features.")

# ==========================================================================
#                                 CONFIG
# ==========================================================================
API_KEY = os.getenv("BINANCE_API_KEY")
API_SECRET = os.getenv("BINANCE_API_SECRET")

if not API_KEY or not API_SECRET:
    print(f"{Fore.RED}Error: ไม่พบ API Key ใน .env file!")
    sys.exit(1)
#True
USE_TESTNET = False

MEMORY_FILE = "titan_memory.json"

# ==========================================================================
#                                 CONFIG $1000
# ==========================================================================
#MAX_LEVERAGE = 20
#RISK_PER_TRADE_PERCENT = 0.025
#MAX_OPEN_POSITIONS = 50
#SIGNAL_THRESHOLD_LONG = 6
#SIGNAL_THRESHOLD_SHORT = 7
#ADX_THRESHOLD = 25
#SCAN_BATCH_SIZE = 60
#MIN_NOTIONAL_USDT = 5
#MIN_BALANCE_TO_TRADE = 100.0

# ปรับตาม Fibonacci: รอ pullback ลึกขึ้น
#ENTRY_PULLBACK_PERCENT = 10.8
#LIMIT_ORDER_TIMEOUT_HOURS = 2

#ATR_SL_MULTIPLIER = 3.0
#ATR_TP_MULTIPLIER = 6.0

# ==========================================================================
#                        OPTIMIZED CONFIG FOR $5 CAPITAL
# ==========================================================================

MAX_LEVERAGE = 10                  # ลดจาก 20 → 10x เพื่อความปลอดภัย (ลดความเสี่ยงล้างพอร์ต)
RISK_PER_TRADE_PERCENT = 0.5       # เพิ่มจาก 0.025 → 0.5% ของพอร์ตต่อไม้ (เหมาะกับทุนน้อย)
MAX_OPEN_POSITIONS = 3             # ลดจาก 50 → 3 ไม้พร้อมกัน (ป้องกัน over-exposure)
SIGNAL_THRESHOLD_LONG = 7          # เพิ่มจาก 6 → 7 (สัญญาณต้องแน่นกว่าเดิม)
SIGNAL_THRESHOLD_SHORT = 8         # เพิ่มจาก 7 → 8 (เข้มงวดกว่า LONG เพราะตลาดลงเร็ว)
ADX_THRESHOLD = 30                 # เพิ่มจาก 25 → 30 (เทรนด์ต้องแข็งแรงจริงๆ)
SCAN_BATCH_SIZE = 30               # ลดจาก 60 → 30 (ลดการสแกนหนักเกินไป)
MIN_NOTIONAL_USDT = 5              # คงไว้ (ขั้นต่ำ Binance Futures)
MIN_BALANCE_TO_TRADE = 4.0         # ลดจาก 100 → 4 (ให้บอทเริ่มเทรดได้แม้ทุนเหลือน้อย)

# ปรับการเข้าให้รอโซนดีจริง ๆ ตาม Fibonacci
ENTRY_PULLBACK_PERCENT = 12.0      # เพิ่มจาก 10.8 → 12.0% รอ pullback ลึกขึ้นเพื่อเข้าในจุดที่ดีกว่า
LIMIT_ORDER_TIMEOUT_HOURS = 4      # เพิ่มจาก 2 → 4 ชม. ให้เวลา Limit รอจับมากขึ้น

# Risk Management ที่สมดุล
ATR_SL_MULTIPLIER = 2.5            # ลดจาก 3.0 → 2.5 (SL แน่นขึ้น ลดความเสี่ยง)
ATR_TP_MULTIPLIER = 6.0            # คงไว้ (RR 1:2.4 ยังดีอยู่)

MAJOR_TICKER_SYMBOLS = [
    'BTCUSDT', 'ETHUSDT', 'SOLUSDT', 'BNBUSDT', 'XRPUSDT', 'ADAUSDT',
    'DOGEUSDT', 'AVAXUSDT', 'LINKUSDT', 'DOTUSDT', 'TRXUSDT', 'MATICUSDT',
    'LTCUSDT', 'BCHUSDT', 'NEARUSDT', 'UNIUSDT', 'SUIUSDT', 'APTUSDT'
]

prev_prices = {sym: 0.0 for sym in MAJOR_TICKER_SYMBOLS}

# ==========================================================================
#                   NATIVE INDICATORS
# ==========================================================================
def calculate_indicators(kline_data):
    try:
        df = pd.DataFrame(kline_data, columns=['ts','o','h','l','c','v','ct','qv','nt','tb','tq','i']).astype(float)
        
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

        df['vol_ma'] = df['v'].rolling(20).mean()

        up = df['h'].diff()
        down = -df['l'].diff()
        plus_dm = up.where((up > down) & (up > 0), 0)
        minus_dm = down.where((down > up) & (down > 0), 0)
        tr_smooth = true_range.ewm(span=14, adjust=False).mean()
        plus_di = 100 * (plus_dm.ewm(span=14, adjust=False).mean() / tr_smooth)
        minus_di = 100 * (minus_dm.ewm(span=14, adjust=False).mean() / tr_smooth)
        dx = (abs(plus_di - minus_di) / (plus_di + minus_di + 1e-9)) * 100
        df['adx'] = dx.ewm(span=14, adjust=False).mean()

        return df
    except Exception as e:
        return pd.DataFrame()

# ==========================================================================
#                            AI BRAIN
# ==========================================================================
class SimpleMLP(nn.Module):
    def __init__(self, input_size, hidden_size=32):
        super().__init__()
        self.fc1 = nn.Linear(input_size, hidden_size)
        self.fc2 = nn.Linear(hidden_size, 1)

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = torch.sigmoid(self.fc2(x))
        return x

class TitanBrain:
    def __init__(self):
        self.memory_file = "titan_memory.json"
        self.model_file = "titan_model.pth"
        self.data = self.load_memory()
        input_size = len(self.data[0][0]) if self.data else 7  # assume 7 features
        self.model = SimpleMLP(input_size)
        if os.path.exists(self.model_file):
            try:
                self.model.load_state_dict(torch.load(self.model_file))
            except:
                pass
        self.train_model()  # train if data enough

    def load_memory(self):
        if os.path.exists(self.memory_file):
            with open(self.memory_file, 'r') as f:
                data_json = json.load(f)
                return [(torch.tensor(d['features'], dtype=torch.float32), d['label']) for d in data_json]
        return []

    def save_memory(self):
        data_json = [{'features': x.tolist(), 'label': y} for x, y in self.data]
        with open(self.memory_file, 'w') as f:
            json.dump(data_json, f)
        if self.model:
            torch.save(self.model.state_dict(), self.model_file)

    def update_memory(self, features, is_win):
        feat_tensor = torch.tensor(features, dtype=torch.float32)
        label = 1.0 if is_win else 0.0
        self.data.append((feat_tensor, label))
        self.save_memory()
        self.train_model()

    def train_model(self):
        if len(self.data) < 10:
            return
        optimizer = optim.Adam(self.model.parameters(), lr=0.001)
        loss_fn = nn.BCELoss()
        epochs = 200
        batch_size = 8
        self.model.train()
        for epoch in range(epochs):
            np.random.shuffle(self.data)  # shuffle
            for i in range(0, len(self.data), batch_size):
                batch = self.data[i:i+batch_size]
                X_batch = torch.stack([x for x,y in batch])
                y_batch = torch.tensor([[y] for x,y in batch], dtype=torch.float32)
                pred = self.model(X_batch)
                loss = loss_fn(pred, y_batch)
                optimizer.zero_grad()
                loss.backward()
                optimizer.step()
        self.save_memory()  # save after train

    def get_ai_confidence(self, f):
        if len(self.data) < 10:
            return 50.0
        self.model.eval()
        with torch.no_grad():
            feat = torch.tensor(f, dtype=torch.float32).unsqueeze(0)
            prob = self.model(feat).item() * 100
            return prob

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

        short_score = 0
        if curr['c'] < curr['ema200']: short_score += 1
        if curr['ema20'] < curr['ema50']: short_score += 1
        if curr['rsi'] < 50: short_score += 1
        if curr['macd'] < curr['signal']: short_score += 1
        if curr['c'] < curr['bb_lower']: short_score += 1
        if curr['v'] > curr['vol_ma']: short_score += 1
        if curr['c'] < curr['o']: short_score += 1
        if curr['adx'] > ADX_THRESHOLD: short_score += 1

        btc_k = await client.futures_klines(symbol="BTCUSDT", interval="15m", limit=250)
        btc_df = calculate_indicators(btc_k)
        if not btc_df.empty:
            btc_curr = btc_df.iloc[-1]
            if btc_curr['c'] > btc_curr['ema200']:
                short_score = 0  

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

        return {"symbol": symbol, "side": side, "score": score, "ai": ai_conf, "atr": atr_val, "curr_p": curr_p}

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
    if tick_size <= 0: return price
    return round(price / tick_size) * tick_size

# ==========================================================================
#                       RISK MANAGEMENT
# ==========================================================================
def calculate_position_size(balance, entry_price, atr, symbol, sym_filters, sym_info):
    try:
        if atr <= 0 or entry_price <= 0: return 0.0
        
        risk_amount = balance * RISK_PER_TRADE_PERCENT
        stop_distance_percent = (atr * ATR_SL_MULTIPLIER) / entry_price
        position_value = risk_amount / (stop_distance_percent + 1e-9)
        raw_qty = position_value / entry_price
        notional = raw_qty * entry_price
        
        if notional < MIN_NOTIONAL_USDT: return 0.0
        
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
#                     TELEGRAM HELPER (รองรับส่งรูปภาพ)
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
def print_dashboard(balance, active_positions, pending_orders, price_map, btc_price, scanning=False):
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
    print(f"{Back.BLACK}║ {mode_str}{Fore.CYAN} TITAN LIMIT SWING v31.3 {Fore.WHITE}│ {Fore.MAGENTA}📊 TOP 100 VOLUME {Fore.WHITE}│ 🕒 {Fore.WHITE}{time_now} {' ':<65}║{Style.RESET_ALL}{Fore.RED}{heartbeat}{Style.RESET_ALL}")
    print(f"{Back.BLACK}{Fore.CYAN}╠" + "═" * 188 + "╣{Style.RESET_ALL}")
    
    balance_str = f"💰 BALANCE: {Fore.YELLOW}{Style.BRIGHT}{balance:,.2f}{Style.NORMAL} USDT"
    pnl_str = f"📈 TOTAL PNL: {bright_pnl}{pnl_color}{total_pnl:+,.2f}{Style.RESET_ALL} USDT"
    btc_str = f"₿ BTC PRICE: {Fore.YELLOW}{Style.BRIGHT}{btc_price:,.1f}{Style.NORMAL}"
    pending_str = f"⏳ PENDING: {Fore.MAGENTA}{len(pending_orders)}"
    active_str = f"⭐ POSITIONS: {Fore.CYAN}{len(active_positions)}/{MAX_OPEN_POSITIONS}"
    
    print(f"{Back.BLACK}║  {balance_str:<40} {pnl_str:<45} {btc_str:<35} {status_str:<25} {active_str}{pending_str.rjust(20)}  ║{Style.RESET_ALL}")
    print(f"{Back.BLACK}{Fore.CYAN}╚" + "═" * 188 + "╝{Style.RESET_ALL}\n")
    
    print(f"{Fore.CYAN}{Style.BRIGHT}⭐ ACTIVE POSITIONS ({len(active_positions)} / {MAX_OPEN_POSITIONS}){Style.RESET_ALL}")
    if active_positions:
        print(f" {Fore.WHITE}{'ID':<4} {'SYMBOL':<12} {'SIDE':<12} {'ENTRY':<12} {'PRICE':<12} {'PNL':<15} {'ROE%':<10} {'SL DIST':<20} {'TP DIST':<20}")
        print(f" {Fore.LIGHTBLACK_EX}{'─' * 188}")
        
        for i, p in enumerate(active_positions, 1):
            side_icon = "📈 LONG 🟢" if p['side'] == 'LONG' else "📉 SHORT 🔴"
            side_color = Fore.GREEN if p['side'] == 'LONG' else Fore.RED
            pc = Fore.GREEN if p['pnl'] >= 0 else Fore.RED
            roe = (p['pnl'] / p['margin'] * 100) if p['margin'] > 0 else 0.0
            
            curr_price = p['curr_price']
            
            if p['sl'] > 0 and curr_price > 0:
                sl_dist = abs(curr_price - p['sl']) / curr_price * 100
                sl_alert = f"{Back.RED}{Fore.WHITE}{Style.BRIGHT} DANGER! {Style.RESET_ALL}" if sl_dist < 1.5 else ""
                sl_show = f"{sl_alert}{Fore.WHITE}{p['sl']:.6f} {Fore.RED}↓{sl_dist:.2f}%"
            else:
                sl_show = f"{Fore.RED}NO SL"
            
            if p['tp'] > 0 and curr_price > 0:
                tp_dist = abs(p['tp'] - curr_price) / curr_price * 100
                tp_near = f"{Fore.YELLOW}{Style.BRIGHT}★ {Style.NORMAL}" if tp_dist < 2.0 else ""
                tp_show = f"{tp_near}{Fore.WHITE}{p['tp']:.6f} {Fore.GREEN}↑{tp_dist:.2f}%"
            else:
                tp_show = f"{Fore.RED}NO TP"

            print(f" {Fore.YELLOW}{Style.BRIGHT}{i:<4}{Style.NORMAL} "
                  f"{side_color}{p['symbol'].replace('USDT',''):<12}{Fore.WHITE} "
                  f"{side_icon:<12} "
                  f"{Fore.WHITE}{p['entry']:<12.6f} "
                  f"{Fore.CYAN}{Style.BRIGHT}{curr_price:<12.6f}{Style.NORMAL} "
                  f"{pc}{p['pnl']:+15.2f} "
                  f"{pc}{roe:+10.2f}% "
                  f"{sl_show:<20} "
                  f"{tp_show:<20}")
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
#                  TELEGRAM COMMAND LISTENER (รวม /analyze + กราฟ Fibonacci สวยงาม)
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

            if TELEGRAM_CHAT_ID and str(chat_id) != TELEGRAM_CHAT_ID:
                await telegram_bot.send_message(chat_id=chat_id, text="❌ ไม่ได้รับอนุญาต")
                continue

            print(f"{Fore.MAGENTA}Telegram command: {text} from {chat_id}")

            if text == '/help':
                help_text = (
                    "📋 **คำสั่ง TITAN PRO Bot**\n\n"
                    "💰 ดูราคา → พิมพ์ `BTC`, `ETH`, `SOL`\n"
                    "📊 `/report` หรือ `/status` → สถานะเต็ม\n"
                    "⏳ `/limits` → รายการ Limit Orders ทั้งหมด\n"
                    "🔍 `/analyze BTC` → วิเคราะห์ + กราฟ Fibonacci 4h (สวยงาม)\n"
                    "🛠 `/cancel` → ยกเลิก Limit ทั้งหมด\n"
                    "🛑 `/closeall` → ปิดทุก Position\n"
                    "🚪 `/q` → หยุดบอท\n\n"
                    "_LFG!_ 🚀"
                )
                await send_telegram_report(help_text, chat_id)

            elif text in ['/report', '/status']:
                lines = [f"📊 **สถานะบอท**"]
                lines.append(f"💰 Balance: {bal:,.2f} USDT")
                lines.append(f"📈 BTC: {btc_p:,.0f}")
                total_pnl = sum(p['pnl'] for p in active)
                lines.append(f"📊 PNL: {total_pnl:+.2f} USDT")
                lines.append(f"⏳ Pending: {len(pending_orders_detail)}")
                if active:
                    lines.append(f"\n**ตำแหน่งที่เปิดอยู่**")
                    for p in active:
                        lines.append(f"• {p['symbol']} {p['side']} | PNL: {p['pnl']:+.2f}")
                await send_telegram_report("\n".join(lines), chat_id)

            elif text in ['/cancel', '/c']:
                await cmd_q.put('c')
                await send_telegram_report("🗑️ กำลังยกเลิก Limit Orders ทั้งหมด...", chat_id)

            elif text in ['/closeall', '/a']:
                await cmd_q.put('a')
                await send_telegram_report("🔴 กำลังปิดทุก Position และยกเลิก Orders...", chat_id)

            elif text in ['/qq', '/quit']:
                running = False
                await send_telegram_report("🛑 บอทกำลังหยุดทำงานอย่างปลอดภัย...", chat_id)

            elif text == '/limits':
                report = get_pending_limits_report(pending_orders_detail, price_map)
                await send_telegram_report(report, chat_id)

            elif text.startswith('/analyze '):
                try:
                    sym_input = text.split(' ', 1)[1].upper()
                    sym = sym_input + 'USDT'
                    current_price = price_map.get(sym, 0.0)
                    if current_price == 0.0:
                        await send_telegram_report("❓ ไม่พบเหรียญนี้หรือราคา", chat_id)
                        continue

                    k = await client.futures_klines(symbol=sym, interval="4h", limit=100)
                    df = pd.DataFrame(k, columns=['ts', 'o', 'h', 'l', 'c', 'v', 'ct', 'qv', 'nt', 'tb', 'tq', 'i']).astype(float)

                    high = df['h'].max()
                    low = df['l'].min()
                    diff = high - low

                    fib_levels = {
                        '0.0% (High)': high,
                        '23.6%': high - 0.236 * diff,
                        '38.2%': high - 0.382 * diff,
                        '50.0%': high - 0.5 * diff,
                        '61.8%': high - 0.618 * diff,
                        '78.6%': high - 0.786 * diff,
                        '100% (Low)': low
                    }

                    # กราฟ Fibonacci สวยงามมาก
                    plt.style.use('dark_background')
                    fig, ax = plt.subplots(figsize=(16, 9), dpi=150)
                    fig.patch.set_facecolor('#121212')
                    ax.set_facecolor('#121212')

                    ax.plot(df.index, df['c'], label='ราคาปิด (Close)', color='#00ffea', linewidth=3, alpha=0.9)

                    fib_colors = ['#ff1744', '#ff9100', '#ffd600', '#00e676', '#00e5ff', '#7c4dff', '#e0e0e0']
                    fib_labels = ['0.0% (High)', '23.6%', '38.2%', '50.0%', '61.8%', '78.6%', '100% (Low)']
                    for i, (label, level) in enumerate(fib_levels.items()):
                        ax.axhline(level, color=fib_colors[i], linestyle='--', linewidth=2.5, alpha=0.85)
                        ax.text(len(df)-1, level, f' {label}: {level:.6f} ', color=fib_colors[i], va='center', ha='right',
                                fontsize=11, bbox=dict(boxstyle="round,pad=0.5", facecolor='#121212', edgecolor=fib_colors[i], alpha=0.8))

                    ax.set_title(f'{sym_input} 4h Chart - Fibonacci Retracement', color='white', fontsize=20, pad=20)
                    ax.set_xlabel('แท่งเทียน (Candles)', color='white', fontsize=14)
                    ax.set_ylabel('ราคา (USDT)', color='white', fontsize=14)
                    ax.tick_params(colors='white', labelsize=10)
                    ax.grid(True, alpha=0.3, color='#424242', linestyle='-', linewidth=0.5)
                    ax.legend(facecolor='#121212', labelcolor='white', fontsize=12, loc='upper left')

                    plt.tight_layout()

                    buf = io.BytesIO()
                    fig.savefig(buf, format='png', bbox_inches='tight', facecolor=fig.get_facecolor(), edgecolor='none')
                    buf.seek(0)
                    photo = buf
                    plt.close(fig)

                    now_str = datetime.now().strftime("%d/%m/%Y %H:%M:%S")
                    report_text = (
                        f"📊 **วิเคราะห์ {sym_input} (4h)**\n"
                        f"ตรวจสอบเมื่อ: `{now_str}`\n"
                        f"ราคาปัจจุบัน: `{current_price:.6f}` USDT\n\n"
                        f"**Fibonacci Retracement Levels**\n"
                    )
                    for label, level in fib_levels.items():
                        report_text += f"• {label}: `{level:.6f}`\n"

                    report_text += (
                        f"\n**คำแนะนำการเทรด**\n"
                        f"หากราคาอยู่เหนือ 61.8% → แนวโน้มขาขึ้น แนะนำ LONG\n"
                        f"หากราคาอยู่ต่ำกว่า 38.2% → แนวโน้มขาลง แนะนำ SHORT\n"
                        f"รอ pullback ไปยังระดับ Fib ที่สำคัญก่อนเข้า"
                    )

                    await send_telegram_report(report_text, chat_id, photo=photo)

                except Exception as e:
                    await send_telegram_report(f"❌ เกิดข้อผิดพลาดในการวิเคราะห์: {str(e)}", chat_id)

            else:
                sym_input = text.upper()
                sym = sym_input + "USDT"
                if sym in price_map:
                    await send_telegram_report(f"💰 **{sym_input}**\nราคา: {price_map[sym]:,.6f} USDT", chat_id)
                else:
                    await send_telegram_report("❓ ไม่พบเหรียญนี้", chat_id)

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
#                               MAIN
# ==========================================================================
async def main():
    global bal, active, btc_p, pending_orders_detail, running, sym_info, sym_filters, top_50_symbols, last_volume_update
    global sl_tp_advice_notified, signal_features

    try:
        client = await AsyncClient.create(API_KEY, API_SECRET, testnet=USE_TESTNET)
        print(f"{Fore.GREEN}Connected to Binance {'Testnet' if USE_TESTNET else 'Mainnet'}!")
        
        acc = await client.futures_account()
        bal = float(acc['totalWalletBalance'])
        
        if telegram_bot:
            greeting = (
                "🚀 **TITAN PRO v31.3 เริ่มทำงานแล้ว! (Top 100 Volume)**\n"
                f"🕒 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                f"⚙️ โหมด: {'🧪 TESTNET' if USE_TESTNET else '🔴 LIVE'}\n"
                f"💰 Balance: {bal:,.2f} USDT\n"
                f"🔥 สแกนจาก Top 100 Volume อัปเดตทุก 4 ชม.\n\n"
                "📱 ควบคุมผ่าน Telegram ได้เต็มรูปแบบ!\n"
                "พิมพ์ `/help` เพื่อดูคำสั่ง\n"
                "_LFG!_ 🚀"
            )
            await send_telegram_report(greeting)

    except Exception as e:
        print(f"{Fore.RED}Connection Error: {e}")
        return

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

    try:
        print(f"{Fore.CYAN}Fetching initial Top 100 by 24h Volume...")
        tickers = await client.futures_ticker()
        volume_list = []
        for t in tickers:
            sym = t['symbol']
            if sym.endswith('USDT') and sym in sym_info:
                try:
                    vol = float(t['quoteVolume'])
                    volume_list.append((sym, vol))
                except:
                    pass
        volume_list.sort(key=lambda x: x[1], reverse=True)
        top_50_symbols = [s[0] for s in volume_list[:100]]
        last_volume_update = datetime.now()
        print(f"{Fore.GREEN}Loaded {len(top_50_symbols)} Top Volume symbols!")
        print(f"{Fore.YELLOW}Top 10: {', '.join(top_50_symbols[:10])}")
    except Exception as e:
        print(f"{Fore.RED}Failed to load initial Top 100: {e}")

    print(f"{Fore.CYAN}System Ready!")

    prev_active_symbols = set()

    while running:
        try:
            acc = await client.futures_account()
            bal = float(acc['totalWalletBalance'])
            pos_data = await client.futures_position_information()
            all_tickers = await client.futures_symbol_ticker()
            price_map = {t['symbol']: float(t['price']) for t in all_tickers}
            btc_p = price_map.get("BTCUSDT", 0.0)
            
            current_active_symbols = set()
            active = []
            active_symbols = set()
            for p in pos_data:
                amt = float(p['positionAmt'])
                if amt != 0:
                    sym = p['symbol']
                    active_symbols.add(sym)
                    current_active_symbols.add(sym)
                    entry = float(p['entryPrice'])
                    
                    orders = await client.futures_get_open_orders(symbol=sym)
                    
                    sl = 0.0
                    tp = 0.0
                    for o in orders:
                        if o['type'] == 'STOP_MARKET' and (o.get('reduceOnly', False) or o.get('closePosition', False)):
                            try:
                                sl = float(o['stopPrice'])
                                break
                            except: pass
                    for o in orders:
                        if o['type'] == 'TAKE_PROFIT_MARKET' and (o.get('reduceOnly', False) or o.get('closePosition', False)):
                            try:
                                tp = float(o['stopPrice'])
                                break
                            except: pass
                    
                    active.append({
                        'symbol': sym,
                        'side': 'LONG' if amt > 0 else 'SHORT',
                        'entry': entry,
                        'curr_price': price_map.get(sym, 0.0),
                        'pnl': float(p['unRealizedProfit']),
                        'amt': amt,
                        'margin': abs(amt * entry / MAX_LEVERAGE),
                        'sl': sl,
                        'tp': tp
                    })

            new_positions = current_active_symbols - prev_active_symbols
            closed_positions = prev_active_symbols - current_active_symbols

            for sym in closed_positions:
                f = signal_features.pop(sym, None)
                if f is not None:
                    try:
                        trades = await client.futures_account_trades(symbol=sym, limit=20)
                        # Find the last trade with realized PNL != 0 (close trade)
                        close_trades = [t for t in trades if float(t['realizedPnl']) != 0]
                        if close_trades:
                            pnl = float(close_trades[-1]['realizedPnl'])
                            is_win = pnl > 0
                            brain.update_memory(f, is_win)
                            print(f"{Fore.CYAN}AI Updated: {sym} {'Win' if is_win else 'Loss'} PNL {pnl}")
                            await send_telegram_report(f"🧠 AI Memory Updated\n{sym}: {'✅ Win' if is_win else '❌ Loss'}\nPNL: {pnl:.2f} USDT")
                    except Exception as e:
                        print(f"{Fore.RED}Error updating AI for {sym}: {e}")

            for sym in new_positions:
                pos = next(p for p in active if p['symbol'] == sym)
                side = pos['side']
                entry_price = pos['entry']
                current_price = pos['curr_price']
                qty = abs(pos['amt'])

                print(f"{Fore.CYAN}→ พบ Position ใหม่: {sym} {side} → ตั้ง SL/TP + แจ้งคำแนะนำ")

                try:
                    klines = await client.futures_klines(symbol=sym, interval="15m", limit=250)
                    df = calculate_indicators(klines)
                    if df.empty or len(df) < 30:
                        atr_val = entry_price * 0.02
                        long_score = 0
                        short_score = 0
                        curr = df.iloc[-1] if not df.empty else {'rsi':50, 'adx':25, 'macd':0, 'signal':0, 'atr':atr_val, 'c':current_price, 'ema200':current_price, 'v':1, 'vol_ma':1}
                    else:
                        atr_val = float(df.iloc[-1]['atr'])
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

                        short_score = 0
                        if curr['c'] < curr['ema200']: short_score += 1
                        if curr['ema20'] < curr['ema50']: short_score += 1
                        if curr['rsi'] < 50: short_score += 1
                        if curr['macd'] < curr['signal']: short_score += 1
                        if curr['c'] < curr['bb_lower']: short_score += 1
                        if curr['v'] > curr['vol_ma']: short_score += 1
                        if curr['c'] < curr['o']: short_score += 1
                        if curr['adx'] > ADX_THRESHOLD: short_score += 1

                except:
                    atr_val = entry_price * 0.02

                if side == 'LONG':
                    sl_price_raw = entry_price - (atr_val * ATR_SL_MULTIPLIER)
                    tp_price_raw = entry_price + (atr_val * ATR_TP_MULTIPLIER)
                else:
                    sl_price_raw = entry_price + (atr_val * ATR_SL_MULTIPLIER)
                    tp_price_raw = entry_price - (atr_val * ATR_TP_MULTIPLIER)

                tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                step_size = sym_filters.get(sym, {}).get('stepSize', 0.001)

                sl_price = round_to_tick(sl_price_raw, tick_size)
                tp_price = round_to_tick(tp_price_raw, tick_size)

                qty = math.floor(qty / step_size) * step_size if step_size > 0 else qty
                qty_precision = sym_info.get(sym, (4, 2))[1]
                qty_str = f"{qty:.{qty_precision}f}"

                price_precision = sym_info.get(sym, (4, 2))[0]
                sl_price_str = f"{sl_price:.{price_precision}f}"
                tp_price_str = f"{tp_price:.{price_precision}f}"
                current_price_str = f"{current_price:.{price_precision}f}"

                try:
                    await client.futures_create_order(
                        symbol=sym,
                        side=SIDE_SELL if side == 'LONG' else SIDE_BUY,
                        type='STOP_MARKET',
                        quantity=qty_str,
                        stopPrice=sl_price_str,
                        reduceOnly=True,
                        timeInForce=TIME_IN_FORCE_GTC,
                        workingType='MARK_PRICE'
                    )
                    pos['sl'] = sl_price
                except Exception as e:
                    print(f"{Fore.RED}ตั้ง SL ล้มเหลว {sym}: {e}")

                try:
                    await client.futures_create_order(
                        symbol=sym,
                        side=SIDE_SELL if side == 'LONG' else SIDE_BUY,
                        type='TAKE_PROFIT_MARKET',
                        quantity=qty_str,
                        stopPrice=tp_price_str,
                        reduceOnly=True,
                        timeInForce=TIME_IN_FORCE_GTC,
                        workingType='MARK_PRICE'
                    )
                    pos['tp'] = tp_price
                except Exception as e:
                    print(f"{Fore.RED}ตั้ง TP ล้มเหลว {sym}: {e}")

                score = long_score if side == 'LONG' else short_score
                f = [
                    float(curr['rsi'] / 100),
                    float(curr['adx'] / 100),
                    float((curr['macd'] - curr['signal']) / curr['atr'] if curr['atr'] > 0 else 0),
                    float((curr['c'] - curr['ema200']) / curr['ema200'] if curr['ema200'] > 0 else 0),
                    float(curr['v'] / curr['vol_ma'] if curr['vol_ma'] > 0 else 1),
                    float(score / 8.0),
                    1.0 if side == 'LONG' else 0.0
                ]
                signal_features[sym] = f

                now_str = datetime.now().strftime("%d/%m/%Y | %H:%M:%S")
                profit_10 = entry_price * 1.10 if side == 'LONG' else entry_price * 0.90
                profit_20 = entry_price * 1.20 if side == 'LONG' else entry_price * 0.80
                sl_wide_raw = entry_price - (atr_val * 5.0) if side == 'LONG' else entry_price + (atr_val * 5.0)
                sl_wide = round_to_tick(sl_wide_raw, tick_size)

                report = (
                    f"✅ **เข้า Position สำเร็จ + คำแนะนำ SL/TP!**\n"
                    f"วันที่: {now_str}\n"
                    f"เหรียญ: `{sym.replace('USDT','')}`\n"
                    f"ราคาปัจจุบัน: `{current_price_str}` USDT\n"
                    f"ทิศ: **{side}** | Entry: `{entry_price:.6f}` | จำนวน: `{qty_str}`\n\n"
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

            prev_active_symbols = current_active_symbols.copy()

            await cancel_old_pending_limits(client)

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
            
            pending_symbols = set(o['symbol'] for o in pending_orders_detail)

            print_dashboard(bal, active, pending_orders_detail, price_map, btc_p, scanning=True)

            if telegram_bot:
                await check_telegram_updates(client, cmd_q, price_map)

            while not cmd_q.empty() and running:
                cmd = await cmd_q.get()
                if cmd in ['qq', 'quit']:
                    running = False
                    await send_telegram_report("🛑 บอทหยุดทำงานเรียบร้อย")
                    print(f"{Fore.YELLOW}Shutdown command received. Stopping gracefully...")
                elif cmd in ['a', 'closeall']:
                    for p in active:
                        side = SIDE_SELL if p['side'] == 'LONG' else SIDE_BUY
                        try:
                            await client.futures_create_order(
                                symbol=p['symbol'],
                                side=side,
                                type='MARKET',
                                quantity=abs(p['amt']),
                                reduceOnly=True
                            )
                        except Exception as e:
                            print(f"{Fore.RED}Error closing {p['symbol']}: {e}")
                    try:
                        open_orders = await client.futures_get_open_orders()
                        for o in open_orders:
                            await client.futures_cancel_order(symbol=o['symbol'], orderId=o['orderId'])
                        await send_telegram_report("🔴 ปิดทุก Position และยกเลิก Orders ทั้งหมดแล้ว")
                    except Exception as e:
                        await send_telegram_report(f"❌ เกิดข้อผิดพลาดในการยกเลิก Orders: {e}")
                    print(f"{Fore.RED}All positions closed & all orders cancelled!")

                elif cmd in ['c', 'cancel']:
                    try:
                        open_orders = await client.futures_get_open_orders()
                        limit_orders = [o for o in open_orders if o['type'] == 'LIMIT']
                        if not limit_orders:
                            await send_telegram_report("ℹ️ ไม่มี Limit Orders ที่ต้องยกเลิก")
                        else:
                            for o in limit_orders:
                                await client.futures_cancel_order(symbol=o['symbol'], orderId=o['orderId'])
                            await send_telegram_report(f"🗑️ ยกเลิก Limit Orders ทั้งหมด {len(limit_orders)} รายการเรียบร้อย")
                            print(f"{Fore.YELLOW}Cancelled {len(limit_orders)} limit orders.")
                    except Exception as e:
                        await send_telegram_report(f"❌ เกิดข้อผิดพลาดในการยกเลิก: {e}")
                        print(f"{Fore.RED}Cancel error: {e}")

            if datetime.now() - last_volume_update > VOLUME_UPDATE_INTERVAL:
                try:
                    print(f"{Fore.CYAN}Updating Top 100 Volume...")
                    tickers = await client.futures_ticker()
                    volume_list = []
                    for t in tickers:
                        sym = t['symbol']
                        if sym.endswith('USDT') and sym in sym_info:
                            try:
                                vol = float(t['quoteVolume'])
                                volume_list.append((sym, vol))
                            except:
                                pass
                    volume_list.sort(key=lambda x: x[1], reverse=True)
                    top_50_symbols = [s[0] for s in volume_list[:100]]
                    last_volume_update = datetime.now()
                    print(f"{Fore.GREEN}Top 100 Updated! Top 5: {', '.join(top_50_symbols[:5])}")
                except Exception as e:
                    print(f"{Fore.RED}Update Top 100 failed: {e}")

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
                        if not running: break
                        if free_slots <= 0: break
                        if r['symbol'] in active_symbols or r['symbol'] in pending_symbols: continue
                        if r['ai'] < 50: continue  # Skip if AI confidence low

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

                            if r['side'] == 'LONG':
                                target_fib = max(fib_618, fib_50, fib_382)
                                limit_price_raw = max(current_p * (1 - (ENTRY_PULLBACK_PERCENT / 100)), target_fib)
                                side = SIDE_BUY
                            else:
                                target_fib = min(fib_382, fib_50, fib_618)
                                limit_price_raw = min(current_p * (1 + (ENTRY_PULLBACK_PERCENT / 100)), target_fib)
                                side = SIDE_SELL

                            tick_size = sym_filters.get(r['symbol'], {}).get('tickSize', 0.001)
                            limit_price = round_to_tick(limit_price_raw, tick_size)

                        except:
                            if r['side'] == 'LONG':
                                limit_price_raw = current_p * (1 - (ENTRY_PULLBACK_PERCENT / 100))
                                side = SIDE_BUY
                            else:
                                limit_price_raw = current_p * (1 + (ENTRY_PULLBACK_PERCENT / 100))
                                side = SIDE_SELL
                            tick_size = sym_filters.get(r['symbol'], {}).get('tickSize', 0.001)
                            limit_price = round_to_tick(limit_price_raw, tick_size)

                        p_prec, q_prec = sym_info.get(r['symbol'], (4, 2))
                        limit_price_str = f"{limit_price:.{p_prec}f}"

                        qty = calculate_position_size(bal, limit_price, r['atr'], r['symbol'], sym_filters, sym_info)
                        
                        if qty <= 0: continue

                        try:
                            await client.futures_change_leverage(symbol=r['symbol'], leverage=MAX_LEVERAGE)
                            
                            await client.futures_create_order(
                                symbol=r['symbol'],
                                side=side,
                                type='LIMIT',
                                timeInForce=TIME_IN_FORCE_GTC,
                                quantity=qty,
                                price=limit_price_str,
                                reduceOnly=False
                            )
                            
                            print(f"{Fore.YELLOW}⏳ Limit Placed (Fibonacci Optimized): {r['symbol']} {r['side']} @ {limit_price_str} (Qty: {qty})")
                            
                            await send_telegram_report(
                                f"⏳ **PENDING LIMIT (ปรับตาม Fibonacci)** #{r['symbol'].replace('USDT','')}\n"
                                f"Side: {r['side']}\n"
                                f"Limit: `{limit_price_str}`\n"
                                f"Pullback: {ENTRY_PULLBACK_PERCENT}% + Fib Support/Resistance\n"
                                f"Qty: {qty}")

                            pending_symbols.add(r['symbol'])
                            free_slots -= 1

                        except Exception as e:
                            print(f"{Fore.RED}Order error {r['symbol']}: {e}")

            await asyncio.sleep(2)

        except Exception as e:
            print(f"{Fore.RED}Main Loop Error: {e}")
            await asyncio.sleep(5)

    print(f"{Fore.YELLOW}Shutting down gracefully...")
    await client.close_connection()
    print(f"{Fore.GREEN}Bot stopped successfully. Goodbye!")

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print(f"\n{Fore.YELLOW}Bot stopped by user.")