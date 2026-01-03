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
running = True  # สำหรับ graceful shutdown
# เรียก init เพื่อให้ colorama ทำงานบน Windows ได้ดี
init(autoreset=True)

# Global variables ที่ต้องประกาศนอกฟังก์ชัน
prev_prices = {}
ticker_offset = 0
ticker_direction = 1  # 1 = เลื่อนไปทางซ้าย, -1 = เลื่อนไปทางขวา (จะสุ่มเปลี่ยนทิศบางครั้ง)

# ตัวแปรสถานะบอท (global เพื่อให้ Telegram เข้าถึงได้)
bal = 0.0
active = []
btc_p = 0.0
pending_orders_detail = []
sym_info = {}
sym_filters = {}
prev_active_symbols = set()  # <--- เพิ่มสำหรับตรวจจับ Position ใหม่

# เพิ่มตัวแปรสำหรับ Top 50 Volume
top_50_symbols = []
last_volume_update = datetime.min
VOLUME_UPDATE_INTERVAL = timedelta(hours=4)  # อัปเดตทุก 4 ชั่วโมง

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
#False
USE_TESTNET = True

MEMORY_FILE = "titan_memory.json"

# ==========================================================================
#                  OPTIMIZED CONFIG FOR $40 BALANCE
# ==========================================================================
MAX_LEVERAGE = 20  # ลดเหลือ 30x เพื่อความปลอดภัยกับทุนน้อย (ลด margin ใช้, ลด liquidation risk)
RISK_PER_TRADE_PERCENT = 0.025  # เสี่ยง 2.5% ต่อไม้ (จากเดิม 2% → เพิ่มนิดเพื่อให้เปิด position ได้ง่ายขึ้น)

MAX_OPEN_POSITIONS = 50
SIGNAL_THRESHOLD_LONG = 6
SIGNAL_THRESHOLD_SHORT = 7
ADX_THRESHOLD = 25
SCAN_BATCH_SIZE = 60
MIN_NOTIONAL_USDT = 5
MIN_BALANCE_TO_TRADE = 100.0  # ต้องมีอย่างน้อย $15 เพื่อเริ่มเทรด (ปลอดภัยกว่า)

# --- LIMIT ENTRY SETTINGS ---
ENTRY_PULLBACK_PERCENT = 3.8
LIMIT_ORDER_TIMEOUT_HOURS = 2

# SL/TP Settings
ATR_SL_MULTIPLIER = 3.0
ATR_TP_MULTIPLIER = 6.0  # RR 1:2

# ลบ MAJOR_SYMBOLS ออก เพราะใช้ Top 50 Volume แทน
# สำหรับ Major Ticker
MAJOR_TICKER_SYMBOLS  = [
    'BTCUSDT', 'ETHUSDT', 'SOLUSDT', 'BNBUSDT', 'XRPUSDT', 'ADAUSDT',
    'DOGEUSDT', 'AVAXUSDT', 'LINKUSDT', 'DOTUSDT', 'TRXUSDT', 'MATICUSDT',
    'LTCUSDT', 'BCHUSDT', 'NEARUSDT', 'UNIUSDT', 'SUIUSDT', 'APTUSDT']


prev_prices = {sym: 0.0 for sym in MAJOR_TICKER_SYMBOLS}  # เก็บราคาครั้งก่อนเพื่อหา up/down
ticker_offset = 0  # สำหรับเอฟเฟกต์ไหล
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
class TitanBrain:
    def __init__(self):
        self.memory = self.load_memory()
    
    def load_memory(self):
        try:
            if os.path.exists(MEMORY_FILE):
                with open(MEMORY_FILE, 'r') as f:
                    return json.load(f)
        except:
            pass
        return {"wins": [], "losses": []}

    def get_ai_confidence(self, f):
        return 50.0

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

        ai_conf = brain.get_ai_confidence({})
        atr_val = float(curr['atr'])
        curr_p = float(curr['c'])

        if long_score >= SIGNAL_THRESHOLD_LONG and short_score >= SIGNAL_THRESHOLD_SHORT:
            if long_score > short_score:
                return {"symbol": symbol, "side": "LONG", "score": long_score, "ai": ai_conf, "atr": atr_val, "curr_p": curr_p}
            elif short_score > long_score:
                return {"symbol": symbol, "side": "SHORT", "score": short_score, "ai": ai_conf, "atr": atr_val, "curr_p": curr_p}
            return None
        elif long_score >= SIGNAL_THRESHOLD_LONG:
            return {"symbol": symbol, "side": "LONG", "score": long_score, "ai": ai_conf, "atr": atr_val, "curr_p": curr_p}
        elif short_score >= SIGNAL_THRESHOLD_SHORT:
            return {"symbol": symbol, "side": "SHORT", "score": short_score, "ai": ai_conf, "atr": atr_val, "curr_p": curr_p}
        
        return None

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
#                     TELEGRAM HELPER
# ==========================================================================
async def send_telegram_report(text, chat_id=None):
    global telegram_bot, TELEGRAM_CHAT_ID
    if not telegram_bot: return
    target = chat_id or TELEGRAM_CHAT_ID
    if not target: return
    try:
        await telegram_bot.send_message(chat_id=target, text=text, parse_mode="Markdown")
    except TelegramError as e:
        print(f"{Fore.RED}Telegram send error: {e}")

# ==========================================================================
#                           DASHBOARD (อัปเดตเวลาแบบ Real-time + นับถอยหลังสวย)
# ==========================================================================
def print_dashboard(balance, active_positions, pending_orders, price_map, btc_price, scanning=False):
    global prev_prices, ticker_offset, ticker_direction
    
    os.system('cls' if os.name == 'nt' else 'clear')
    
    # --- Calculations ---
    total_pnl = sum(p['pnl'] for p in active_positions)
    pnl_color = Fore.GREEN if total_pnl >= 0 else Fore.RED
    bright_pnl = Style.BRIGHT if abs(total_pnl) > 100 else Style.NORMAL  # Pulse เมื่อ PNL มาก
    status_spinners = ["│", "/", "−", "\\"]
    spinner_idx = int(datetime.now().timestamp() * 8) % 4
    spinner = status_spinners[spinner_idx]
    status_str = f"{Fore.GREEN}{Style.BRIGHT}{spinner} SCANNING{Style.RESET_ALL}" if scanning else f"{Fore.LIGHTBLACK_EX}○ IDLE"
    mode_str = f"{Back.YELLOW}{Fore.BLACK}{Style.BRIGHT} 🧪 TESTNET {Style.RESET_ALL}" if USE_TESTNET else f"{Back.RED}{Fore.WHITE}{Style.BRIGHT} ⚡ LIVE {Style.RESET_ALL}"
    time_now = datetime.now().strftime('%H:%M:%S')

    # === PUK in LINE STYLE + CUTE CAT (Pulse Effect) ===
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

    # === MAJOR TICKER - REAL-TIME MARQUEE WITH RANDOM REVERSE ===
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
        
        # อัปเดต prev_prices
        prev_prices[sym] = curr_p
    
    full_ticker = "   │   ".join(ticker_parts) + "          "  # ช่องว่างเพิ่มเติม
    ticker_length = len(full_ticker.rstrip())  # ไม่นับช่องว่างท้ายสุด
    
    # สุ่มเปลี่ยนทิศทาง 5% โอกาสต่อการ refresh
    if random.random() < 0.05:
        ticker_direction *= -1
    
    # เลื่อน ticker (เร็วขึ้นนิดหน่อย)
    ticker_offset = (ticker_offset + ticker_direction * 2) % ticker_length
    if ticker_offset < 0:
        ticker_offset += ticker_length
    
    scrolling_ticker = full_ticker[ticker_offset:] + full_ticker[:ticker_offset]
    
    # พิมพ์ Ticker Bar
    print(f"{Back.BLACK}{Fore.WHITE}{Style.BRIGHT} " + scrolling_ticker.center(188) + Style.RESET_ALL)
    print(f"{Back.BLACK}{Fore.CYAN}╔" + "═" * 188 + "╗{Style.RESET_ALL}")

    # --- Header Section ---
    heartbeat = "❤️" if int(datetime.now().timestamp() * 1.5) % 2 == 0 else "🖤"
    print(f"{Back.BLACK}║ {mode_str}{Fore.CYAN} TITAN LIMIT SWING v31.3 {Fore.WHITE}│ {Fore.MAGENTA}📊 TOP 100 VOLUME {Fore.WHITE}│ 🕒 {Fore.WHITE}{time_now} {' ':<65}║{Style.RESET_ALL}{Fore.RED}{heartbeat}{Style.RESET_ALL}")
    print(f"{Back.BLACK}{Fore.CYAN}╠" + "═" * 188 + "╣{Style.RESET_ALL}")
    
    # --- Account Info ---
    balance_str = f"💰 BALANCE: {Fore.YELLOW}{Style.BRIGHT}{balance:,.2f}{Style.NORMAL} USDT"
    pnl_str = f"📈 TOTAL PNL: {bright_pnl}{pnl_color}{total_pnl:+,.2f}{Style.RESET_ALL} USDT"
    btc_str = f"₿ BTC PRICE: {Fore.YELLOW}{Style.BRIGHT}{btc_price:,.1f}{Style.NORMAL}"
    pending_str = f"⏳ PENDING: {Fore.MAGENTA}{len(pending_orders)}"
    active_str = f"⭐ POSITIONS: {Fore.CYAN}{len(active_positions)}/{MAX_OPEN_POSITIONS}"
    
    print(f"{Back.BLACK}║  {balance_str:<40} {pnl_str:<45} {btc_str:<35} {status_str:<25} {active_str}{pending_str.rjust(20)}  ║{Style.RESET_ALL}")
    print(f"{Back.BLACK}{Fore.CYAN}╚" + "═" * 188 + "╝{Style.RESET_ALL}\n")
    
    # --- Active Positions ---
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
            
            # SL Distance
            if p['sl'] > 0 and curr_price > 0:
                sl_dist = abs(curr_price - p['sl']) / curr_price * 100
                sl_alert = f"{Back.RED}{Fore.WHITE}{Style.BRIGHT} DANGER! {Style.RESET_ALL}" if sl_dist < 1.5 else ""
                sl_show = f"{sl_alert}{Fore.WHITE}{p['sl']:.6f} {Fore.RED}↓{sl_dist:.2f}%"
            else:
                sl_show = f"{Fore.RED}NO SL"
            
            # TP Distance
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

    # --- Pending Orders ---
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

    # --- Footer with Heartbeat ---
    heartbeat_footer = "❤️" if int(datetime.now().timestamp() * 1.5) % 2 == 0 else "🖤"
    print(f"\n{Fore.CYAN}╔{'═' * 186}╗")
    print(f"║ {Fore.WHITE}🎮 COMMANDS: {Fore.YELLOW}{Style.BRIGHT}[ID]{Style.NORMAL}{Fore.WHITE} Close │ "
          f"{Fore.YELLOW}{Style.BRIGHT}A{Style.NORMAL}{Fore.WHITE} Close All │ "
          f"{Fore.YELLOW}{Style.BRIGHT}C{Style.NORMAL}{Fore.WHITE} Cancel Limits │ "
          f"{Fore.RED}{Style.BRIGHT}Q{Style.NORMAL}{Fore.WHITE} Quit │ "
          f"{Fore.CYAN}📱 Telegram: /help /report /limits {heartbeat_footer.rjust(45)}║")
    print(f"╚{'═' * 186}╝{Style.RESET_ALL}")

# ==========================================================================
#                  ANALYZE TREND (4h timeframe)
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
#                  TELEGRAM COMMAND LISTENER
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
                    "🔍 `/analyze BTC` → วิเคราะห์แนวโน้ม 4h\n"
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
                    sym = text.split(' ', 1)[1].upper() + 'USDT'
                    analysis = await analyze_trend(client, sym)
                    await send_telegram_report(analysis, chat_id)
                except:
                    await send_telegram_report("❌ ใช้งาน: `/analyze BTC`", chat_id)

            else:
                sym_input = text.upper()
                sym = sym_input + "USDT"
                if sym in price_map:
                    current_price = price_map[sym]

                    # ดึง klines 4h
                    k = await client.futures_klines(symbol=sym, interval="4h", limit=100)
                    df = pd.DataFrame(k, columns=['ts', 'o', 'h', 'l', 'c', 'v', 'ct', 'qv', 'nt', 'tb', 'tq', 'i']).astype(float)
                    df['ts'] = pd.to_datetime(df['ts'], unit='ms')

                    # คำนวณ Fibonacci levels (ใช้ high/low ในช่วง 100 candles 4h ~16 วัน)
                    high = df['h'].max()
                    low = df['l'].min()
                    diff = high - low
                    fib_levels = {
                        '0% (High)': high,
                        '23.6%': high - 0.236 * diff,
                        '38.2%': high - 0.382 * diff,
                        '50%': high - 0.5 * diff,
                        '61.8%': high - 0.618 * diff,
                        '78.6%': high - 0.786 * diff,
                        '100% (Low)': low
                    }

                    # คำนวณแนวรับแนวต้านจาก Pivot Point (ใช้ last candle)
                    last_high = df['h'].iloc[-1]
                    last_low = df['l'].iloc[-1]
                    last_close = df['c'].iloc[-1]
                    pivot = (last_high + last_low + last_close) / 3
                    support1 = 2 * pivot - last_high
                    resistance1 = 2 * pivot - last_low
                    support2 = pivot - (last_high - last_low)
                    resistance2 = pivot + (last_high - last_low)

                    # สร้างกราฟ line chart (simple)
                    fig, ax = plt.subplots(figsize=(10, 6))
                    ax.plot(df['ts'], df['c'], label='Close Price', color='blue')

                    # เพิ่มเส้น Fibo dashed lines
                    for label, level in fib_levels.items():
                        ax.axhline(y=level, color='red', linestyle='--', label=f'{label}: {level:.6f}')

                    # เพิ่มแนวรับแนวต้าน
                    ax.axhline(y=support1, color='green', linestyle='-', label=f'S1: {support1:.6f}')
                    ax.axhline(y=resistance1, color='orange', linestyle='-', label=f'R1: {resistance1:.6f}')
                    ax.axhline(y=support2, color='darkgreen', linestyle='-', label=f'S2: {support2:.6f}')
                    ax.axhline(y=resistance2, color='darkorange', linestyle='-', label=f'R2: {resistance2:.6f}')

                    ax.legend(loc='upper left', bbox_to_anchor=(1, 1))
                    ax.set_title(f"{sym_input} 4h Chart with Fibonacci & S/R Levels")
                    ax.set_xlabel('Time')
                    ax.set_ylabel('Price')
                    plt.tight_layout()

                    # บันทึกกราฟเป็น bytes
                    buf = io.BytesIO()
                    fig.savefig(buf, format='png')
                    buf.seek(0)

                    # ส่งข้อความราคา + Fibo + S/R
                    report = f"💰 **{sym_input}**\nราคาปัจจุบัน: {current_price:,.6f} USDT\n\n**Fibonacci Levels (จาก High/Low 4h ล่าสุด):**"
                    for label, level in fib_levels.items():
                        report += f"\n{label}: {level:.6f}"

                    report += f"\n\n**แนวรับ/แนวต้าน (Pivot Point 4h ล่าสุด):**\nS1: {support1:.6f}\nS2: {support2:.6f}\nR1: {resistance1:.6f}\nR2: {resistance2:.6f}"

                    await telegram_bot.send_message(chat_id=chat_id, text=report, parse_mode="Markdown")

                    # ส่งรูปกราฟ
                    await telegram_bot.send_photo(chat_id=chat_id, photo=buf)

                    buf.close()
                    plt.close(fig)

                else:
                    await send_telegram_report("❓ ไม่พบเหรียญนี้", chat_id)

    except Exception as e:
        print(f"{Fore.RED}Telegram polling error: {e}")

# ==========================================================================
#                               MAIN
# ==========================================================================
async def main():
    global bal, active, btc_p, pending_orders_detail, running, sym_info, sym_filters
    global top_50_symbols, last_volume_update

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

    # ดึง Top 50 Volume ครั้งแรก
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

    while running:
        try:
            acc = await client.futures_account()
            bal = float(acc['totalWalletBalance'])
            pos_data = await client.futures_position_information()
            all_tickers = await client.futures_symbol_ticker()
            price_map = {t['symbol']: float(t['price']) for t in all_tickers}
            btc_p = price_map.get("BTCUSDT", 0.0)
            
            active = []
            active_symbols = set()
            for p in pos_data:
                amt = float(p['positionAmt'])
                if amt != 0:
                    sym = p['symbol']
                    active_symbols.add(sym)
                    entry = float(p['entryPrice'])
                    
                    orders = await client.futures_get_open_orders(symbol=sym)
                    
                    sl = 0.0
                    for o in orders:
                        if o['type'] == 'STOP_MARKET' and o.get('closePosition', False):
                            try:
                                sl = float(o['stopPrice'])
                                break
                            except:
                                pass
                    
                    tp = 0.0
                    for o in orders:
                        if o['type'] == 'TAKE_PROFIT_MARKET' and o.get('closePosition', False):
                            try:
                                tp = float(o['stopPrice'])
                                break
                            except:
                                pass
                    
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

            # === ตั้ง SL/TP อัตโนมัติให้ทุก Position ที่ยังไม่มี SL หรือ TP (ทั้งใหม่และเก่า) ===
            positions_needing_protection = [
                p for p in active 
                if p['sl'] == 0.0 or p['tp'] == 0.0  # ยังไม่มี SL หรือไม่มี TP
            ]

            if positions_needing_protection:
                print(f"{Fore.CYAN}🛡️ พบ {len(positions_needing_protection)} Position ที่ยังไม่มี SL/TP → กำลังตั้งอัตโนมัติ...")
            for pos in positions_needing_protection:
                sym = pos['symbol']
                side = pos['side']
                entry_price = pos['entry']
                qty = abs(pos['amt'])

                # ข้ามถ้ามีทั้ง SL และ TP แล้ว
                if pos['sl'] > 0 and pos['tp'] > 0:
                    continue

                print(f"{Fore.CYAN}→ กำลังตั้ง SL/TP ให้ {sym} {side} (Entry: {entry_price:.6f})")

                try:
                    klines = await client.futures_klines(symbol=sym, interval="15m", limit=100)
                    df = calculate_indicators(klines)
                    if df.empty or len(df) < 50:
                        print(f"{Fore.YELLOW}ข้อมูลไม่พอสำหรับ {sym} → ข้ามการตั้ง SL/TP")
                        continue

                    atr_val = float(df.iloc[-1]['atr'])
                    if atr_val <= 0:
                        print(f"{Fore.YELLOW}ATR = 0 สำหรับ {sym} → ข้าม")
                        continue

                except Exception as e:
                    print(f"{Fore.RED}ดึง ATR ล้มเหลว {sym}: {e}")
                    continue

                # คำนวณ SL และ TP
                if side == 'LONG':
                    sl_price_raw = entry_price - (atr_val * ATR_SL_MULTIPLIER)
                    tp_price_raw = entry_price + (atr_val * ATR_TP_MULTIPLIER)
                    sl_side = SIDE_SELL
                    tp_side = SIDE_SELL
                else:  # SHORT
                    sl_price_raw = entry_price + (atr_val * ATR_SL_MULTIPLIER)
                    tp_price_raw = entry_price - (atr_val * ATR_TP_MULTIPLIER)
                    sl_side = SIDE_BUY
                    tp_side = SIDE_BUY

                tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                sl_price = round_to_tick(sl_price_raw, tick_size)
                tp_price = round_to_tick(tp_price_raw, tick_size)

                if sl_price <= 0 or tp_price <= 0:
                    print(f"{Fore.RED}ราคา SL/TP ไม่ถูกต้อง → ข้าม {sym}")
                    continue

                price_precision = sym_info.get(sym, (4, 2))[0]
                sl_price_str = f"{sl_price:.{price_precision}f}"
                tp_price_str = f"{tp_price:.{price_precision}f}"

                success_sl = pos['sl'] > 0  # ถ้ามีอยู่แล้ว = True
                success_tp = pos['tp'] > 0

                # ตั้ง SL เฉพาะเมื่อยังไม่มี
                if not success_sl:
                    try:
                        await client.futures_create_order(
                            symbol=sym,
                            side=sl_side,
                            type='STOP_MARKET',
                            stopPrice=sl_price_str,
                            closePosition=True,
                            timeInForce=TIME_IN_FORCE_GTC
                        )
                        success_sl = True
                        pos['sl'] = sl_price
                        print(f"{Fore.GREEN}✅ ตั้ง SL สำเร็จ: {sym} @ {sl_price_str}")
                    except BinanceAPIException as e:
                        if "Order would immediately trigger" in str(e):
                            print(f"{Fore.RED}⚠️ SL ใกล้เกินไป จะทริกเกอร์ทันที → ข้าม SL {sym}")
                        else:
                            print(f"{Fore.RED}ตั้ง SL ล้มเหลว {sym}: {e}")
                    except Exception as e:
                        print(f"{Fore.RED}ตั้ง SL ล้มเหลว {sym}: {e}")

                # ตั้ง TP เฉพาะเมื่อยังไม่มี
                if not success_tp:
                    try:
                        await client.futures_create_order(
                            symbol=sym,
                            side=tp_side,
                            type='TAKE_PROFIT_MARKET',
                            stopPrice=tp_price_str,
                            closePosition=True,
                            timeInForce=TIME_IN_FORCE_GTC
                        )
                        success_tp = True
                        pos['tp'] = tp_price
                        print(f"{Fore.GREEN}✅ ตั้ง TP สำเร็จ: {sym} @ {tp_price_str}")
                    except BinanceAPIException as e:
                        if "Order would immediately trigger" in str(e):
                            print(f"{Fore.YELLOW}⚠️ TP ถึงเป้าแล้วหรือใกล้เกินไป → ข้าม TP {sym}")
                        else:
                            print(f"{Fore.RED}ตั้ง TP ล้มเหลว {sym}: {e}")
                    except Exception as e:
                        print(f"{Fore.RED}ตั้ง TP ล้มเหลว {sym}: {e}")

                # ส่งแจ้งเตือน Telegram ถ้าตั้งสำเร็จอย่างน้อยหนึ่งอย่าง
                if success_sl or success_tp:
                    rr_ratio = f"1:{ATR_TP_MULTIPLIER / ATR_SL_MULTIPLIER:.1f}"
                    status = "🟢 ปกป้องแล้ว" if (success_sl and success_tp) else "🟡 ปกป้องบางส่วน"
                    report = (
                        f"{status} **ตั้ง SL/TP อัตโนมัติ**\n"
                        f"เหรียญ: `{sym.replace('USDT', '')}`\n"
                        f"ทิศ: **{side}**\n"
                        f"Entry: `{entry_price:.6f}`\n"
                        f"{'SL: `' + sl_price_str + '`' if success_sl else 'SL: ไม่มี/ล้มเหลว'}\n"
                        f"{'TP: `' + tp_price_str + '` (RR 1:2)' if success_tp else 'TP: ไม่มี/ล้มเหลว'}\n"
                        f"ATR × {ATR_SL_MULTIPLIER}/{ATR_TP_MULTIPLIER} → RR {rr_ratio}\n"
                        f"จำนวน: `{qty:.4f}`"
                    )
                    await send_telegram_report(report)
                else:
                    await send_telegram_report(
                        f"⚠️ **ไม่สามารถตั้ง SL/TP ได้** สำหรับ `{sym.replace('USDT', '')}` {side}\n"
                        f"กรุณาตรวจสอบและตั้งด้วยตนเอง!"
                    )

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
                    # ... (โค้ด close all เดิม)
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
                    # ... (โค้ด cancel เดิม)
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

            # อัปเดต Top 50 Volume ทุก 4 ชม.
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

                        p_prec, q_prec = sym_info.get(r['symbol'], (4, 2))
                        tick_size = sym_filters.get(r['symbol'], {}).get('tickSize', 0.001)
                        current_p = r['curr_p']

                        if r['side'] == 'LONG':
                            limit_price_raw = current_p * (1 - (ENTRY_PULLBACK_PERCENT / 100))
                            side = SIDE_BUY
                        else:
                            limit_price_raw = current_p * (1 + (ENTRY_PULLBACK_PERCENT / 100))
                            side = SIDE_SELL
                            
                        limit_price = round_to_tick(limit_price_raw, tick_size)
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
                            
                            print(f"{Fore.YELLOW}⏳ Limit Placed: {r['symbol']} {r['side']} @ {limit_price_str} (Qty: {qty})")
                            
                            await send_telegram_report(
                                f"⏳ **PENDING LIMIT** #{r['symbol'].replace('USDT','')}\nSide: {r['side']}\nLimit: `{limit_price_str}`\nPullback: {ENTRY_PULLBACK_PERCENT}%\nQty: {qty}")

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