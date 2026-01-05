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

# ตัวแปรสถานะบอท (global เพื่อให้ Telegram เข้าถึงได้)
bal = 0.0
active = []
btc_p = 0.0
pending_orders_detail = []
sym_info = {}
sym_filters = {}
prev_active_symbols = set()  # <--- เพิ่มสำหรับตรวจจับ Position ใหม่

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

USE_TESTNET = False

MEMORY_FILE = "titan_memory.json"
# ==========================================================================
#                         OPTIMIZED CONFIG FOR $30
# ==========================================================================
MAX_LEVERAGE = 50
RISK_PER_TRADE_PERCENT = 0.02  # เสี่ยง 1% ต่อไม้

MAX_OPEN_POSITIONS = 3
SIGNAL_THRESHOLD_LONG = 6
SIGNAL_THRESHOLD_SHORT = 7
ADX_THRESHOLD = 25
SCAN_BATCH_SIZE = 60
MIN_NOTIONAL_USDT = 5
MIN_BALANCE_TO_TRADE = 10.0

# --- LIMIT ENTRY SETTINGS ---
ENTRY_PULLBACK_PERCENT =5.8
LIMIT_ORDER_TIMEOUT_HOURS = 2

# SL/TP Settings
ATR_SL_MULTIPLIER = 3.0
ATR_TP_MULTIPLIER = 6.0  # RR 1:2

MAJOR_SYMBOLS = {
    'BTCUSDT', 'ETHUSDT', 'SOLUSDT', 'BNBUSDT', 'XRPUSDT', 'ADAUSDT',
    'DOGEUSDT', 'AVAXUSDT', 'LINKUSDT', 'DOTUSDT', 'TRXUSDT', 'MATICUSDT',
    'LTCUSDT', 'BCHUSDT', 'NEARUSDT', 'UNIUSDT', 'SUIUSDT', 'APTUSDT'
}

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
#                           DASHBOARD
# ==========================================================================
def print_dashboard(balance, active_positions, pending_orders, price_map, btc_price, scanning=False):
    os.system('cls' if os.name == 'nt' else 'clear')
    
    total_pnl = sum(p['pnl'] for p in active_positions)
    pnl_color = Fore.GREEN if total_pnl >= 0 else Fore.RED
    status_str = f"{Fore.GREEN}SCANNING..." if scanning else f"{Fore.LIGHTBLACK_EX}IDLE"
    mode_str = f"{Back.YELLOW}{Fore.BLACK} TESTNET " if USE_TESTNET else f"{Back.RED}{Fore.WHITE} LIVE "

    print(f"{Fore.CYAN}{'='*190}")
    print(f" {mode_str} TITAN LIMIT SWING v31.2 | {Fore.CYAN}{datetime.now().strftime('%H:%M:%S')}")
    print(f" {Fore.WHITE} BALANCE: {Fore.YELLOW}{balance:,.2f} USDT | PNL: {pnl_color}{total_pnl:+,.2f} USDT | BTC: {Fore.YELLOW}{btc_price:,.0f}")
    print(f" {Fore.WHITE} STATUS: {status_str} | Pending Orders: {Fore.MAGENTA}{len(pending_orders)} | Pullback: {ENTRY_PULLBACK_PERCENT}%")
    print(f"{Fore.CYAN}{'='*190}")
    
    if active_positions:
        print(f"{'ID':<4} {'SYMBOL':<10} {'SIDE':<6} {'ENTRY':<12} {'PRICE':<12} {'PNL':<14} {'ROE%':<8} {'SL':<18} {'TP':<18}")
        print(f"{Fore.LIGHTBLACK_EX}{'-'*190}")
        
        for i, p in enumerate(active_positions, 1):
            sl_val = p['sl']
            tp_val = p['tp']
            curr_price = p['curr_price']
            
            # คำนวณ % ระยะทางไป SL
            if sl_val > 0 and curr_price > 0:
                if p['side'] == 'LONG':
                    sl_percent = ((sl_val - curr_price) / curr_price) * 100
                else:  # SHORT
                    sl_percent = ((curr_price - sl_val) / curr_price) * 100
                sl_percent_str = f"{sl_percent:+.2f}%"
                sl_color = Fore.RED if sl_percent < 0 else Fore.GREEN
                if abs(sl_percent) < 1.0 and sl_percent < 0:
                    sl_show = f"{Fore.RED}{Back.YELLOW}{sl_val:.4f} ({sl_percent:+.2f}%) DANGER!{Style.RESET_ALL}"
                else:
                    sl_show = f"{sl_val:.4f} ({sl_color}{sl_percent_str}{Fore.LIGHTBLACK_EX})"
            else:
                sl_show = f"{Fore.RED}NO SL"
            
            # คำนวณ % ระยะทางไป TP
            if tp_val > 0 and curr_price > 0:
                if p['side'] == 'LONG':
                    tp_percent = ((tp_val - curr_price) / curr_price) * 100
                else:  # SHORT
                    tp_percent = ((curr_price - tp_val) / curr_price) * 100
                tp_percent_str = f"{tp_percent:+.2f}%"
                tp_color = Fore.GREEN if abs(tp_percent) <= 1.0 else Fore.LIGHTBLACK_EX
                tp_show = f"{tp_val:.4f} ({tp_color}{tp_percent_str}{Fore.LIGHTBLACK_EX})"
            else:
                tp_show = f"{Fore.RED}NO TP"
            
            sc_color = Fore.GREEN if p['side']=='LONG' else Fore.RED
            pc = Fore.GREEN if p['pnl']>=0 else Fore.RED
            roe = (p['pnl']/p['margin']*100) if p['margin']>0 else 0
            
            row = (
                f"{Fore.YELLOW}{i:<4} "
                f"{Fore.WHITE}{p['symbol'].replace('USDT',''):<10} "
                f"{sc_color}{p['side']:<6}{Fore.WHITE} "
                f"{p['entry']:<12.4f} "
                f"{Fore.CYAN}{curr_price:<12.4f} "
                f"{pc}{p['pnl']:<+14.2f}{Fore.WHITE} "
                f"{pc}{roe:>+8.1f}%{Fore.WHITE} "
                f"{Fore.LIGHTBLACK_EX}{sl_show:<18} "
                f"{Fore.LIGHTBLACK_EX}{tp_show:<18} "
            )
            print(row)
    else:
        print(f"{Fore.LIGHTBLACK_EX}  [No filled positions... Waiting for limits to hit]")
    
    print(f"{Fore.CYAN}{'='*190}")
    
    if pending_orders:
        print(f"{'NO':<4} {'SYMBOL':<10} {'SIDE':<6} {'CURRENT':<12} {'LIMIT':<12} {'DIFF $':<12} {'DIFF %':<10} {'QTY':<12} {'AGE (H)':<10} {'ORDER ID':<15}")
        print(f"{Fore.LIGHTBLACK_EX}{'-'*190}")
        
        sorted_pending = sorted(pending_orders, key=lambda x: x['time'])
        
        for i, o in enumerate(sorted_pending, 1):
            sym = o['symbol']
            current_price = price_map.get(sym, 0.0)
            limit_price = o['price']
            side_multiplier = -1 if o['side'] == 'BUY' else 1
            price_diff = (limit_price - current_price) * side_multiplier
            percent_diff = (price_diff / current_price * 100) if current_price > 0 else 0.0
            
            diff_color = Fore.GREEN if percent_diff > 0 else Fore.RED
            age_hours = (datetime.now() - o['time']).total_seconds() / 3600
            age_str = f"{age_hours:.1f}h"
            if age_hours > LIMIT_ORDER_TIMEOUT_HOURS:
                age_str = f"{Fore.RED}{age_str} (Old!)"
            
            side_color = Fore.GREEN if o['side'] == 'BUY' else Fore.RED
            
            row = (
                f"{Fore.YELLOW}{i:<4} "
                f"{Fore.WHITE}{sym.replace('USDT',''):<10} "
                f"{side_color}{o['side']:<6}{Fore.WHITE} "
                f"{Fore.CYAN}{current_price:<12.4f}{Fore.WHITE} "
                f"{limit_price:<12.4f} "
                f"{diff_color}{price_diff:+.4f}{Fore.WHITE:<12} "
                f"{diff_color}{percent_diff:+.2f}%{Fore.WHITE:<10} "
                f"{o['qty']:<12.4f} "
                f"{age_str:<10} "
                f"{Fore.LIGHTBLACK_EX}{o['orderId']:<15} "
            )
            print(row)
    else:
        print(f"{Fore.LIGHTBLACK_EX}  [No pending limit orders]")

    print(f"{Fore.CYAN}{'='*190}")
    print(f"{Fore.WHITE} Commands: [ID] Close | a Close All | c Cancel All | q Quit | Telegram: /help /report /limits /analyze")

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
                    await send_telegram_report(f"💰 **{sym_input}**\nราคา: {price_map[sym]:,.6f} USDT", chat_id)
                else:
                    await send_telegram_report("❓ ไม่พบเหรียญนี้", chat_id)

    except Exception as e:
        print(f"{Fore.RED}Telegram polling error: {e}")

# ==========================================================================
#                               MAIN
# ==========================================================================
async def main():
    global bal, active, btc_p, pending_orders_detail, running, sym_info, sym_filters, prev_active_symbols

    try:
        client = await AsyncClient.create(API_KEY, API_SECRET, testnet=USE_TESTNET)
        print(f"{Fore.GREEN}Connected to Binance {'Testnet' if USE_TESTNET else 'Mainnet'}!")
        
        acc = await client.futures_account()
        bal = float(acc['totalWalletBalance'])
        
        if telegram_bot:
            greeting = (
                "🚀 **TITAN PRO v31.2 เริ่มทำงานแล้ว!**\n"
                f"🕒 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                f"⚙️ โหมด: {'🧪 TESTNET' if USE_TESTNET else '🔴 LIVE'}\n"
                f"💰 Balance: {bal:,.2f} USDT\n\n"
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
        if s['symbol'].endswith('USDT') and s['status'] == 'TRADING':
            sym = s['symbol']
            sym_info[sym] = (s['pricePrecision'], s['quantityPrecision'])
            tick = step = 0.0
            for f in s['filters']:
                if f['filterType'] == 'PRICE_FILTER':
                    tick = float(f['tickSize'])
                elif f['filterType'] == 'LOT_SIZE':
                    step = float(f['stepSize'])
            sym_filters[sym] = {'tickSize': tick, 'stepSize': step}

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
                    
                    # ดึง SL และ TP จาก open orders
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

            # ==========================================================================
            #           AUTO SET STOP LOSS & TAKE PROFIT WHEN NEW POSITION FILLED
            # ==========================================================================
            current_active_symbols = {p['symbol'] for p in active}
            
            new_positions = [
                p for p in active
                if p['symbol'] not in prev_active_symbols and p['sl'] == 0.0
            ]
            
            for pos in new_positions:
                sym = pos['symbol']
                side = pos['side']
                entry_price = pos['entry']
                qty = abs(pos['amt'])
                
                try:
                    klines = await client.futures_klines(symbol=sym, interval="15m", limit=100)
                    df = calculate_indicators(klines)
                    if df.empty:
                        print(f"{Fore.YELLOW}ไม่พบข้อมูล ATR สำหรับ {sym} - ข้ามการตั้ง SL/TP")
                        continue
                    atr_val = float(df.iloc[-1]['atr'])
                except Exception as e:
                    print(f"{Fore.RED}ดึง ATR ล้มเหลว {sym}: {e}")
                    continue
                
                if atr_val <= 0:
                    print(f"{Fore.YELLOW}ATR = 0 สำหรับ {sym} - ข้ามการตั้ง SL/TP")
                    continue
                
                if side == 'LONG':
                    sl_price_raw = entry_price - (atr_val * ATR_SL_MULTIPLIER)
                    tp_price_raw = entry_price + (atr_val * ATR_TP_MULTIPLIER)
                    sl_side = SIDE_SELL
                    tp_side = SIDE_SELL
                else:
                    sl_price_raw = entry_price + (atr_val * ATR_SL_MULTIPLIER)
                    tp_price_raw = entry_price - (atr_val * ATR_TP_MULTIPLIER)
                    sl_side = SIDE_BUY
                    tp_side = SIDE_BUY
                
                tick_size = sym_filters.get(sym, {}).get('tickSize', 0.0001)
                sl_price = round_to_tick(sl_price_raw, tick_size)
                tp_price = round_to_tick(tp_price_raw, tick_size)
                
                if sl_price <= 0 or tp_price <= 0:
                    continue
                
                price_precision = sym_info.get(sym, (4, 2))[0]
                sl_price_str = f"{sl_price:.{price_precision}f}"
                tp_price_str = f"{tp_price:.{price_precision}f}"
                
                success_sl = False
                success_tp = False
                
                try:
                    await client.futures_create_order(
                        symbol=sym,
                        side=sl_side,
                        type='STOP_MARKET',
                        stopPrice=sl_price_str,
                        closePosition=True,
                        reduceOnly=True
                    )
                    success_sl = True
                    print(f"{Fore.GREEN}✅ ตั้ง SL อัตโนมัติ: {sym} {side} @ {sl_price}")
                except Exception as e:
                    print(f"{Fore.RED}ตั้ง SL ล้มเหลว {sym}: {e}")
                
                try:
                    await client.futures_create_order(
                        symbol=sym,
                        side=tp_side,
                        type='TAKE_PROFIT_MARKET',
                        stopPrice=tp_price_str,
                        closePosition=True,
                        reduceOnly=True
                    )
                    success_tp = True
                    print(f"{Fore.GREEN}✅ ตั้ง TP อัตโนมัติ: {sym} {side} @ {tp_price}")
                except Exception as e:
                    print(f"{Fore.RED}ตั้ง TP ล้มเหลว {sym}: {e}")
                
                if success_sl or success_tp:
                    report_lines = [
                        f"🛡️ **ตั้ง SL/TP อัตโนมัติสำเร็จ!**",
                        f"เหรียญ: {sym.replace('USDT','')}",
                        f"ทิศ: {side}",
                        f"Entry: {entry_price:.4f}",
                        f"{'SL: ' + str(sl_price) if success_sl else '❌ SL ล้มเหลว'}",
                        f"{'TP: ' + str(tp_price) + ' (RR 1:2)' if success_tp else '❌ TP ล้มเหลว'}",
                        f"ระยะ: SL {ATR_SL_MULTIPLIER}x | TP {ATR_TP_MULTIPLIER}x ATR",
                        f"จำนวน: {qty:.4f}"
                    ]
                    await send_telegram_report("\n".join(report_lines))
                    
                    pos['sl'] = sl_price
            
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

            total_active_trade_intent = len(active_symbols) + len(pending_symbols)
            free_slots = MAX_OPEN_POSITIONS - total_active_trade_intent

            if free_slots > 0 and bal >= MIN_BALANCE_TO_TRADE:
                potential = [s for s in MAJOR_SYMBOLS if s in sym_info and s not in active_symbols and s not in pending_symbols]
                
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
                                f"⏳ **PENDING LIMIT** #{r['symbol']}\nSide: {r['side']}\nLimit: `{limit_price_str}`\nPullback: {ENTRY_PULLBACK_PERCENT}%\nQty: {qty}")

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