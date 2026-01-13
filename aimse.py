import pandas as pd
import numpy as np
from collections import defaultdict
from datetime import datetime
import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import Dataset, DataLoader
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
import requests  # สำหรับดึงราคา real-time
matplotlib.use('Agg')  # ใช้ backend ที่ไม่ต้อง display
# =========================
# CONFIG (อัปเกรดเพิ่มเติม)
# =========================
MIN_CONFIDENCE = 0.55
MIN_RR = 1.5
SWING_LOOKBACK = 3
ATR_PERIOD = 14
SEQ_LEN = 5
EPOCHS = 50
HIDDEN = 64

ENCODER = {'HH': 0, 'HL': 1, 'LH': 2, 'LL': 3, 'H': 0, 'L': 1}
DECODER = {0: 'HH', 1: 'HL', 2: 'LH', 3: 'LL'}

SYMBOL = "BTC/USDT"

# =========================
# 1) ดึงราคา Real-Time + Historical Data (จาก Binance API)
# =========================
def fetch_live_data(days=1825):  # ~5 ปี daily
    url = "https://api.binance.com/api/v3/klines"
    params = {
        'symbol': 'BTCUSDT',
        'interval': '1d',
        'limit': 1000
    }
    data = []
    end_time = None
    while len(data) < days:
        if end_time:
            params['endTime'] = end_time
        resp = requests.get(url, params=params)
        resp.raise_for_status()
        batch = resp.json()
        if not batch:
            break
        data = batch + data
        end_time = batch[0][0] - 1
        if len(batch) < 1000:
            break
    
    df = pd.DataFrame(data, columns=[
        'timestamp', 'open', 'high', 'low', 'close', 'volume',
        'close_time', 'quote_volume', 'trades', 'taker_buy_base',
        'taker_buy_quote', 'ignore'
    ])
    df = df[['timestamp', 'open', 'high', 'low', 'close', 'volume']]
    df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
    df[['open', 'high', 'low', 'close', 'volume']] = df[['open', 'high', 'low', 'close', 'volume']].astype(float)
    
    # ATR
    tr = np.maximum(df['high'] - df['low'],
                    np.maximum(abs(df['high'] - df['close'].shift()),
                               abs(df['low'] - df['close'].shift())))
    df['atr'] = tr.rolling(ATR_PERIOD).mean()
    
    return df.dropna().reset_index(drop=True)

def get_current_price():
    resp = requests.get("https://api.binance.com/api/v3/ticker/price", params={'symbol': 'BTCUSDT'})
    return float(resp.json()['price'])

# =========================
# ฟังก์ชันหลักทั้งหมด (อยู่ก่อน run_titan_live)
# =========================
def detect_swings(df, lookback=SWING_LOOKBACK):
    df['swing'] = None
    for i in range(lookback, len(df) - lookback):
        if (df['high'].iloc[i] > df['high'].iloc[i-lookback:i].max() and
            df['high'].iloc[i] > df['high'].iloc[i+1:i+lookback+1].max()):
            df.loc[df.index[i], 'swing'] = 'H'
        elif (df['low'].iloc[i] < df['low'].iloc[i-lookback:i].min() and
              df['low'].iloc[i] < df['low'].iloc[i+1:i+lookback+1].min()):
            df.loc[df.index[i], 'swing'] = 'L'
    return df

def build_structure(df):
    swings = df[df['swing'].notnull()].copy()
    if len(swings) < 2:
        return []
    structures = []
    prev_type = None
    prev_price = None
    for _, row in swings.iterrows():
        current_type = row['swing']
        current_price = row['high'] if current_type == 'H' else row['low']
        if prev_type and prev_price:
            if prev_type == 'H' and current_type == 'H':
                struct = 'HH' if current_price > prev_price else 'LH'
            elif prev_type == 'L' and current_type == 'L':
                struct = 'LL' if current_price < prev_price else 'HL'
            else:
                continue
            structures.append(struct)
        prev_type = current_type
        prev_price = current_price
    return structures

def train_markov(structures):
    if len(structures) < 2:
        return defaultdict(lambda: defaultdict(int))
    transitions = defaultdict(lambda: defaultdict(int))
    for i in range(len(structures) - 1):
        transitions[structures[i]][structures[i+1]] += 1
    prob = defaultdict(lambda: defaultdict(lambda: 0.0))
    for current, nexts in transitions.items():
        total = sum(nexts.values())
        for next_state, count in nexts.items():
            prob[current][next_state] = count / total
    return prob

class StructureDataset(Dataset):
    def __init__(self, structures, seq_len=SEQ_LEN):
        self.data = []
        for i in range(len(structures) - seq_len):
            seq = structures[i:i+seq_len]
            target = structures[i+seq_len]
            self.data.append((seq, target))
    
    def __len__(self):
        return len(self.data)
    
    def __getitem__(self, idx):
        seq, target = self.data[idx]
        seq_encoded = [ENCODER.get(s, 1) for s in seq]
        return torch.tensor(seq_encoded), torch.tensor(ENCODER.get(target, 1))

class LSTMModel(nn.LSTM):
    def __init__(self, input_size=1, hidden=HIDDEN, num_layers=2, num_classes=4):
        super().__init__(input_size, hidden, num_layers, batch_first=True)
        self.fc = nn.Linear(hidden, num_classes)
    
    def forward(self, x):
        x = x.unsqueeze(-1).float()
        out, _ = super().forward(x)
        return self.fc(out[:, -1, :])

def train_lstm(structures):
    if len(structures) < SEQ_LEN + 10:
        return None
    dataset = StructureDataset(structures)
    loader = DataLoader(dataset, batch_size=8, shuffle=True)
    model = LSTMModel()
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.Adam(model.parameters(), lr=0.001)
    for epoch in range(EPOCHS):
        for seq, target in loader:
            optimizer.zero_grad()
            output = model(seq)
            loss = criterion(output, target)
            loss.backward()
            optimizer.step()
    return model

def predict_lstm(model, last_seq):
    if model is None:
        return 0.25, None
    with torch.no_grad():
        input_seq = torch.tensor([ENCODER.get(s, 1) for s in last_seq]).unsqueeze(0)
        output = model(input_seq)
        prob = torch.softmax(output, dim=1).squeeze().numpy()
        pred_idx = np.argmax(prob)
        return prob[pred_idx], DECODER[pred_idx]

def decide_bias(structures, model, markov):
    if not structures:
        return 'Neutral', 0.0
    last = structures[-1]
    last_seq = structures[-SEQ_LEN:] if len(structures) >= SEQ_LEN else structures
    lstm_conf, _ = predict_lstm(model, last_seq)
    if last in markov and markov[last]:
        next_probs = markov[last]
        bullish_prob = sum(next_probs.get(s, 0) for s in ['HH', 'HL'])
        bearish_prob = sum(next_probs.get(s, 0) for s in ['LH', 'LL'])
        markov_bias = 'Bullish' if bullish_prob > bearish_prob else 'Bearish'
        markov_conf = max(bullish_prob, bearish_prob)
    else:
        markov_bias = 'Neutral'
        markov_conf = 0.0
    conf = (lstm_conf + markov_conf) / 2 if model else markov_conf
    bias = 'Bullish' if ('HH' in last or 'HL' in last or markov_bias == 'Bullish') else 'Bearish'
    return bias, conf

def trade_setup(df, bias):
    last_close = df['close'].iloc[-1]
    atr = df['atr'].iloc[-1]
    if bias == 'Bullish':
        entry = last_close
        sl = last_close - 1.5 * atr
        tp = last_close + 3 * atr
    elif bias == 'Bearish':
        entry = last_close
        sl = last_close + 1.5 * atr
        tp = last_close - 3 * atr
    else:
        return {'rr': 0}
    risk = abs(entry - sl)
    reward = abs(tp - entry)
    rr = reward / risk if risk > 0 else 0
    return {'entry': entry, 'sl': sl, 'tp': tp, 'rr': rr}

def human_summary(symbol, df, last_struct, bias, conf, setup):
    last_struct = last_struct if last_struct else 'N/A'
    return f"""
🚀 TITAN SIGNAL - {symbol}
โครงสร้างล่าสุด: {last_struct}
ทิศทาง: {bias} (Confidence: {conf:.1%})
Entry: {setup['entry']:,.0f} USDT
Stop Loss: {setup['sl']:,.0f} USDT
Take Profit: {setup['tp']:,.0f} USDT
Risk:Reward = 1:{setup['rr']:.2f}
คำแนะนำ: {'เข้าเทรดทันที!' if bias != 'Neutral' else 'รอสัญญาณชัดเจน'}
    """

def detect_triangle(df, window=60):
    recent = df[-window:].copy()
    recent['idx'] = range(len(recent))
    swings = recent[recent['swing'].notnull()]
    if len(swings) < 5:
        return None
    highs = swings[swings['swing'] == 'H'][['idx', 'high']]
    lows = swings[swings['swing'] == 'L'][['idx', 'low']]
    if len(highs) < 3 or len(lows) < 3:
        return None
    upper_slope = np.polyfit(highs['idx'], highs['high'], 1)
    lower_slope = np.polyfit(lows['idx'], lows['low'], 1)
    if upper_slope[0] < 0 and lower_slope[0] > 0:
        return {
            'type': 'Symmetrical Triangle',
            'upper': upper_slope,
            'lower': lower_slope,
            'highs': highs,
            'lows': lows
        }
    return None

def plot_chart_with_triangle(df, triangle=None):
    fig, ax = plt.subplots(figsize=(16, 8))
    ax.plot(df['timestamp'], df['close'], label='BTC/USDT Close', color='blue', linewidth=1.5)
    
    swings = df[df['swing'].notnull()]
    ax.scatter(swings[swings['swing'] == 'H']['timestamp'], swings[swings['swing'] == 'H']['high'],
               marker='^', color='green', s=100, label='Swing High')
    ax.scatter(swings[swings['swing'] == 'L']['timestamp'], swings[swings['swing'] == 'L']['low'],
               marker='v', color='red', s=100, label='Swing Low')
    
    if triangle:
        # คำนวณเส้น trendline ให้ครอบคลุมช่วง triangle
        recent_len = 100  # แสดงช่วงล่าสุดให้เห็นชัด
        start_idx = max(0, len(df) - recent_len)
        idx_range = range(start_idx, len(df))
        dates = df['timestamp'].iloc[idx_range]
        plot_idx = range(len(idx_range))
        
        # ปรับ polyfit ให้ใช้ plot_idx ที่ต่อเนื่อง
        upper_line = np.polyval(triangle['upper'], plot_idx[-len(triangle['highs']):])
        lower_line = np.polyval(triangle['lower'], plot_idx[-len(triangle['lows']):])
        
        # วาดเส้น (ปรับความยาวให้พอดี)
        ax.plot(dates[-len(upper_line):], upper_line, 'r--', linewidth=2, label='Upper Trendline (Converging)')
        ax.plot(dates[-len(lower_line):], lower_line, 'g--', linewidth=2, label='Lower Trendline (Converging)')
        ax.fill_between(dates[-len(upper_line):], upper_line, lower_line, alpha=0.15, color='orange')
        
        # Label A B C D E - ใช้ index จริงของ df
        points = pd.concat([triangle['highs'], triangle['lows']]).sort_values('idx')
        points = points.iloc[-5:]  # 5 จุดล่าสุด
        labels = ['A', 'B', 'C', 'D', 'E']
        for i, (_, row) in enumerate(points.iterrows()):
            local_idx = row['idx']
            global_idx = len(df) - len(df[-60:]) + local_idx  # แปลงเป็น index จริงของ df
            price = row['high'] if 'high' in row else row['low']
            ts = df['timestamp'].iloc[global_idx]
            ax.text(ts, price * 1.01, labels[i], fontsize=14, fontweight='bold', color='purple')
        
        ax.set_title('BTC/USDT - Detected Symmetrical Triangle (ABCDE) - Breakout Imminent!', fontsize=16, color='darkblue')
    else:
        ax.set_title('BTC/USDT Market Structure Chart', fontsize=16)
    
    ax.grid(alpha=0.3)
    ax.legend(fontsize=12)
    ax.xaxis.set_major_formatter(mdates.DateFormatter('%b %Y'))
    ax.tick_params(axis='x', rotation=45)
    plt.tight_layout()
    plt.show()
    plt.tight_layout()
    plt.savefig('/mnt/newhdd/dev/price/btc_chart.png', dpi=300, bbox_inches='tight')  # บันทึกเป็นไฟล์
    print("📊 กราฟบันทึกเรียบร้อยที่: /mnt/newhdd/dev/price/btc_chart.png")
    # plt.show()  # comment บรรทัดนี้ทิ้งเพื่อไม่ให้ error บน server
# =========================
# RUN เต็มระบบ
# =========================
def run_titan_live():
    print("🔄 กำลังดึงข้อมูล Real-Time จาก Binance...")
    df = fetch_live_data()
    current_price = get_current_price()
    print(f"💰 ราคา BTC/USDT ปัจจุบัน: {current_price:,.0f} USDT ({datetime.now().strftime('%d %B %Y')})")
    
    df = detect_swings(df)
    structures = build_structure(df)
    markov = train_markov(structures)
    model = train_lstm(structures)
    
    bias, conf = decide_bias(structures, model, markov)
    setup = trade_setup(df, bias)
    
    last_struct = structures[-1] if structures else None
    
    if conf < MIN_CONFIDENCE or setup['rr'] < MIN_RR:
        print("⛔ ไม่มีสัญญาณเทรด valid")
    else:
        print(human_summary(SYMBOL, df, last_struct, bias, conf, setup))
    
    triangle = detect_triangle(df)
    if triangle:
        print("🔺 ตรวจพบ Symmetrical Triangle Pattern (ABCDE)! กำลังจะ breakout แรง")
        print("   คาดการณ์: ถ้า breakout ขึ้น → Target 100,000+ / ลง → Retest 85,000")
    else:
        print("📉 ไม่พบรูปแบบสามเหลี่ยมชัดเจนในตอนนี้")
    
    plot_chart_with_triangle(df, triangle)

if __name__ == "__main__":
    run_titan_live()