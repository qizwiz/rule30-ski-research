import yfinance as yf
import pandas as pd
import json
from datetime import datetime
import os

class IchimokuForwardTest:
    def __init__(self, starting_cash=100.0, log_file='forward_test_log.json'):
        self.cash = starting_cash
        self.position_size = 0
        self.entry_price = 0
        self.log_file = log_file
        self.trades = []
        
        # Load existing log if it exists
        if os.path.exists(log_file):
            with open(log_file, 'r') as f:
                data = json.load(f)
                self.trades = data.get('trades', [])
                last_state = data.get('current_state', {})
                self.cash = last_state.get('cash', starting_cash)
                self.position_size = last_state.get('position_size', 0)
                self.entry_price = last_state.get('entry_price', 0)
    
    def calculate_ichimoku(self, data, tenkan=9, kijun=26, senkou=52):
        """Calculate Ichimoku Cloud indicators"""
        # Tenkan-sen (Conversion Line)
        high_9 = data['High'].rolling(window=tenkan).max()
        low_9 = data['Low'].rolling(window=tenkan).min()
        data['tenkan_sen'] = (high_9 + low_9) / 2
        
        # Kijun-sen (Base Line)
        high_26 = data['High'].rolling(window=kijun).max()
        low_26 = data['Low'].rolling(window=kijun).min()
        data['kijun_sen'] = (high_26 + low_26) / 2
        
        # Senkou Span A (Leading Span A)
        data['senkou_span_a'] = ((data['tenkan_sen'] + data['kijun_sen']) / 2).shift(kijun)
        
        # Senkou Span B (Leading Span B)
        high_52 = data['High'].rolling(window=senkou).max()
        low_52 = data['Low'].rolling(window=senkou).min()
        data['senkou_span_b'] = ((high_52 + low_52) / 2).shift(kijun)
        
        # Cloud boundaries
        data['cloud_top'] = data[['senkou_span_a', 'senkou_span_b']].max(axis=1)
        data['cloud_bottom'] = data[['senkou_span_a', 'senkou_span_b']].min(axis=1)
        
        return data
    
    def get_signal(self, data):
        """Determine current trading signal"""
        if len(data) < 52:
            return 'WAIT', 'Insufficient data'
        
        current = data.iloc[-1]
        current_price = current['Close']
        
        # Check if we have valid indicators
        if pd.isna(current['cloud_top']) or pd.isna(current['tenkan_sen']):
            return 'WAIT', 'Indicators not ready'
        
        # Entry signals: Price above cloud AND Tenkan above Kijun
        above_cloud = current_price > current['cloud_top']
        tk_bullish = current['tenkan_sen'] > current['kijun_sen']
        
        # Exit signals: Price below cloud OR Tenkan below Kijun
        below_cloud = current_price < current['cloud_bottom']
        tk_bearish = current['tenkan_sen'] < current['kijun_sen']
        
        if self.position_size == 0:
            if above_cloud and tk_bullish:
                return 'BUY', f'Price ${current_price:.2f} above cloud, TK bullish'
            else:
                return 'HOLD', f'Waiting for entry signal (Above cloud: {above_cloud}, TK bullish: {tk_bullish})'
        else:
            if below_cloud or tk_bearish:
                return 'SELL', f'Exit signal: Below cloud={below_cloud}, TK bearish={tk_bearish}'
            else:
                return 'HOLD', f'Holding position from ${self.entry_price:.2f}'
    
    def execute_trade(self, signal, price, reason):
        """Execute a trade and log it"""
        timestamp = datetime.now().isoformat()
        
        if signal == 'BUY' and self.position_size == 0:
            # Buy with 95% of cash
            amount_to_invest = self.cash * 0.95
            fee = amount_to_invest * 0.001  # 0.1% fee
            shares = (amount_to_invest - fee) / price
            
            self.position_size = shares
            self.entry_price = price
            self.cash = self.cash - amount_to_invest
            
            trade = {
                'timestamp': timestamp,
                'action': 'BUY',
                'price': price,
                'shares': shares,
                'cost': amount_to_invest,
                'fee': fee,
                'reason': reason,
                'cash_remaining': self.cash
            }
            self.trades.append(trade)
            return trade
            
        elif signal == 'SELL' and self.position_size > 0:
            # Sell entire position
            proceeds = self.position_size * price
            fee = proceeds * 0.001
            net_proceeds = proceeds - fee
            
            profit = net_proceeds - (self.entry_price * self.position_size)
            profit_pct = (price / self.entry_price - 1) * 100
            
            self.cash += net_proceeds
            
            trade = {
                'timestamp': timestamp,
                'action': 'SELL',
                'price': price,
                'shares': self.position_size,
                'proceeds': net_proceeds,
                'fee': fee,
                'entry_price': self.entry_price,
                'profit': profit,
                'profit_pct': profit_pct,
                'reason': reason,
                'cash_total': self.cash
            }
            self.trades.append(trade)
            
            self.position_size = 0
            self.entry_price = 0
            return trade
        
        return None
    
    def check_market(self):
        """Check current market and generate signal"""
        # Fetch data
        print("Fetching SOL-USD data...")
        data = yf.download('SOL-USD', period='3mo', interval='1d', progress=False)
        
        if data.empty:
            print("ERROR: Could not fetch data")
            return
        
        # Flatten multi-index columns if needed
        if isinstance(data.columns, pd.MultiIndex):
            data.columns = data.columns.get_level_values(0)
        
        # Calculate indicators
        data = self.calculate_ichimoku(data)
        
        # Get current signal
        signal, reason = self.get_signal(data)
        current_price = data['Close'].iloc[-1]
        
        # Log current state
        timestamp = datetime.now().isoformat()
        current_state = {
            'timestamp': timestamp,
            'signal': signal,
            'price': float(current_price),
            'reason': reason,
            'cash': self.cash,
            'position_size': self.position_size,
            'entry_price': self.entry_price
        }
        
        # Calculate current portfolio value
        if self.position_size > 0:
            position_value = self.position_size * current_price
            total_value = self.cash + position_value
            unrealized_profit = (current_price - self.entry_price) * self.position_size
            unrealized_pct = (current_price / self.entry_price - 1) * 100 if self.entry_price > 0 else 0
        else:
            position_value = 0
            total_value = self.cash
            unrealized_profit = 0
            unrealized_pct = 0
        
        current_state['position_value'] = position_value
        current_state['total_value'] = total_value
        current_state['unrealized_profit'] = unrealized_profit
        current_state['unrealized_pct'] = unrealized_pct
        
        # Execute trade if signal is BUY or SELL
        trade = None
        if signal in ['BUY', 'SELL']:
            trade = self.execute_trade(signal, current_price, reason)
        
        # Save to log
        self.save_log(current_state, trade)
        
        # Print summary
        print(f"\n{'='*70}")
        print(f"FORWARD TEST CHECK - {timestamp}")
        print(f"{'='*70}")
        print(f"SOL Price: ${current_price:.2f}")
        print(f"Signal: {signal}")
        print(f"Reason: {reason}")
        print(f"")
        print(f"Portfolio Status:")
        print(f"  Cash: ${self.cash:.2f}")
        if self.position_size > 0:
            print(f"  Position: {self.position_size:.6f} SOL @ ${self.entry_price:.2f}")
            print(f"  Position Value: ${position_value:.2f}")
            print(f"  Unrealized P/L: ${unrealized_profit:.2f} ({unrealized_pct:+.2f}%)")
        print(f"  Total Value: ${total_value:.2f}")
        print(f"  Total Return: ${total_value - 100:.2f} ({(total_value/100 - 1)*100:+.1f}%)")
        print(f"")
        print(f"Trades Completed: {len([t for t in self.trades if t['action'] == 'SELL'])}")
        
        if trade:
            print(f"\n🔥 TRADE EXECUTED:")
            print(f"   {trade['action']} {trade['shares']:.6f} SOL @ ${trade['price']:.2f}")
            if trade['action'] == 'SELL':
                print(f"   Profit: ${trade['profit']:.2f} ({trade['profit_pct']:+.2f}%)")
        
        print(f"{'='*70}\n")
        
        return current_state
    
    def save_log(self, current_state, trade=None):
        """Save current state to log file"""
        log_data = {
            'test_started': datetime.now().isoformat(),
            'starting_cash': 100.0,
            'current_state': current_state,
            'trades': self.trades,
            'trade_count': len([t for t in self.trades if t['action'] == 'SELL']),
        }
        
        with open(self.log_file, 'w') as f:
            json.dump(log_data, f, indent=2)
        
        print(f"✓ Logged to {self.log_file}")
    
    def show_history(self):
        """Display full trade history"""
        if not self.trades:
            print("No trades yet")
            return
        
        print(f"\n{'='*70}")
        print(f"TRADE HISTORY")
        print(f"{'='*70}")
        
        for i, trade in enumerate(self.trades, 1):
            print(f"\n{i}. {trade['timestamp']}")
            print(f"   {trade['action']}: {trade['shares']:.6f} SOL @ ${trade['price']:.2f}")
            if trade['action'] == 'SELL':
                print(f"   Entry: ${trade['entry_price']:.2f}")
                print(f"   Profit: ${trade['profit']:.2f} ({trade['profit_pct']:+.2f}%)")
            print(f"   Reason: {trade['reason']}")

if __name__ == '__main__':
    print("ICHIMOKU FORWARD TEST")
    print("Starting with $100 on SOL-USD")
    print("This will track REAL signals going forward (no cheating!)\n")
    
    tester = IchimokuForwardTest()
    tester.check_market()
    
    print("\nTo check again later, just run: python3 forward_test.py")
    print("Set up a daily cron job to track this automatically!")
