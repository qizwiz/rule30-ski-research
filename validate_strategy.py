"""
COMPREHENSIVE STRATEGY VALIDATION SUITE
Tests Ichimoku strategy across 5 critical dimensions to find if it's real or bullshit
"""
import yfinance as yf
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import json
from itertools import product

class StrategyValidator:
    def __init__(self, starting_cash=100.0):
        self.starting_cash = starting_cash
        self.results = {}
        
    def calculate_ichimoku(self, data, tenkan=9, kijun=26, senkou=52):
        """Calculate Ichimoku Cloud indicators"""
        df = data.copy()
        
        # Tenkan-sen (Conversion Line)
        high_tenkan = df['High'].rolling(window=tenkan).max()
        low_tenkan = df['Low'].rolling(window=tenkan).min()
        df['tenkan_sen'] = (high_tenkan + low_tenkan) / 2
        
        # Kijun-sen (Base Line)
        high_kijun = df['High'].rolling(window=kijun).max()
        low_kijun = df['Low'].rolling(window=kijun).min()
        df['kijun_sen'] = (high_kijun + low_kijun) / 2
        
        # Senkou Span A (Leading Span A)
        df['senkou_span_a'] = ((df['tenkan_sen'] + df['kijun_sen']) / 2).shift(kijun)
        
        # Senkou Span B (Leading Span B)
        high_senkou = df['High'].rolling(window=senkou).max()
        low_senkou = df['Low'].rolling(window=senkou).min()
        df['senkou_span_b'] = ((high_senkou + low_senkou) / 2).shift(kijun)
        
        # Cloud boundaries
        df['cloud_top'] = df[['senkou_span_a', 'senkou_span_b']].max(axis=1)
        df['cloud_bottom'] = df[['senkou_span_a', 'senkou_span_b']].min(axis=1)
        
        return df
    
    def generate_signals(self, data, tenkan=9, kijun=26, senkou=52):
        """Generate buy/sell signals based on Ichimoku"""
        df = self.calculate_ichimoku(data, tenkan, kijun, senkou)
        
        df['signal'] = 0  # 0 = hold, 1 = buy, -1 = sell
        
        for i in range(senkou, len(df)):
            price = df['Close'].iloc[i]
            cloud_top = df['cloud_top'].iloc[i]
            cloud_bottom = df['cloud_bottom'].iloc[i]
            tenkan_val = df['tenkan_sen'].iloc[i]
            kijun_val = df['kijun_sen'].iloc[i]
            
            if pd.isna(cloud_top) or pd.isna(tenkan_val):
                continue
                
            # Buy signal: Price above cloud AND Tenkan above Kijun
            if price > cloud_top and tenkan_val > kijun_val:
                df.loc[df.index[i], 'signal'] = 1
            # Sell signal: Price below cloud OR Tenkan below Kijun  
            elif price < cloud_bottom or tenkan_val < kijun_val:
                df.loc[df.index[i], 'signal'] = -1
                
        return df
    
    def backtest_strategy(self, data, tenkan=9, kijun=26, senkou=52, fee=0.001):
        """Run backtest on data with given parameters"""
        df = self.generate_signals(data, tenkan, kijun, senkou)
        
        cash = self.starting_cash
        position = 0
        entry_price = 0
        trades = []
        equity_curve = []
        
        for i in range(len(df)):
            price = df['Close'].iloc[i]
            signal = df['signal'].iloc[i]
            
            # Track equity
            portfolio_value = cash + (position * price)
            equity_curve.append({
                'date': df.index[i],
                'value': portfolio_value,
                'price': price
            })
            
            # Execute trades
            if signal == 1 and position == 0:  # Buy
                amount_to_invest = cash * 0.95
                fee_cost = amount_to_invest * fee
                shares = (amount_to_invest - fee_cost) / price
                position = shares
                entry_price = price
                cash = cash - amount_to_invest
                
                trades.append({
                    'date': df.index[i],
                    'action': 'BUY',
                    'price': price,
                    'shares': shares,
                    'cost': amount_to_invest
                })
                
            elif signal == -1 and position > 0:  # Sell
                proceeds = position * price
                fee_cost = proceeds * fee
                net_proceeds = proceeds - fee_cost
                profit = net_proceeds - (entry_price * position)
                profit_pct = (price / entry_price - 1) * 100
                
                cash += net_proceeds
                
                trades.append({
                    'date': df.index[i],
                    'action': 'SELL',
                    'price': price,
                    'shares': position,
                    'proceeds': net_proceeds,
                    'entry_price': entry_price,
                    'profit': profit,
                    'profit_pct': profit_pct
                })
                
                position = 0
                entry_price = 0
        
        # Final portfolio value
        final_value = cash + (position * df['Close'].iloc[-1])
        
        # Calculate statistics
        equity_df = pd.DataFrame(equity_curve)
        returns = equity_df['value'].pct_change().dropna()
        
        # Calculate max drawdown
        rolling_max = equity_df['value'].expanding().max()
        drawdown = (equity_df['value'] - rolling_max) / rolling_max
        max_drawdown = drawdown.min() * 100
        
        # Win rate
        winning_trades = [t for t in trades if t['action'] == 'SELL' and t['profit'] > 0]
        losing_trades = [t for t in trades if t['action'] == 'SELL' and t['profit'] <= 0]
        total_trades = len([t for t in trades if t['action'] == 'SELL'])
        win_rate = len(winning_trades) / total_trades * 100 if total_trades > 0 else 0
        
        # Sharpe ratio (annualized)
        if len(returns) > 0 and returns.std() > 0:
            sharpe = (returns.mean() / returns.std()) * np.sqrt(252)
        else:
            sharpe = 0
        
        # Buy and hold comparison
        buy_hold_shares = (self.starting_cash * 0.95) / df['Close'].iloc[senkou]
        buy_hold_value = buy_hold_shares * df['Close'].iloc[-1]
        buy_hold_return = (buy_hold_value / self.starting_cash - 1) * 100
        
        return {
            'final_value': final_value,
            'profit': final_value - self.starting_cash,
            'return_pct': (final_value / self.starting_cash - 1) * 100,
            'trades': trades,
            'total_trades': total_trades,
            'win_rate': win_rate,
            'max_drawdown': max_drawdown,
            'sharpe_ratio': sharpe,
            'buy_hold_return': buy_hold_return,
            'beat_buy_hold': (final_value / self.starting_cash - 1) * 100 > buy_hold_return,
            'equity_curve': equity_curve
        }
    
    # TEST 1: MULTI-ASSET VALIDATION
    def test_multi_asset(self, period='2y'):
        """Test same strategy across different assets"""
        print("\n" + "="*80)
        print("TEST 1: MULTI-ASSET VALIDATION")
        print("Testing if Ichimoku works on assets I DIDN'T cherry-pick")
        print("="*80)
        
        assets = {
            'SOL-USD': 'Solana (cherry-picked winner)',
            'BTC-USD': 'Bitcoin (less volatile)',
            'ETH-USD': 'Ethereum (mid volatility)',
            'DOGE-USD': 'Dogecoin (shitcoin test)',
            'SPY': 'S&P 500 (traditional market)'
        }
        
        results = {}
        
        for ticker, description in assets.items():
            print(f"\nTesting {ticker} ({description})...")
            try:
                data = yf.download(ticker, period=period, interval='1d', progress=False)
                if data.empty:
                    print(f"  ✗ No data available")
                    continue
                
                # Flatten multi-index if needed
                if isinstance(data.columns, pd.MultiIndex):
                    data.columns = data.columns.get_level_values(0)
                
                result = self.backtest_strategy(data)
                results[ticker] = {
                    'description': description,
                    **result
                }
                
                print(f"  Final Value: ${result['final_value']:.2f}")
                print(f"  Return: {result['return_pct']:.1f}%")
                print(f"  Buy & Hold: {result['buy_hold_return']:.1f}%")
                print(f"  Beat B&H: {'✓' if result['beat_buy_hold'] else '✗'}")
                print(f"  Win Rate: {result['win_rate']:.1f}%")
                print(f"  Max Drawdown: {result['max_drawdown']:.1f}%")
                print(f"  Sharpe: {result['sharpe_ratio']:.2f}")
                
            except Exception as e:
                print(f"  ✗ Error: {e}")
        
        self.results['multi_asset'] = results
        
        # Summary
        print(f"\n{'='*80}")
        print("MULTI-ASSET SUMMARY:")
        working_assets = [t for t, r in results.items() if r['return_pct'] > 0]
        beat_bh = [t for t, r in results.items() if r['beat_buy_hold']]
        print(f"  Assets with positive returns: {len(working_assets)}/{len(results)}")
        print(f"  Assets that beat buy & hold: {len(beat_bh)}/{len(results)}")
        
        if len(working_assets) < 3:
            print(f"  ⚠ WARNING: Strategy only works on {len(working_assets)} assets")
            print(f"  This suggests OVERFITTING or SURVIVORSHIP BIAS")
        else:
            print(f"  ✓ Strategy shows some generalization")
        
        return results
    
    # TEST 2: WALK-FORWARD ANALYSIS
    def test_walk_forward(self, ticker='SOL-USD'):
        """Split data into train/test periods"""
        print(f"\n{'='*80}")
        print("TEST 2: WALK-FORWARD ANALYSIS")
        print("Does strategy work out-of-sample?")
        print(f"{'='*80}")
        
        # Download full dataset
        data = yf.download(ticker, start='2023-01-01', end='2025-12-31', interval='1d', progress=False)
        if isinstance(data.columns, pd.MultiIndex):
            data.columns = data.columns.get_level_values(0)
        
        # Define periods
        periods = [
            ('2023-01-01', '2023-12-31', '2024-01-01', '2024-12-31'),  # Train 2023, test 2024
            ('2024-01-01', '2024-12-31', '2025-01-01', '2025-12-31'),  # Train 2024, test 2025
        ]
        
        results = []
        
        for train_start, train_end, test_start, test_end in periods:
            print(f"\nTrain: {train_start} to {train_end}, Test: {test_start} to {test_end}")
            
            # Get test data
            test_data = data[test_start:test_end]
            
            if len(test_data) < 100:
                print("  ✗ Insufficient test data")
                continue
            
            result = self.backtest_strategy(test_data)
            results.append({
                'train_period': f"{train_start} to {train_end}",
                'test_period': f"{test_start} to {test_end}",
                **result
            })
            
            print(f"  Test Return: {result['return_pct']:.1f}%")
            print(f"  Buy & Hold: {result['buy_hold_return']:.1f}%")
            print(f"  Beat B&H: {'✓' if result['beat_buy_hold'] else '✗'}")
            print(f"  Max Drawdown: {result['max_drawdown']:.1f}%")
        
        self.results['walk_forward'] = results
        
        # Summary
        print(f"\n{'='*80}")
        print("WALK-FORWARD SUMMARY:")
        avg_return = np.mean([r['return_pct'] for r in results])
        positive_periods = len([r for r in results if r['return_pct'] > 0])
        beat_bh_count = len([r for r in results if r['beat_buy_hold']])
        
        print(f"  Average out-of-sample return: {avg_return:.1f}%")
        print(f"  Positive periods: {positive_periods}/{len(results)}")
        print(f"  Beat buy & hold: {beat_bh_count}/{len(results)}")
        
        if positive_periods < len(results):
            print(f"  ⚠ WARNING: Strategy failed in {len(results) - positive_periods} test periods")
            print(f"  This suggests strategy may not adapt to changing conditions")
        
        return results
    
    # TEST 3: PARAMETER SENSITIVITY
    def test_parameter_sensitivity(self, ticker='SOL-USD', period='2y'):
        """Test if strategy breaks with small parameter changes"""
        print(f"\n{'='*80}")
        print("TEST 3: PARAMETER SENSITIVITY")
        print("Does strategy break with small parameter tweaks?")
        print(f"{'='*80}")
        
        data = yf.download(ticker, period=period, interval='1d', progress=False)
        if isinstance(data.columns, pd.MultiIndex):
            data.columns = data.columns.get_level_values(0)
        
        # Test variations around default (9, 26, 52)
        tenkan_values = [7, 8, 9, 10, 11]
        kijun_values = [24, 25, 26, 27, 28]
        
        print(f"\nTesting Tenkan variations (Kijun=26, Senkou=52):")
        tenkan_results = []
        for t in tenkan_values:
            result = self.backtest_strategy(data, tenkan=t, kijun=26, senkou=52)
            tenkan_results.append({
                'tenkan': t,
                'return': result['return_pct'],
                'sharpe': result['sharpe_ratio'],
                'max_dd': result['max_drawdown']
            })
            marker = "  <-- DEFAULT" if t == 9 else ""
            print(f"  Tenkan={t}: Return={result['return_pct']:.1f}%, Sharpe={result['sharpe_ratio']:.2f}{marker}")
        
        print(f"\nTesting Kijun variations (Tenkan=9, Senkou=52):")
        kijun_results = []
        for k in kijun_values:
            result = self.backtest_strategy(data, tenkan=9, kijun=k, senkou=52)
            kijun_results.append({
                'kijun': k,
                'return': result['return_pct'],
                'sharpe': result['sharpe_ratio'],
                'max_dd': result['max_drawdown']
            })
            marker = "  <-- DEFAULT" if k == 26 else ""
            print(f"  Kijun={k}: Return={result['return_pct']:.1f}%, Sharpe={result['sharpe_ratio']:.2f}{marker}")
        
        self.results['parameter_sensitivity'] = {
            'tenkan': tenkan_results,
            'kijun': kijun_results
        }
        
        # Analysis
        print(f"\n{'='*80}")
        print("SENSITIVITY ANALYSIS:")
        
        default_return = [r for r in tenkan_results if r['tenkan'] == 9][0]['return']
        tenkan_returns = [r['return'] for r in tenkan_results]
        return_std = np.std(tenkan_returns)
        
        print(f"  Default (9,26,52) return: {default_return:.1f}%")
        print(f"  Return std deviation across Tenkan: {return_std:.1f}%")
        
        if return_std > 50:
            print(f"  ⚠ HIGH SENSITIVITY: Small changes cause big swings")
            print(f"  This suggests OVERFITTING to specific parameters")
        elif return_std < 20:
            print(f"  ✓ ROBUST: Strategy stable across parameter changes")
        else:
            print(f"  ⚠ MODERATE SENSITIVITY: Some parameter dependence")
        
        return {'tenkan': tenkan_results, 'kijun': kijun_results}
    
    # TEST 4: BEAR MARKET TEST
    def test_bear_market(self, ticker='SOL-USD'):
        """Test in crypto winter 2022"""
        print(f"\n{'='*80}")
        print("TEST 4: BEAR MARKET TEST")
        print("Does strategy survive when market crashes?")
        print(f"{'='*80}")
        
        # Crypto winter period
        bear_periods = [
            ('2022-01-01', '2022-12-31', 'Crypto Winter 2022'),
            ('2021-05-01', '2021-07-31', 'May 2021 Crash'),
        ]
        
        results = []
        
        for start, end, description in bear_periods:
            print(f"\n{description} ({start} to {end}):")
            try:
                data = yf.download(ticker, start=start, end=end, interval='1d', progress=False)
                if isinstance(data.columns, pd.MultiIndex):
                    data.columns = data.columns.get_level_values(0)
                
                if len(data) < 100:
                    print("  ✗ Insufficient data")
                    continue
                
                result = self.backtest_strategy(data)
                results.append({
                    'period': description,
                    **result
                })
                
                print(f"  Strategy Return: {result['return_pct']:.1f}%")
                print(f"  Buy & Hold Return: {result['buy_hold_return']:.1f}%")
                print(f"  Max Drawdown: {result['max_drawdown']:.1f}%")
                print(f"  Protected capital: {'✓' if result['return_pct'] > result['buy_hold_return'] else '✗'}")
                
            except Exception as e:
                print(f"  ✗ Error: {e}")
        
        self.results['bear_market'] = results
        
        # Summary
        print(f"\n{'='*80}")
        print("BEAR MARKET SUMMARY:")
        if results:
            protected = [r for r in results if r['return_pct'] > r['buy_hold_return']]
            positive = [r for r in results if r['return_pct'] > 0]
            
            print(f"  Periods tested: {len(results)}")
            print(f"  Positive returns: {len(positive)}/{len(results)}")
            print(f"  Protected vs buy & hold: {len(protected)}/{len(results)}")
            
            if len(protected) < len(results):
                print(f"  ⚠ WARNING: Strategy failed to protect capital in bear markets")
            else:
                print(f"  ✓ Strategy provides downside protection")
        
        return results
    
    # TEST 5: REAL STATISTICS
    def test_statistics(self, ticker='SOL-USD', period='2y'):
        """Calculate comprehensive risk metrics"""
        print(f"\n{'='*80}")
        print("TEST 5: COMPREHENSIVE STATISTICS")
        print("What are the REAL risk/reward numbers?")
        print(f"{'='*80}")
        
        data = yf.download(ticker, period=period, interval='1d', progress=False)
        if isinstance(data.columns, pd.MultiIndex):
            data.columns = data.columns.get_level_values(0)
        
        result = self.backtest_strategy(data)
        trades = [t for t in result['trades'] if t['action'] == 'SELL']
        
        print(f"\n{ticker} Performance:")
        print(f"  Final Value: ${result['final_value']:.2f}")
        print(f"  Total Return: {result['return_pct']:.1f}%")
        print(f"  Buy & Hold: {result['buy_hold_return']:.1f}%")
        print(f"  Annualized Return: {(result['return_pct'] / 2):.1f}% (approx)")
        
        print(f"\nRisk Metrics:")
        print(f"  Max Drawdown: {result['max_drawdown']:.1f}%")
        print(f"  Sharpe Ratio: {result['sharpe_ratio']:.2f}")
        
        print(f"\nTrade Statistics:")
        print(f"  Total Trades: {result['total_trades']}")
        print(f"  Win Rate: {result['win_rate']:.1f}%")
        
        if trades:
            winning_trades = [t for t in trades if t['profit'] > 0]
            losing_trades = [t for t in trades if t['profit'] <= 0]
            
            avg_win = np.mean([t['profit'] for t in winning_trades]) if winning_trades else 0
            avg_loss = np.mean([abs(t['profit']) for t in losing_trades]) if losing_trades else 0
            
            print(f"  Average Win: ${avg_win:.2f}")
            print(f"  Average Loss: ${avg_loss:.2f}")
            
            if avg_loss > 0:
                win_loss_ratio = avg_win / avg_loss
                print(f"  Win/Loss Ratio: {win_loss_ratio:.2f}")
            
            best_trade = max(trades, key=lambda t: t['profit'])
            worst_trade = min(trades, key=lambda t: t['profit'])
            
            print(f"  Best Trade: ${best_trade['profit']:.2f} ({best_trade['profit_pct']:.1f}%)")
            print(f"  Worst Trade: ${worst_trade['profit']:.2f} ({worst_trade['profit_pct']:.1f}%)")
        
        print(f"\nRealistic Expectations (with 1% spreads):")
        realistic_return = result['return_pct'] - (result['total_trades'] * 2)  # 1% each way
        print(f"  Adjusted Return: {realistic_return:.1f}%")
        print(f"  Monthly Estimate: ${realistic_return / 24:.2f}/month on $100")
        
        self.results['statistics'] = {
            'final_value': result['final_value'],
            'return_pct': result['return_pct'],
            'buy_hold': result['buy_hold_return'],
            'max_drawdown': result['max_drawdown'],
            'sharpe': result['sharpe_ratio'],
            'win_rate': result['win_rate'],
            'total_trades': result['total_trades'],
            'realistic_monthly': realistic_return / 24
        }
        
        return result
    
    def run_all_tests(self):
        """Run all 5 validation tests"""
        print("\n" + "="*80)
        print(" COMPREHENSIVE STRATEGY VALIDATION ")
        print(" Testing if Ichimoku is REAL EDGE or OVERFITTED GARBAGE ")
        print("="*80)
        
        # Run all tests
        self.test_multi_asset()
        self.test_walk_forward()
        self.test_parameter_sensitivity()
        self.test_bear_market()
        self.test_statistics()
        
        # Final verdict
        self.print_final_verdict()
        
        # Save results
        self.save_results()
    
    def print_final_verdict(self):
        """Synthesize all tests into final assessment"""
        print(f"\n\n{'='*80}")
        print(" FINAL VERDICT ")
        print(f"{'='*80}\n")
        
        score = 0
        max_score = 5
        flags = []
        
        # Test 1: Multi-Asset
        if 'multi_asset' in self.results:
            working = len([r for r in self.results['multi_asset'].values() if r['return_pct'] > 0])
            total = len(self.results['multi_asset'])
            if working >= 3:
                score += 1
                print(f"✓ Multi-Asset: Works on {working}/{total} assets - Shows generalization")
            else:
                print(f"✗ Multi-Asset: Only works on {working}/{total} assets - OVERFITTING WARNING")
                flags.append("Overfitting to SOL")
        
        # Test 2: Walk-Forward
        if 'walk_forward' in self.results:
            positive = len([r for r in self.results['walk_forward'] if r['return_pct'] > 0])
            total = len(self.results['walk_forward'])
            if positive == total:
                score += 1
                print(f"✓ Walk-Forward: Profitable in {positive}/{total} periods - Adapts well")
            else:
                print(f"✗ Walk-Forward: Failed in {total - positive}/{total} periods - Poor adaptation")
                flags.append("Doesn't adapt to changing markets")
        
        # Test 3: Parameter Sensitivity
        if 'parameter_sensitivity' in self.results:
            tenkan_returns = [r['return'] for r in self.results['parameter_sensitivity']['tenkan']]
            std = np.std(tenkan_returns)
            if std < 50:
                score += 1
                print(f"✓ Sensitivity: Stable (std={std:.1f}%) - Robust parameters")
            else:
                print(f"✗ Sensitivity: High variance (std={std:.1f}%) - Parameters overfitted")
                flags.append("Parameters are curve-fitted")
        
        # Test 4: Bear Market
        if 'bear_market' in self.results:
            protected = len([r for r in self.results['bear_market'] if r['return_pct'] > r['buy_hold_return']])
            total = len(self.results['bear_market'])
            if protected >= total * 0.5:
                score += 1
                print(f"✓ Bear Market: Protected in {protected}/{total} crashes - Has defense")
            else:
                print(f"✗ Bear Market: Failed to protect in crashes - Bull market only")
                flags.append("Only works in bull markets")
        
        # Test 5: Statistics
        if 'statistics' in self.results:
            stats = self.results['statistics']
            if stats['sharpe'] > 1.0 and stats['win_rate'] > 40:
                score += 1
                print(f"✓ Statistics: Sharpe={stats['sharpe']:.2f}, WinRate={stats['win_rate']:.1f}% - Good metrics")
            else:
                print(f"✗ Statistics: Sharpe={stats['sharpe']:.2f}, WinRate={stats['win_rate']:.1f}% - Weak metrics")
                flags.append("Poor risk-adjusted returns")
        
        # Final score
        print(f"\n{'='*80}")
        print(f"FINAL SCORE: {score}/{max_score}")
        print(f"{'='*80}\n")
        
        if score >= 4:
            print("🎯 VERDICT: Strategy shows REAL EDGE")
            print("   This might actually work. Worth paper trading 30 days.")
            print("   Still need forward testing, but passed validation hurdles.")
        elif score >= 3:
            print("⚠️  VERDICT: Strategy has POTENTIAL but RED FLAGS")
            print("   Proceed with caution. Paper trade required.")
            for flag in flags:
                print(f"   - {flag}")
        elif score >= 2:
            print("❌ VERDICT: Strategy is QUESTIONABLE")
            print("   Likely overfitted. Not recommended for real money.")
            for flag in flags:
                print(f"   - {flag}")
        else:
            print("🚫 VERDICT: Strategy is GARBAGE")
            print("   Do NOT trade this with real money.")
            print("   Pure backtest curve-fitting.")
            for flag in flags:
                print(f"   - {flag}")
        
        print(f"\n{'='*80}\n")
    
    def save_results(self):
        """Save all results to JSON"""
        filename = 'validation_results.json'
        with open(filename, 'w') as f:
            # Convert numpy types to native Python types
            def convert_types(obj):
                if isinstance(obj, np.integer):
                    return int(obj)
                elif isinstance(obj, np.floating):
                    return float(obj)
                elif isinstance(obj, np.ndarray):
                    return obj.tolist()
                elif isinstance(obj, pd.Timestamp):
                    return obj.isoformat()
                elif isinstance(obj, dict):
                    return {k: convert_types(v) for k, v in obj.items()}
                elif isinstance(obj, list):
                    return [convert_types(item) for item in obj]
                return obj
            
            clean_results = convert_types(self.results)
            json.dump(clean_results, f, indent=2)
        
        print(f"✓ Results saved to {filename}")

if __name__ == '__main__':
    print("\n" + "="*80)
    print(" ICHIMOKU STRATEGY VALIDATION ")
    print(" Running comprehensive tests to find the TRUTH ")
    print("="*80)
    print("\nThis will take 5-10 minutes...")
    print("Testing across multiple assets, time periods, and market conditions\n")
    
    validator = StrategyValidator(starting_cash=100.0)
    validator.run_all_tests()
    
    print("\nValidation complete!")
    print("Check validation_results.json for detailed data")
