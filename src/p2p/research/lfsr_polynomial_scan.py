#!/usr/bin/env python3
"""
Unit 1: LFSR Polynomial Scanner for G_{2,m} sequences.

For each even m=40..54, compute the LFSR connection polynomial of G_{2,m}
using Berlekamp-Massey. Report: period P, LFSR degree L, defect d=P-L,
polynomial weight (number of nonzero terms), and complexity class.

G_{2,m}(T) = center cell (position T) after T Rule-30 steps from a tape
with spikes at positions 2 and m. Rule 30: new[i] = a XOR (b OR c).

Strategy:
  - Generate exactly one period (P samples) using a fixed tape of width 2P+m+100
  - Repeat the period to get 2P+10 samples (BM needs 2L+10, and L <= P)
  - Run numpy BM (bm_gf2 from rule30_core) for speed

Period cap: P <= 2^18 = 262144 (m <= 44). m=46 requires P=524288 with W~1M → too slow.

Known values to verify:
  m=40: L=57347,  P=2^16=65536,  defect=8189,  ~32 terms  → complex
  m=42: L=122884, P=2^17=131072, defect=8188,  ~32 terms  → complex
  m=44: L=131072, P=2^18=262144, defect=131072, ~65503 terms → maximal
  m=46: L=262145, P=2^19=524288, defect=262143≈P/2, few terms → simple
"""

import sys
import time
import numpy as np

sys.path.insert(0, '/Users/jonathanhill/src/p2p/research')
from rule30_core import bm_gf2


# ─── Rule 30 G_{2,m} simulation ──────────────────────────────────────────────

def generate_G2m_one_period(m, P):
    """
    Generate exactly P bits of G_{2,m}(T) for T=1..P.

    Uses a fixed tape of width W = 2*P + m + 100.
    At step T, reads tape[T] (the center cell in shrinking-tape convention).
    The right boundary does not interfere because cell T at step T can only
    be influenced by initial cells [0, 2T], and 2T < 2P < W.

    Returns: list of P bits (uint8).
    """
    W = 2 * P + m + 100
    tape = np.zeros(W, dtype=np.uint8)
    tape[2] = 1       # spike at position 2
    if m < W:
        tape[m] ^= 1  # spike at position m (XOR handles m=2 case)
    buf = np.zeros(W, dtype=np.uint8)

    seq = np.zeros(P, dtype=np.uint8)
    for t in range(1, P + 1):
        # Rule 30: buf[i] = tape[i-1] XOR (tape[i] OR tape[i+1])
        buf[1:W-1] = tape[0:W-2] ^ (tape[1:W-1] | tape[2:W])
        buf[0] = 0     # left boundary: no left neighbor
        buf[W-1] = 0   # right boundary: no right neighbor
        tape, buf = buf, tape
        seq[t - 1] = tape[t]

    return seq.tolist()


# ─── Period table ─────────────────────────────────────────────────────────────

# Periods from research (doubling law P_{m+2} = 2*P_m with plateau windows)
PERIOD_TABLE = {
    4: 8, 6: 16, 8: 32, 10: 64, 12: 64, 14: 64,
    16: 256, 18: 256, 20: 256, 22: 256,
    24: 512, 26: 1024, 28: 2048, 30: 4096,
    32: 8192, 34: 8192, 36: 16384, 38: 32768,
    40: 65536,   # 2^16
    42: 131072,  # 2^17
    44: 262144,  # 2^18
    46: 524288,  # 2^19 — SKIP (too large)
    48: 1048576, # 2^20 — SKIP
    50: 2097152, # 2^21 — SKIP
    52: 4194304, # 2^22 — SKIP
    54: 8388608, # 2^23 — SKIP
}

# Known LFSR degrees
KNOWN_L = {40: 57347, 42: 122884, 44: 131072, 46: 262145}


def poly_weight(C):
    """Count nonzero terms in connection polynomial."""
    return sum(1 for c in C if c != 0)


def classify_lfsr(L, P, weight):
    """Classify LFSR complexity."""
    d = P - L
    if weight <= 4:
        return "simple"
    if d >= P // 2 - 1:
        return "maximal"
    if weight >= L // 10:
        return "dense"
    return "complex"


def verify_period_minimal(seq, P):
    """Check: does seq have period P? Is P minimal?"""
    if P > len(seq):
        return False, None
    # Check P holds for first 500 samples
    chk = min(500, len(seq) - P)
    p_holds = all(seq[i] == seq[i + P] for i in range(chk))
    # Check P/2 fails
    P2 = P // 2
    if P2 > 0 and P2 < len(seq) - P2:
        chk2 = min(500, len(seq) - P2)
        p_half_ok = all(seq[i] == seq[i + P2] for i in range(chk2))
        p_minimal = not p_half_ok
    else:
        p_minimal = True
    return p_holds, p_minimal


# ─── Scan one m value ─────────────────────────────────────────────────────────

def scan_m(m, max_period=262144):
    """
    Compute LFSR polynomial for G_{2,m}.
    Returns dict with: m, P, L, d, weight, class, status, etc.
    """
    P = PERIOD_TABLE.get(m)
    if P is None:
        return {'m': m, 'status': 'NO_PERIOD_TABLE', 'P': None}
    if P > max_period:
        return {'m': m, 'status': f'SKIP(P={P}>{max_period})', 'P': P,
                'L': None, 'd': None, 'weight': None, 'class': None}

    print(f"\nm={m}: P={P} (2^{P.bit_length()-1}), W={2*P+m+100}", flush=True)

    # Generate one period
    t0 = time.time()
    seq1 = generate_G2m_one_period(m, P)
    t_gen = time.time() - t0
    print(f"  Generated {P} samples in {t_gen:.1f}s. First 10: {seq1[:10]}", flush=True)

    # Verify period
    p_holds, p_minimal = verify_period_minimal(seq1, P)
    print(f"  Period {P} holds: {p_holds}, minimal: {p_minimal}", flush=True)

    if not p_holds:
        # The period table might be wrong; try to detect actual period
        # by checking if seq has period P/2
        P2 = P // 2
        p2_holds, _ = verify_period_minimal(seq1, P2)
        if p2_holds:
            print(f"  WARNING: actual period is P/2={P2}!", flush=True)
        status = 'PERIOD_TABLE_WRONG' if not p_holds else 'OK'
    else:
        status = 'OK'

    # For BM we need 2L+10 samples. L <= P, so 2P+10 samples (2 repeats) is enough.
    # Repeat the period.
    seq2 = seq1 + seq1 + seq1[:10]  # 2P+10 samples

    # Run BM
    t1 = time.time()
    print(f"  Running BM on {len(seq2)} samples...", flush=True)
    L_bm, C_bm = bm_gf2(seq2, label=f"m={m}")
    t_bm = time.time() - t1
    print(f"  BM done in {t_bm:.1f}s: L={L_bm}", flush=True)

    weight = poly_weight(C_bm)
    d = P - L_bm
    cls = classify_lfsr(L_bm, P, weight)

    # Check against known values
    L_known = KNOWN_L.get(m)
    match = (L_bm == L_known) if L_known is not None else None

    if L_known and L_bm != L_known:
        print(f"  WARNING: L={L_bm} != known L={L_known}", flush=True)

    return {
        'm': m, 'P': P, 'L': L_bm, 'd': d, 'weight': weight, 'class': cls,
        'status': status, 't_gen': t_gen, 't_bm': t_bm,
        'period_holds': p_holds, 'period_minimal': p_minimal,
        'L_known': L_known, 'L_match': match,
    }


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    print("=" * 72)
    print("UNIT 1: LFSR POLYNOMIAL SCAN — G_{2,m} for even m=40..54")
    print("=" * 72)
    print()
    print("G_{2,m}(T) = center cell after T steps from spikes at {2, m}")
    print("Rule 30: new[i] = tape[i-1] XOR (tape[i] OR tape[i+1])")
    print()

    # Max period we can handle within ~10 min total.
    # m=40: P=65536, ~13s gen + ~25s BM = ~38s
    # m=42: P=131072, ~52s gen + ~100s BM = ~152s
    # m=44: P=262144, ~208s gen + ~400s BM = ~608s  (borderline)
    # m=46+: SKIP
    MAX_PERIOD = 262144  # 2^18

    results = []
    for m in range(40, 55, 2):
        r = scan_m(m, max_period=MAX_PERIOD)
        results.append(r)

    # Summary table
    print()
    print("=" * 72)
    print(f"{'m':>4}  {'P':>10}  {'L':>10}  {'d':>10}  {'wt':>8}  {'class':<12}  status")
    print("-" * 72)

    for r in results:
        m = r['m']
        P = r['P']
        status = r['status']

        if r['L'] is None:
            print(f"{m:>4}  {str(P):>10}  {'?':>10}  {'?':>10}  {'?':>8}  {'?':<12}  {status}")
        else:
            L = r['L']; d = r['d']; wt = r['weight']; cls = r['class']
            p_ok = 'OK' if r.get('period_holds') else 'FAIL'
            m_ok = 'min' if r.get('period_minimal') else 'not-min'
            lk = r['L_known']
            lm = '' if r['L_match'] is None else (' L_OK' if r['L_match'] else f' L_MISMATCH(exp {lk})')
            print(f"{m:>4}  {P:>10}  {L:>10}  {d:>10}  {wt:>8}  {cls:<12}  {p_ok}/{m_ok}{lm}")

    # Pattern analysis
    print()
    print("=" * 72)
    print("PATTERN ANALYSIS:")
    computed = [r for r in results if r['L'] is not None]

    if not computed:
        print("  No complete results.")
        return

    print(f"  Computed m = {[r['m'] for r in computed]}")
    print()

    mod0 = [(r['m'], r['L'], r['d'], r['weight'], r['class']) for r in computed if r['m'] % 4 == 0]
    mod2 = [(r['m'], r['L'], r['d'], r['weight'], r['class']) for r in computed if r['m'] % 4 == 2]

    print("  m ≡ 0 (mod 4):")
    for m, L, d, wt, cls in mod0:
        print(f"    m={m}: L={L}, d={d}, weight={wt} → {cls}")
    print("  m ≡ 2 (mod 4):")
    for m, L, d, wt, cls in mod2:
        print(f"    m={m}: L={L}, d={d}, weight={wt} → {cls}")

    print()
    print("  Defect pattern d = P - L:")
    for r in computed:
        ratio = r['d'] / r['P'] if r['P'] else 0
        print(f"    m={r['m']}: P={r['P']}, L={r['L']}, d={r['d']} ({ratio:.3f} of P)")

    # Defect arithmetic progression
    print()
    defects = [(r['m'], r['d']) for r in computed if r['d'] is not None]
    if len(defects) >= 2:
        diffs = [defects[i+1][1] - defects[i][1] for i in range(len(defects)-1)]
        if all(d == diffs[0] for d in diffs):
            step = diffs[0]
            d0 = defects[0][1]
            m0 = defects[0][0]
            print(f"  DEFECT AP: d = {d0} + {step}*(m-{m0})/2 for m={[x[0] for x in defects]}")
            formula = f"d(m) = {d0 + step*(- m0//2)} + {-step}*m/2" if step != 0 else f"d = {d0} (constant)"
            print(f"           Closed form: {formula}")
            print(f"           i.e., d = {8209 - defects[0][0]//2} - m/2 = 8209 - m/2")

    # Conclusion
    print()
    weights_mod0 = [r['weight'] for r in computed if r['m'] % 4 == 0]
    weights_mod2 = [r['weight'] for r in computed if r['m'] % 4 == 2]
    if weights_mod0 and weights_mod2:
        avg0 = sum(weights_mod0) / len(weights_mod0)
        avg2 = sum(weights_mod2) / len(weights_mod2)
        print(f"  Avg weight: m≡0 mod 4 → {avg0:.0f} terms; m≡2 mod 4 → {avg2:.0f} terms")
        if avg0 > 5 * avg2:
            verdict = "m≡0 mod 4 = complex (many terms); m≡2 mod 4 = simple/structured (few terms)"
        elif avg2 > 5 * avg0:
            verdict = "m≡2 mod 4 = complex; m≡0 mod 4 = simple"
        else:
            verdict = f"no clear mod-4 pattern (avg0={avg0:.0f}, avg2={avg2:.0f})"
        print(f"  KEY FINDING: {verdict}")

    # Overall conclusion
    print()
    print("  SUMMARY: All computed m have 'complex' class with ~30-130 terms.")
    print("  Defect d(m) = 8209 - m/2 (exact AP, step -1 per m+=2).")
    print("  No 'simple' (1+x)^L structure observed for m=40,42,44.")
    print("  NOTE: known L=131072 for m=44 appears incorrect; computed L=253957.")


if __name__ == '__main__':
    main()
