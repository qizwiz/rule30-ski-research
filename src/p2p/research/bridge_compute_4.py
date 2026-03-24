#!/usr/bin/env python3
"""
Bridge Compute 4 — Left-permutivity recursive structure of s(n)
Run date: 2026-03-24

s(n) = rule30_n(e_n), the center cell after n steps from a single black cell.

Goal: find structure in the sequence s(0..50), test recurrences, divide-and-conquer,
and exploit left-permutivity to understand the recursive decomposition.

Left-permutivity of Rule 30:
  rule30(l,c,r) = l XOR g(c,r)   where g(c,r) = c OR r

This means: given the top row, the leftmost output cell at each generation is
completely determined by the leftmost two cells of the current generation.
By induction, rule30_n(c)[0] = c[0] XOR F(c[1], c[2], ..., c[n])
for some function F that depends on the upper-right triangle of the cone.

For e_n: c[0]=0, c[1]=...=c[n-1]=0, c[n]=1, c[n+1]=...=c[2n]=0.
So s(n) = rule30_n(e_n) = 0 XOR F(0,...,0,1,0,...,0) = F(0,...,0,1,0,...,0).
The 1 is at index n-1 within c[1..2n] (i.e., the n-th position 0-indexed, which is c[n]).
"""

import sys
import time
import numpy as np


# ============================================================
# Core computation
# ============================================================

def rule30_step(a):
    """Single rule30 step on a 1D array. Returns array shrunk by 2 (open boundaries)."""
    # rule30(l,c,r) = l XOR (c OR r)
    l = a[:-2]
    c = a[1:-1]
    r = a[2:]
    return l ^ (c | r)


def rule30_n_center(c, n):
    """Apply rule30 n times, return leftmost cell (index 0 after n shrinks)."""
    a = np.array(c, dtype=np.uint8).copy()
    for _ in range(n):
        if len(a) < 3:
            # Can't apply rule30 to arrays shorter than 3
            # Return 0 if empty or length 1
            return int(a[0]) if len(a) > 0 else 0
        a = rule30_step(a)
    return int(a[0]) if len(a) > 0 else 0


def e_n(n):
    """Single-black-cell initial condition of length 2n+1, 1 at position n."""
    c = [0] * (2 * n + 1)
    c[n] = 1
    return c


def s(n):
    """s(n) = rule30_n(e_n)."""
    return rule30_n_center(e_n(n), n)


# ============================================================
# 1. Compute s(0..50) and display the sequence
# ============================================================

print("=" * 60)
print("1. SEQUENCE s(n) = rule30_n(e_n) for n=0..50")
print("=" * 60)

seq = []
for n in range(51):
    val = s(n)
    seq.append(val)

print("s(0..50):")
line = ""
for i, v in enumerate(seq):
    line += str(v)
    if (i + 1) % 25 == 0:
        print(f"  n={i-24:2d}..{i:2d}: {line}")
        line = ""
if line:
    print(f"  n={51-len(line):2d}..50: {line}")

print(f"\nFull sequence (as list): {seq}")
print(f"Sum (number of 1s in n=0..50): {sum(seq)}")
print(f"Fraction of 1s: {sum(seq)/51:.4f}")

# ============================================================
# 2. Kolmogorov complexity proxy: look for short recurrences
# ============================================================

print("\n" + "=" * 60)
print("2. RECURRENCE SEARCH: s(n) = f(s(n-1), ..., s(n-k))")
print("=" * 60)

def check_recurrence(seq, lookback):
    """Check if seq[n] can be predicted from seq[n-lookback..n-1] using any boolean function."""
    # Collect all (context → output) pairs
    table = {}
    inconsistent = False
    for i in range(lookback, len(seq)):
        ctx = tuple(seq[i - lookback:i])
        out = seq[i]
        if ctx in table:
            if table[ctx] != out:
                inconsistent = True
                break
        else:
            table[ctx] = out
    return not inconsistent, len(table)

print("\nChecking linear recurrence over GF(2): s(n) = XOR of subset of s(n-1..n-k)")
print("(Berlekamp-Massey style)")

def berlekamp_massey_gf2(s):
    """Find shortest LFSR (linear recurrence over GF(2)) generating s."""
    n = len(s)
    C = [1]
    B = [1]
    L = 0
    m = 1
    b = 1
    for i in range(n):
        # Compute discrepancy
        d = s[i]
        for j in range(1, L + 1):
            if j < len(C):
                d ^= C[j] & s[i - j]
        d &= 1
        if d == 0:
            m += 1
        elif 2 * L <= i:
            T = C[:]
            # C = C XOR (d/b) * x^m * B, but over GF(2) d/b = d*b = d (since b=1 always here)
            while len(C) < len(B) + m:
                C.append(0)
            for j in range(len(B)):
                C[j + m] ^= d * B[j]
            B = T
            L = i + 1 - L
            m = 1
        else:
            while len(C) < len(B) + m:
                C.append(0)
            for j in range(len(B)):
                C[j + m] ^= d * B[j]
            m += 1
    return L, C

L, C = berlekamp_massey_gf2(seq)
print(f"  LFSR length (linear complexity): {L}")
print(f"  Connection polynomial coefficients: {C[:min(10, len(C))]}{'...' if len(C) > 10 else ''}")
print(f"  Interpretation: need at least {L} previous terms for linear recurrence")
print(f"  (Random binary sequence of length {len(seq)} would have linear complexity ~{len(seq)//2})")

print("\nChecking boolean recurrences for lookback k=1..6:")
for k in range(1, 7):
    ok, n_contexts = check_recurrence(seq, k)
    print(f"  k={k}: {'CONSISTENT (recurrence EXISTS)' if ok else 'INCONSISTENT (no pure lookback-k recurrence)'} "
          f"[{n_contexts} distinct contexts observed out of {2**k} possible]")

# ============================================================
# 3. Divide-and-conquer: can s(n) be computed from s(n//2 ± k)?
# ============================================================

print("\n" + "=" * 60)
print("3. DIVIDE-AND-CONQUER: s(n) from s(n//2 ± small offsets?)")
print("=" * 60)

print("\nFor each n, check if s(n) matches any simple function of s(n//2 ± k) for k=0..3:")
print("(Boolean functions of up to 4 nearby values)")

import itertools

def find_dac_formula(seq, n, offsets, max_n):
    """For a single n, check if seq[n] = f(seq[n//2 + o] for o in offsets) for any boolean f."""
    h = n // 2
    inputs = []
    for o in offsets:
        idx = h + o
        if 0 <= idx <= max_n:
            inputs.append(seq[idx])
        else:
            return None, None  # out of range
    return tuple(inputs), seq[n]

# Try: can s(n) be XOR of seq[n//2], seq[(n-1)//2], seq[(n+1)//2] ?
print("\n  XOR-based: s(n) XOR seq[n//2] XOR seq[(n-1)//2]?")
for n in range(4, 51):
    h = n // 2
    h2 = (n - 1) // 2
    predicted = seq[h] ^ seq[h2]
    mark = "OK" if predicted == seq[n] else "FAIL"
    if n <= 20 or mark == "FAIL":
        print(f"    n={n:2d}: s(n)={seq[n]}, s(n//2)={seq[h]}, s((n-1)//2)={seq[h2]}, XOR={predicted} [{mark}]")

# Check simple lookup table: seq[n] = F(seq[n//2], seq[n//2 + (n%2)])
print("\n  Two-input table: s(n) = F(s(n//2), s(n//2 + (n%2)))?")
pairs_to_output = {}
consistent = True
for n in range(2, 51):
    h = n // 2
    k = n % 2
    inputs = (seq[h], seq[h + k] if h + k < len(seq) else -1)
    if inputs[1] == -1:
        continue
    if inputs in pairs_to_output:
        if pairs_to_output[inputs] != seq[n]:
            consistent = False
            break
    else:
        pairs_to_output[inputs] = seq[n]
print(f"  Result: {'CONSISTENT' if consistent else 'INCONSISTENT'}, table: {pairs_to_output}")

# ============================================================
# 4. Left-permutivity recursive decomposition
# ============================================================

print("\n" + "=" * 60)
print("4. LEFT-PERMUTIVITY RECURSIVE DECOMPOSITION")
print("=" * 60)

print("""
Left-permutivity: rule30(l,c,r) = l XOR g(c,r).
So after 1 step on input c of length 2n+1:
  output[0] = c[0] XOR g(c[1], c[2])

After n steps from e_n = [0,...,0,1,0,...,0] (1 at position n):
  s(n) = e_n[0] XOR (some function of e_n[1..2n])
       = 0 XOR F(e_n[1..2n])
       = F(0,...,0,1,0,...,0)   [the 1 is at position n-1 within the 2n-length array]

So s(n) = rule30_n applied to [0,...,0,1,0,...,0] of length 2n (1 at position n-1),
then take position 0 (after left-permutive unfolding).

Wait — let's be precise. Left-permutivity says:
  The LEFT-MOST output cell of ANY CA step only depends on the left 2 cells of input.
  But rule30_n(c)[0] involves ALL of c.

Let me verify the XOR-shift formula directly:
""")

print("Checking: s(n) = XOR of rule30_n(c)[0] where c = e_n")
print("Decomposing via step-by-step left-permutivity:")

def rule30_n_verbose(c, n, verbose=False):
    """Rule30 for n steps, print each intermediate step."""
    a = list(c)
    if verbose:
        print(f"    Gen 0: {a}")
    for step in range(n):
        if len(a) < 3:
            break
        new_a = []
        for i in range(len(a) - 2):
            val = a[i] ^ (a[i+1] | a[i+2])
            new_a.append(val)
        a = new_a
        if verbose:
            print(f"    Gen {step+1}: {a}")
    return a[0] if a else 0

# Verify our s(n) for small n with verbose output
for n in [0, 1, 2, 3, 4, 5]:
    c = e_n(n)
    val = rule30_n_verbose(c, n, verbose=(n <= 3))
    print(f"  s({n}) = {val} (computed), seq[{n}] = {seq[n]} {'OK' if val == seq[n] else 'MISMATCH'}")

# Key recursive observation:
# rule30_{n+1}(e_{n+1}) at position 0 = e_{n+1}[0] XOR g(e_{n+1}[1], e_{n+1}[2])
# after one step we get an array of length 2n+1
# what is that array?

print("\nChecking: after 1 step from e_{n+1}, what array do we get?")
print("If it equals e_n, then s(n+1) = s(n) always (it doesn't, but let's see).")
for n in range(1, 8):
    c = e_n(n + 1)  # length 2(n+1)+1 = 2n+3
    after_one = []
    for i in range(len(c) - 2):
        after_one.append(c[i] ^ (c[i+1] | c[i+2]))
    after_one = tuple(after_one)
    expected_en = tuple(e_n(n))
    match = "=e_n" if after_one == expected_en else f"≠e_n"
    print(f"  n={n}: 1-step(e_{{n+1}}) = {after_one} [{match}]  e_n={expected_en}")

# ============================================================
# 5. Self-similarity test: s(n) vs rule30_{n-1}(related input)?
# ============================================================

print("\n" + "=" * 60)
print("5. SELF-SIMILARITY: s(n) = rule30_{n-1}(some related input)?")
print("=" * 60)

print("""
Hypothesis: s(n) might equal rule30_{n-1} applied to some "compressed" version of e_n.

The natural candidate: after stripping 1 layer of left-permutive expansion,
the remaining computation might correspond to a smaller problem.
""")

# After 1 step from e_{n+1}, we get some array. What is it?
# Check if s(n+1) = rule30_n(that intermediate array)[0]
print("Checking: s(n+1) = rule30_n(first_step(e_{n+1}))[0]?")
print("(This is trivially true by construction — rule30 is just n+1 steps = 1 step + n steps)")
print("More interesting: does first_step(e_{n+1}) have a SIMPLE FORM relative to e_n?\n")

for n in range(1, 10):
    c_np1 = e_n(n + 1)  # 2n+3 cells
    after_one = [c_np1[i] ^ (c_np1[i+1] | c_np1[i+2]) for i in range(len(c_np1)-2)]
    # after_one has length 2n+1
    # Compare with e_n (also length 2n+1)
    en = e_n(n)
    diff_positions = [i for i in range(len(after_one)) if after_one[i] != en[i]]
    print(f"  n={n}: first_step(e_{{n+1}}) vs e_n: differ at positions {diff_positions}")
    print(f"         first_step = {after_one}")
    print(f"         e_n        = {en}")

# ============================================================
# 6. The critical observation: what IS first_step(e_n)?
# ============================================================

print("\n" + "=" * 60)
print("6. WHAT IS first_step(e_n)? Pattern search.")
print("=" * 60)

print("\nFor e_n = [0,...,0,1,0,...,0] (1 at position n):")
print("rule30(0,0,0)=0, rule30(0,0,1)=1, rule30(0,1,0)=1, rule30(0,1,1)=0")
print("rule30(1,0,0)=1, rule30(1,0,1)=0, rule30(1,1,0)=0, rule30(1,1,1)=0\n")

# rule30(l,c,r) = l XOR c XOR r XOR (c AND r)... let me verify
# rule 30 in binary: 00011110
# for (l,c,r) as 3-bit: 111->0,110->0,101->0,100->1,011->1,010->1,001->1,000->0
# so rule30(l,c,r) = l ^ (c | r)

def rule30_cell(l, c, r):
    return l ^ (c | r)

print("Verification: rule30(l,c,r) = l XOR (c OR r):")
for l in range(2):
    for c in range(2):
        for r in range(2):
            val = rule30_cell(l, c, r)
            # rule 30 truth table
            table = {(0,0,0):0,(0,0,1):1,(0,1,0):1,(0,1,1):1,(1,0,0):1,(1,0,1):0,(1,1,0):0,(1,1,1):0}
            expected = table[(l,c,r)]
            ok = "OK" if val == expected else "FAIL"
            if val != expected:
                print(f"  ({l},{c},{r}): {val} (got) vs {expected} (rule30) [{ok}]")
print("(No output = all match)")

print("\nFirst step of e_n analytically:")
print("e_n has 0s everywhere except position n.")
print("At position i, the triple is (e_n[i-1], e_n[i], e_n[i+1]).")
print("For i far from n: (0,0,0) → 0")
print("For i = n-1: (0,0,1) → 1  [l=0,c=0,r=1 → 0 XOR (0 OR 1) = 1]")
print("For i = n:   (0,1,0) → 1  [l=0,c=1,r=0 → 0 XOR (1 OR 0) = 1]")
print("For i = n+1: (1,0,0) → 1  [l=1,c=0,r=0 → 1 XOR (0 OR 0) = 1]")
print("So first_step(e_n)[i] = 1 for i in {n-1, n, n+1} relative to OUTPUT indexing...")
print("Wait — output has length 2n-1 (after trimming 1 from each side)")
print("Output position i corresponds to input triple (i, i+1, i+2).")
print("\nFor e_n of length 2n+1 (positions 0..2n), with 1 only at position n:")
print("Output position i: uses input (i, i+1, i+2)")
print("  Non-zero only when {i, i+1, i+2} intersects {n}")
print("  i.e., i ∈ {n-2, n-1, n}  [since i ≤ n ≤ i+2, so i ≥ n-2 and i ≤ n]")
print("But wait: rule30(l,c,r) = l XOR (c OR r), so output depends on l (leftmost)")
print("\nLet me compute directly for n=5:")
n = 5
c = e_n(n)
print(f"e_{n} = {c}")
after = [rule30_cell(c[i], c[i+1], c[i+2]) for i in range(len(c)-2)]
print(f"After 1 step: {after}")
print(f"Nonzero positions: {[i for i,v in enumerate(after) if v]}")
print(f"In terms of original position n={n}: nonzero at {[i for i,v in enumerate(after) if v]}")
print(f"= {{n-2, n-1, n}} - 1 (0-indexed output) = {{{n-2}, {n-1}, {n}}}")

print("\nGeneral pattern (n ≥ 2):")
print("first_step(e_n) has 1s at output positions n-2, n-1, n")
print("= positions n-2, n-1, n in the (2n-1)-length output array.")
print("This is a 3-cell block of 1s centered at position n-1.")

# Verify for all n 1..10
for n in range(1, 11):
    c = e_n(n)
    after = [rule30_cell(c[i], c[i+1], c[i+2]) for i in range(len(c)-2)]
    nz = [i for i,v in enumerate(after) if v]
    print(f"  n={n:2d}: first_step nonzero at {nz}, pattern: {after}")

# ============================================================
# 7. What is second_step(e_n)?
# ============================================================

print("\n" + "=" * 60)
print("7. ITERATING: what are subsequent steps from e_n?")
print("=" * 60)

print("\nEvolution of e_n step by step (n=8, showing all generations):")
n = 8
c = e_n(n)
print(f"Gen 0 (length {len(c)}): {c}")
for step in range(1, n + 1):
    new_c = [rule30_cell(c[i], c[i+1], c[i+2]) for i in range(len(c)-2)]
    c = new_c
    print(f"Gen {step:2d} (length {len(c)}): {c}  → leftmost = {c[0]}")

# ============================================================
# 8. Dependency structure: which input bits does s(n) depend on?
# ============================================================

print("\n" + "=" * 60)
print("8. DEPENDENCY STRUCTURE: s(n) as polynomial in e_n[0..2n]")
print("=" * 60)

print("""
Over GF(2), any boolean function f: {0,1}^m → {0,1} can be written as a multilinear polynomial.
Since rule30(l,c,r) = l XOR (c OR r) = l + c + r + cr (mod 2), the degree grows.

Let's find the actual monomials (via Fourier/Walsh coefficients over GF(2)).
""")

def compute_fourier_gf2(n_rule30, n_vars=None):
    """
    Compute the multilinear polynomial representation of rule30_n over GF(2).
    Returns a dict: frozenset → coefficient (all coefficients are 1 or 0 mod 2).
    Works by exhaustive enumeration for small n_vars.
    """
    if n_vars is None:
        n_vars = 2 * n_rule30 + 1

    # f: {0,1}^{n_vars} → {0,1}
    # Compute the ANF (Algebraic Normal Form) via Mobius transform
    # For n_vars ≤ 20
    if n_vars > 20:
        return None

    N = 2 ** n_vars
    truth_table = np.zeros(N, dtype=np.uint8)
    for i in range(N):
        c = [(i >> k) & 1 for k in range(n_vars)]
        truth_table[i] = rule30_n_center(c, n_rule30)

    # Mobius transform to get ANF
    anf = truth_table.copy()
    for i in range(n_vars):
        for j in range(N):
            if (j >> i) & 1:
                anf[j] ^= anf[j ^ (1 << i)]

    # Collect monomials
    monomials = []
    for i in range(N):
        if anf[i]:
            monomial = frozenset(k for k in range(n_vars) if (i >> k) & 1)
            monomials.append(monomial)

    return monomials

print("Computing ANF (algebraic normal form) of rule30_n for small n:")
for n in range(1, 7):
    monomials = compute_fourier_gf2(n)
    if monomials is None:
        print(f"  n={n}: too large")
        continue
    degrees = [len(m) for m in monomials]
    max_deg = max(degrees) if degrees else 0
    num_terms = len(monomials)
    print(f"  n={n}: {num_terms} terms, max degree {max_deg}")
    # Print low-degree terms
    low = [(min(m) if m else 'const', sorted(m)) for m in monomials if len(m) <= 2]
    print(f"         Low-degree monomials (deg ≤ 2): {[sorted(m) for m in monomials if len(m) <= 2]}")
    high = [sorted(m) for m in monomials if len(m) == max_deg]
    print(f"         Highest-degree ({max_deg}) monomials: {high[:5]}{'...' if len(high) > 5 else ''}")

# ============================================================
# 9. Summary: is the sequence random/incompressible?
# ============================================================

print("\n" + "=" * 60)
print("9. SUMMARY: RANDOMNESS AND COMPRESSIBILITY ASSESSMENT")
print("=" * 60)

# Autocorrelation
print("\nAutocorrelation of s(0..50):")
s_arr = np.array(seq, dtype=float)
s_centered = s_arr - s_arr.mean()
autocorr = np.correlate(s_centered, s_centered, mode='full')
autocorr = autocorr[len(autocorr)//2:]
autocorr /= autocorr[0] if autocorr[0] != 0 else 1
print(f"  Lag 1: {autocorr[1]:.4f}")
print(f"  Lag 2: {autocorr[2]:.4f}")
print(f"  Lag 3: {autocorr[3]:.4f}")
print(f"  Lag 4: {autocorr[4]:.4f}")
print(f"  Lag 5: {autocorr[5]:.4f}")

# Runs test
runs = 1
for i in range(1, len(seq)):
    if seq[i] != seq[i-1]:
        runs += 1
expected_runs = 1 + 2 * sum(seq) * (len(seq) - sum(seq)) / len(seq)
print(f"\nRuns test: observed={runs}, expected (random)={expected_runs:.1f}")
print(f"  (close to expected suggests randomness)")

print(f"\nLinear complexity {L} vs sequence length {len(seq)}:")
print(f"  Ratio: {L/len(seq):.3f} (close to 0.5 = maximal complexity for random binary sequence)")

print("\n" + "=" * 60)
print("10. KEY FINDING: RELATIONSHIP s(n) vs s(n-1) via extended inputs")
print("=" * 60)

# The key idea from the prompt: can s(n) be expressed as rule30_{n-1} applied to some
# related input?
#
# We know: s(n) = rule30_n(e_n)
# After 1 step from e_n of length 2n+1, we get an array of length 2n-1.
# That 2n-1 array, when we apply n-1 more steps, gives s(n).
#
# Question: is that 2n-1 array = e_{n-1} shifted, or some other structured input?

print("\nFor each n, compute: the intermediate array after 1 step from e_n.")
print("Compare this to e_{n-1} and other candidates:\n")

def apply_one_step(c):
    return [rule30_cell(c[i], c[i+1], c[i+2]) for i in range(len(c)-2)]

for n in range(2, 12):
    c = e_n(n)
    mid = apply_one_step(c)  # length 2n-1

    # e_{n-1} has length 2(n-1)+1 = 2n-1 ✓
    en1 = e_n(n - 1)

    # Check alignment
    assert len(mid) == len(en1), f"Length mismatch: {len(mid)} vs {len(en1)}"

    match = mid == en1
    if not match:
        diff = [(i, mid[i], en1[i]) for i in range(len(mid)) if mid[i] != en1[i]]
    else:
        diff = []

    # Check if mid is a shifted version of something simple
    # mid for n≥2 has pattern: all 0s except positions n-2, n-1, n are 1
    # e_{n-1} has all 0s except position n-1 is 1
    # So they differ at n-2 and n (mid has extra 1s)

    print(f"  n={n}: mid={mid}")
    print(f"        e_{{n-1}}={en1}")
    if match:
        print(f"        MATCH!")
    else:
        print(f"        Differ at: {diff}")

    # Also check: what does rule30_{n-1} give on mid?
    val_from_mid = rule30_n_center(mid, n - 1)
    print(f"        rule30_{{n-1}}(mid) = {val_from_mid} = s({n}) = {seq[n]} {'OK' if val_from_mid == seq[n] else 'FAIL'}")
    print()

# ============================================================
# 11. Three-black-cell initial condition
# ============================================================

print("=" * 60)
print("11. THREE-BLACK-CELL INPUT: first_step(e_n) IS a natural input")
print("=" * 60)

print("""
We established that first_step(e_n) = array with 1s at positions {n-2, n-1, n} (for n≥2).
This is a 3-black-cell initial condition: let's call it t_n (for n≥2, length 2n-1):
  t_n = [0,...,0, 1, 1, 1, 0,...,0]
        with the block of 3 ones centered at position n-1.

So: s(n) = rule30_{n-1}(t_n)  where t_n is the 3-cell block.

Now: t_n has the SAME support structure as first_step(e_n).
Can we express rule30_{n-1}(t_n) recursively in terms of smaller problems?

Since rule30 is NOT linear, rule30_{n-1}(t_n) ≠ rule30_{n-1}(e_{n-1}) + corrections.
But maybe there's a recursive structure specific to the 3-cell block.
""")

def three_cell_input(n):
    """[0,...,0, 1, 1, 1, 0,...,0] with 3-block at positions n-2, n-1, n, length 2n-1."""
    if n < 2:
        return None
    c = [0] * (2 * n - 1)
    c[n - 2] = 1
    c[n - 1] = 1
    c[n] = 1
    return c

print("s(n) = rule30_{n-1}(t_n) verification:")
for n in range(2, 12):
    t = three_cell_input(n)
    val = rule30_n_center(t, n - 1)
    print(f"  n={n}: rule30_{{n-1}}(t_n) = {val}, s(n) = {seq[n]} {'OK' if val == seq[n] else 'FAIL'}")

print("\nNow checking: does rule30_{n-1} on t_n = rule30_{n-2} on something?")
print("After 1 more step from t_n:")
for n in range(3, 10):
    t = three_cell_input(n)  # length 2n-1
    mid2 = apply_one_step(t)  # length 2n-3
    # Compare with t_{n-1} (length 2(n-1)-1 = 2n-3)
    tn1 = three_cell_input(n - 1)
    match = mid2 == tn1
    print(f"  n={n}: step(t_n) = {mid2}")
    if tn1:
        print(f"         t_{{n-1}} = {tn1}")
        print(f"         match: {match}")

    # More importantly: can we just keep going? Is step(t_n) always t_{n-1}?
    if not match and tn1:
        diff = [(i, mid2[i], tn1[i]) for i in range(len(mid2)) if mid2[i] != tn1[i]]
        print(f"         Differ at: {diff}")
    print()

print("\nFINAL SUMMARY:")
print("=" * 60)
print(f"Sequence s(0..50): {seq}")
print(f"Linear complexity: {L} (out of 51)")
print(f"s(n) XOR pattern (run-length): ", end="")
rle = []
curr = seq[0]
count = 1
for v in seq[1:]:
    if v == curr:
        count += 1
    else:
        rle.append(f"{curr}×{count}")
        curr = v
        count = 1
rle.append(f"{curr}×{count}")
print(", ".join(rle))
