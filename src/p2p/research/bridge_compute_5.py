#!/usr/bin/env python3
"""bridge_compute_5.py — Pattern analysis of k=n sensitivity for e_n, and reduction test.

Three tasks:
1. For n=1..30: check whether k=n is sensitive for e_n (extend Attack 3)
2. Pattern analysis: is the sensitivity sequence related to s(n), PTM, or something else?
3. Reduction test: for each n where e_n is NOT sensitive at k=n, find c such that
   rule30_n(c) = s(n) AND rule30_n(flip(c,n)) != s(n)

Rule 30: new[i] = old[i-1] XOR (old[i] OR old[i+1])
e_n = all zeros except position n = 1, tape length 2n+1.
"""

def rule30_step(tape):
    n = len(tape)
    out = []
    for i in range(n):
        l = tape[i-1] if i > 0 else 0
        c = tape[i]
        r = tape[i+1] if i < n-1 else 0
        out.append(l ^ (c | r))
    return out

def rule30_n(tape, n_steps):
    t = list(tape)
    for _ in range(n_steps):
        t = rule30_step(t)
    return t[len(t)//2]

def make_en(n):
    t = [0] * (2*n + 1)
    t[n] = 1
    return t

def flip(tape, k):
    t = list(tape)
    t[k] ^= 1
    return t

def s(n):
    if n == 0:
        return 1
    return rule30_n(make_en(n), n)

# ── Task 1: k=n sensitivity for n=1..30 ──────────────────────────────────────
print("=" * 60)
print("TASK 1: k=n sensitivity for e_n, n=1..30")
print("=" * 60)
print(f"{'n':>3}  {'s(n)':>4}  {'k=n?':>6}  {'|S_n|':>6}  {'S_n (first 8)':}")
print("-" * 60)

kn_seq = []   # 1 if k=n sensitive, else 0
sn_seq = []
scounts = []

for n in range(1, 31):
    en = make_en(n)
    base = rule30_n(en, n)
    sn_seq.append(base)
    kn_s = 1 if rule30_n(flip(en, n), n) != base else 0
    kn_seq.append(kn_s)
    S_n = [k for k in range(2*n+1) if rule30_n(flip(en, k), n) != base]
    scounts.append(len(S_n))
    tag = "YES" if kn_s else " no"
    print(f"{n:>3}  {base:>4}  {tag:>6}  {len(S_n):>6}  {S_n[:8]}")

print()
print(f"k=n sens  (n=1..30): {''.join(str(x) for x in kn_seq)}")
print(f"s(n)      (n=1..30): {''.join(str(x) for x in sn_seq)}")

# ── Task 2: Pattern analysis ──────────────────────────────────────────────────
print()
print("=" * 60)
print("TASK 2: Pattern analysis")
print("=" * 60)

def thue_morse(n): return bin(n).count('1') % 2

ptm    = [thue_morse(n) for n in range(1, 31)]
parity = [n % 2 for n in range(1, 31)]
sn_lag = [1] + sn_seq[:-1]  # s(n-1), with s(0)=1

def agree(a, b): return sum(x == y for x,y in zip(a,b))

print(f"Agree s(n):        {agree(kn_seq, sn_seq)}/30 = {agree(kn_seq,sn_seq)/30:.3f}")
print(f"Agree NOT s(n):    {agree(kn_seq, [1-x for x in sn_seq])}/30 = {agree(kn_seq,[1-x for x in sn_seq])/30:.3f}")
print(f"Agree n%2:         {agree(kn_seq, parity)}/30 = {agree(kn_seq,parity)/30:.3f}")
print(f"Agree PTM:         {agree(kn_seq, ptm)}/30 = {agree(kn_seq,ptm)/30:.3f}")
print(f"Agree s(n-1):      {agree(kn_seq, sn_lag)}/30 = {agree(kn_seq,sn_lag)/30:.3f}")
print(f"Agree s(n) XOR n%2:{agree(kn_seq,[a^b for a,b in zip(sn_seq,parity)])}/30 = {agree(kn_seq,[a^b for a,b in zip(sn_seq,parity)])/30:.3f}")

# Cross-tabulation: s(n) vs k=n sensitivity
c11 = sum(1 for a,b in zip(kn_seq,sn_seq) if a==1 and b==1)
c10 = sum(1 for a,b in zip(kn_seq,sn_seq) if a==1 and b==0)
c01 = sum(1 for a,b in zip(kn_seq,sn_seq) if a==0 and b==1)
c00 = sum(1 for a,b in zip(kn_seq,sn_seq) if a==0 and b==0)
print(f"\nCross-tab (sensitive vs s(n)):")
print(f"  sens+s=1:{c11}  sens+s=0:{c10}  non+s=1:{c01}  non+s=0:{c00}")

# Does s(n)=1 => k=n sensitive? (i.e. c01 == 0?)
if c01 == 0:
    print(f"  *** s(n)=1 => k=n ALWAYS sensitive (for n=1..30)! ***")
elif c01 <= 2:
    print(f"  *** s(n)=1 => k=n sensitive with {c01} exceptions in n=1..30 ***")
    exceptions = [n for n in range(1,31) if kn_seq[n-1]==0 and sn_seq[n-1]==1]
    print(f"  Exceptions: n={exceptions}")
else:
    print(f"  s(n)=1 does NOT imply k=n sensitive ({c01} counterexamples)")

# Does s(n)=0 => k=n non-sensitive?
if c10 == 0:
    print(f"  *** s(n)=0 => k=n NEVER sensitive (for n=1..30)! ***")
else:
    sens_when_zero = [n for n in range(1,31) if kn_seq[n-1]==1 and sn_seq[n-1]==0]
    print(f"  s(n)=0 but k=n sensitive at n={sens_when_zero}")

# When k=n non-sensitive: is rule30_n(all-zeros) = s(n)?
print(f"\nNon-sensitive at k=n: rule30_n(zeros) == s(n)?")
for n in range(1,31):
    if kn_seq[n-1] == 0:
        z = rule30_n([0]*(2*n+1), n)
        if z != sn_seq[n-1]:
            print(f"  n={n}: zeros gives {z}, s(n)={sn_seq[n-1]} -- DIFFERS!")
        # else: confirm silently (expected: zeros -> 0, and s(n)=0 when non-sensitive)
        else:
            pass
print("  (All non-sensitive n: rule30_n(zeros)=s(n) confirmed if no DIFFERS above)")

# Sensitive/non-sensitive indices
sens_idx = [n for n in range(1,31) if kn_seq[n-1]==1]
nonsens_idx = [n for n in range(1,31) if kn_seq[n-1]==0]
print(f"\nSensitive n: {sens_idx}")
print(f"Non-sens  n: {nonsens_idx}")
diffs = [sens_idx[i+1]-sens_idx[i] for i in range(len(sens_idx)-1)]
print(f"Gaps between sensitive n: {diffs}")

# ── Task 3: Reduction test ────────────────────────────────────────────────────
print()
print("=" * 60)
print("TASK 3: Reduction test")
print("=" * 60)
print("For non-sensitive n: find c with rule30_n(c)=s(n) AND flip at k=n changes output.")

import random
random.seed(42)

found_count = tested = 0
for n in range(1, 21):
    if kn_seq[n-1] == 1:
        continue  # already sensitive at e_n, skip
    base = sn_seq[n-1]
    tape_len = 2*n+1
    tested += 1
    found = None
    for attempt in range(3000):
        c = [random.randint(0,1) for _ in range(tape_len)]
        if rule30_n(c, n) != base:
            continue
        if rule30_n(flip(c, n), n) != base:
            found = c
            break
    if found:
        found_count += 1
        ones = [k for k,v in enumerate(found) if v==1]
        print(f"  n={n:>2} s(n)={base}: witness found (try {attempt+1}), 1s@{ones}")
    else:
        print(f"  n={n:>2} s(n)={base}: NO witness in 3000 tries")

print(f"\nFound {found_count}/{tested} witnesses for non-sensitive n")

# ── Summary ───────────────────────────────────────────────────────────────────
print()
print("=" * 60)
print("SUMMARY")
print("=" * 60)
print(f"k=n sensitivity: {''.join(str(x) for x in kn_seq)}")
print(f"s(n) sequence:   {''.join(str(x) for x in sn_seq)}")
print(f"Match: {agree(kn_seq,sn_seq)}/30")
print()
print("Key conjecture to test: s(n)=1 <=> k=n sensitive?")
print(f"  s(n)=1 and k=n sensitive: {c11}")
print(f"  s(n)=1 and k=n non-sens:  {c01}  <-- must be 0 for conjecture to hold")
print(f"  s(n)=0 and k=n sensitive: {c10}  <-- must be 0 for conjecture to hold")
print(f"  s(n)=0 and k=n non-sens:  {c00}")
