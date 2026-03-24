#!/usr/bin/env python3
"""
Loop 16 adversarial review computations.
Target: confirm/deny m=40 active status.
"""

import sys

def step_rule30(state, mask):
    l = (state << 1) & mask
    r = (state >> 1)
    return (l ^ (state | r)) & mask

def compute_FG(n_prime, m):
    size = 2 * n_prime + 3
    center = n_prime + 1
    last = 2 * n_prime + 2
    mask = (1 << size) - 1
    state_f = (1 << m) & mask
    state_g = ((1 << m) | (1 << last)) & mask
    for _ in range(n_prime + 1):
        state_f = step_rule30(state_f, mask)
        state_g = step_rule30(state_g, mask)
    F = (state_f >> center) & 1
    G = (state_g >> center) & 1
    return F, G

def scan_range(m, start, stop, step=1, show_all_hits=True):
    """Scan n' in [start, stop) with given step. Return list of (n', F, G) for non-(0,0) and non-(1,1)."""
    hits = []
    for np in range(start, stop, step):
        F, G = compute_FG(np, m)
        if F != G:  # non-trivial
            hits.append((np, F, G))
    return hits

def check_point(n_prime, m):
    F, G = compute_FG(n_prime, m)
    return F, G

results = []
log = results.append

log("=" * 70)
log("LOOP 16: m=40 STATUS — Adversarial Review of 'active set terminates at m=38'")
log("=" * 70)
log("")

# ---- Task 1: Check resonant n' = 16403 for m=40 ----
log("TASK 1: Check n'=16403 for m=40 (resonant position under doubling law)")
log("  Resonance prediction: if m=40 period = 2^16 = 65536,")
log("  first (0,1) should be where last-m = 2^15 = 32768,")
log("  i.e., 2n'+2-40 = 32768 => n' = (32768+40-2)/2 = 32806/2 = 16403")
F, G = check_point(16403, 40)
log(f"  n'=16403, m=40: F={F}, G={G}  => ({F},{G})")
if (F, G) == (0, 1):
    log("  *** ACTIVE: SubcaseB hit at resonant position! ***")
elif (F, G) == (1, 0):
    log("  (1,0): non-trivial but not SubcaseB")
else:
    log("  Trivial (both equal): no hit at resonant position")
log("")

# ---- Task 2: Dense scans around key positions ----
log("TASK 2: Dense scans for m=40")
log("")

log("  2a. Dense [3087, 5000) step 1 for m=40:")
hits_2a = scan_range(40, 3087, 5000, step=1)
if hits_2a:
    for np, F, G in hits_2a:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits.")
log("")

log("  2b. Dense [8190, 8220) step 1 for m=40  (around m=38's first (0,1) region):")
hits_2b = scan_range(40, 8190, 8220, step=1)
if hits_2b:
    for np, F, G in hits_2b:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits.")
log("")

log("  2c. Dense [16390, 16420) step 1 for m=40  (around resonant n'=16403):")
hits_2c = scan_range(40, 16390, 16420, step=1)
if hits_2c:
    for np, F, G in hits_2c:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits.")
log("")

log("  2d. Dense [32780, 32820) step 1 for m=40  (around 2^15=32768 resonance):")
hits_2d = scan_range(40, 32780, 32820, step=1)
if hits_2d:
    for np, F, G in hits_2d:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits.")
log("")

log("  2e. Dense [36880, 36900) step 1 for m=40  (around known (1,0) at n'=36887):")
hits_2e = scan_range(40, 36880, 36900, step=1)
if hits_2e:
    for np, F, G in hits_2e:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits.")
log("")

log("  2f. Sparse [3087, 100000) step 50 for m=40  (broad coverage):")
hits_2f = scan_range(40, 3087, 100000, step=50)
if hits_2f:
    log(f"    {len(hits_2f)} hits found:")
    for np, F, G in hits_2f:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits in [3087,100000) step-50.")
log("")

# ---- Task 3: Find next (1,0) after 36887 for m=40 ----
log("TASK 3: Find next (1,0) after n'=36887 for m=40 (to determine period)")
log("")

log("  3a. Dense [36888, 40000) step 1 for m=40:")
hits_3a = scan_range(40, 36888, 40000, step=1)
if hits_3a:
    for np, F, G in hits_3a:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
    # Try to determine period
    all_10_hits = [(36887, 1, 0)] + hits_3a
    log(f"    First hit after 36887: n'={hits_3a[0][0]}, gap={hits_3a[0][0]-36887}")
else:
    log("    No hits in [36888, 40000). Period > 3113, or 36887 is an isolated event.")
log("")

log("  3b. Check [3087+65536, 3087+65536+1000) = [68623, 69623) step 1 for m=40")
log("      (Testing period=65536 hypothesis: next occurrence of 36887's type would be at 36887+65536=102423)")
log("      Instead check 3087+65536=68623 to see if period-shifted from 3087 pattern):")
start_3b = 3087 + 65536
hits_3b = scan_range(40, start_3b, start_3b + 1000, step=1)
if hits_3b:
    for np, F, G in hits_3b:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log(f"    No hits in [{start_3b}, {start_3b+1000}).")
log("")

log("  3c. Check wide sparse [40000, 110000) step 100 for m=40:")
hits_3c = scan_range(40, 40000, 110000, step=100)
if hits_3c:
    log(f"    {len(hits_3c)} hits:")
    for np, F, G in hits_3c:
        log(f"    n'={np}: ({F},{G})  last-m={2*np+2-40}")
else:
    log("    No hits in [40000, 110000) step-100.")
log("")

# ---- Task 4: m=42 and m=44 in [3087, 100000) step 50 ----
log("TASK 4: m=42 and m=44 in [3087, 100000) step 50")
log("")

for m_test in [42, 44]:
    hits = scan_range(m_test, 3087, 100000, step=50)
    if hits:
        log(f"  m={m_test}: {len(hits)} hits:")
        for np, F, G in hits:
            log(f"    n'={np}: ({F},{G})  last-m={2*np+2-m_test}")
    else:
        log(f"  m={m_test}: NO hits in [3087, 100000) step-50.")
log("")

# ---- Task 5: Analyze (1,0) at n'=36887 for m=40 ----
log("TASK 5: Geometric analysis of m=40's (1,0) at n'=36887")
log("")
np_hit = 36887
last_m = 2 * np_hit + 2 - 40
log(f"  n'={np_hit}, m=40: last-m = 2*{np_hit}+2-40 = {last_m}")
log(f"  {last_m} = ?")
# Decompose
v = last_m
for p in [2, 3, 5, 7, 11, 13]:
    count = 0
    while v % p == 0:
        v //= p
        count += 1
    if count:
        log(f"    divisible by {p}^{count}")
log(f"    remainder after factoring: {v}")
log(f"  In powers of 2: {last_m} = 2^16 + 2^13 + 8 = {65536+8192+8} (check: {65536+8192+8==last_m})")
log(f"  Not a clean power of 2. Compare m=38's (1,0) at n'=4118: last-m = {2*4118+2-38} = 8200 = 2^13+8")
log(f"  And m=36's first hit at n'=4113: last-m = {2*4113+2-36}")
log(f"  m=38's first (0,1) at n'=8210: last-m = {2*8210+2-38} = 16384 = 2^14 (resonance!)")
log("")

# ---- Additional: verify known m=38 hits are still correct ----
log("TASK 6: Spot-check m=38 hits (sanity check)")
m38_expected = [(4118, 1, 0), (8210, 0, 1), (8214, 0, 1), (12310, 1, 0)]
for np, eF, eG in m38_expected:
    F, G = check_point(np, 38)
    status = "OK" if (F == eF and G == eG) else f"MISMATCH! got ({F},{G})"
    log(f"  n'={np}, m=38: ({F},{G}) expected ({eF},{eG}): {status}")
log("")

# ---- Summary ----
log("=" * 70)
log("SUMMARY")
log("=" * 70)
log("")

active_40 = any(G == 1 and F == 0 for _, F, G in hits_2a + hits_2b + hits_2c + hits_2d + hits_2e + hits_2f + hits_3a + hits_3b + hits_3c)
any_hit_40 = any(F != G for _, F, G in hits_2a + hits_2b + hits_2c + hits_2d + hits_2e + hits_2f + hits_3a + hits_3b + hits_3c)

if active_40:
    log("m=40 STATUS: ACTIVE (SubcaseB (0,1) hit found)")
    all_01_hits = [(np, F, G) for np, F, G in hits_2a + hits_2b + hits_2c + hits_2d + hits_2e + hits_2f + hits_3a + hits_3b + hits_3c if F == 0 and G == 1]
    log(f"  First (0,1) at n'={min(np for np,_,_ in all_01_hits)}")
else:
    log("m=40 STATUS: NO (0,1) found in scans")
    if any_hit_40:
        all_10_hits = [(np, F, G) for np, F, G in hits_2a + hits_2b + hits_2c + hits_2d + hits_2e + hits_2f + hits_3a + hits_3b + hits_3c if F == 1 and G == 0]
        log(f"  But (1,0) hits exist: {[np for np,_,_ in all_10_hits]}")
        log("  Classification: WEAKLY INACTIVE (tentative — scan is not exhaustive)")
    else:
        log("  No non-trivial hits at all in sparse coverage")
        log("  Classification: likely STRICTLY INACTIVE (F=G pattern)")

log("")
log("Scans performed:")
log(f"  Dense [3087,5000) step-1: {len(hits_2a)} hits")
log(f"  Dense [8190,8220) step-1: {len(hits_2b)} hits")
log(f"  Dense [16390,16420) step-1: {len(hits_2c)} hits")
log(f"  Dense [32780,32820) step-1: {len(hits_2d)} hits")
log(f"  Dense [36880,36900) step-1: {len(hits_2e)} hits")
log(f"  Sparse [3087,100000) step-50: {len(hits_2f)} hits")
log(f"  Dense [36888,40000) step-1: {len(hits_3a)} hits")
log(f"  Dense [{start_3b},{start_3b+1000}) step-1: {len(hits_3b)} hits")
log(f"  Sparse [40000,110000) step-100: {len(hits_3c)} hits")
log("")
log("m=42 sparse [3087,100000) step-50: any hits: " + ("YES" if any(scan_range(42, 3087, 100000, step=50)) else "NO"))
log("m=44 sparse [3087,100000) step-50: any hits: " + ("YES" if any(scan_range(44, 3087, 100000, step=50)) else "NO"))

output = "\n".join(results)
print(output)

with open("/Users/jonathanhill/src/p2p/research/loop16_m40_status.txt", "w") as f:
    f.write(output)
    f.write("\n")

print("\nResults saved to loop16_m40_status.txt")
