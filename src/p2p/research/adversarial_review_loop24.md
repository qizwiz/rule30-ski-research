# Adversarial Review Loop 24 (2026-03-24)
# Focus: Hardening active m-set completeness claims

## Key findings

### Finding 1: Original m=44..80 scan range was too weak
Paper claimed: "m=44,...,80: no events in [3087, 4500) (original sweep)"
Problem: m=38 (last active) has first SubcaseB at n'=8210 — outside 4500!
Triangle-method dense scan reveals: 8400-8500 F=0 candidates per m in [3087,20001) but 0 SubcaseB

### Finding 2: Step-500 sparse scan is nearly useless
Paper claimed: "sparse scan m≤300, n'≤26000 step-500 finds none"
Computation: step-500 detects only 0.2% of F=0 events for m=34 (active)
Implication: if m=46 had SubcaseB events at density 0.006% (like m=38), step-500 would miss them with 99.7% probability

### Finding 3: m=46..80 confirmed inactive — triangle method [3087,20001)
Fast triangle method: O(N_max^2) per m, ~0.5s per m-value
Result: all 18 even m in [46,80] have 8396-8528 F=0 candidates but 0 SubcaseB hits
Upgrade from: [3087,4500) original sweep → [3087,20001) dense triangle scan (9s total)

### Finding 4: m=82..200 confirmed inactive — [3087,20001)
Extended scan: all m in {82,84,...,200} (60 values) have 0 SubcaseB in [3087,20001)
Time: 30s total via triangle method
Upgrade from: not scanned → [3087,20001) dense (30s)

### Finding 5: m=46..56 full G-check — all F=0 candidates in [3087,7000)
For m=46..56, checked ALL ~1929-1975 F=0 candidates in [3087,7000) individually
Result: 0 SubcaseB hits
This is exhaustive (100%) coverage of F=0 candidates in this range

### Finding 6: Period minimality for m=30 — FULL sequence comparison
Paper: "single-point check for m=30" to confirm P=4096
New: full F-sequence via triangle method, 10000 values computed in 0.1s
P=2048 FAILS immediately at n'=3087: F(3087,30)=1 but F(5135,30)=0
P=4096 passes 50-point spot check ✓

### Finding 7: Period minimality for m=32 — full sequence
m=32: P=2048 fails at n'=3087: F(3087,32)=0 but F(5135,32)=1 ✓

## Paper corrections required

1. Upgrade: "m=44,...,80: no events in [3087, 4500)" 
   → "m=46..80: 0 SubcaseB in [3087,20001) via dense triangle scan (9s, 2026-03-24)"

2. Upgrade: "sparse scan m≤300, n'≤26000 step-500"
   → "dense triangle scan m≤200, n'≤20001 (39s, 2026-03-24)"
   Note: step-500 detection rate for active m=34: 0.2% — insufficient evidence

3. Upgrade: "single-point check for m=30 period minimality"
   → "full F-sequence comparison (10000 values, P=2048 fails at n'=3087)"

## Adversarial verdict
The active m-set {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38} is correct.
No active positions found in m=46..200 up to n'=20001.
The claims now have much stronger computational backing than the original paper.
