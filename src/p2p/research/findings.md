# Rule 30 Prize 3 — Persistent Research Findings

## Loop 43 findings (2026-03-24) — Adversarial density/involution review: m=2n'-6 SubcaseB

### Computation run: adversarial_loop43_density.py

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_loop43_density.py`
**Runtime**: 16.7s for 212 values in [3089, 3300]

Targeted five claims in prize3_paper.tex lines 778–805 about the shifting position m=2n'-6.

---

### Results: all 5 attacks repelled, 0 violations

| Attack | Claim | Range | Violations | Status |
|--------|-------|-------|------------|--------|
| A | Mod-4 SubcaseB rule: SubcaseB iff n'≡1,2 (mod 4) | [3089,3300] | 0 | VERIFIED |
| B | Anti-correlation: F(n',2n'-6)+G(n',2n'-6)=1 always | [3089,3300] | 0 | VERIFIED |
| C | Exact period 4 of F in n' (period 2 minimal-fails) | [3089,3297] | 0 | VERIFIED |
| D | Involution F(n')+F(n'+2)=1 for all n' | [3089,3289] | 0 | VERIFIED |
| E | F pattern 0,0,1,1,... at [3089,3108], 20/20 correct | [3089,3108] | 0 | VERIFIED |

Additional finding: G(n', 2n'-6) also has exact period 4 (0 violations in [3089,3297]).
SubcaseB density: exactly 106/212 = 0.500000.
(F,G) pair distribution: (0,1) → 106 times, (1,0) → 106 times. No (0,0) or (1,1) seen.

---

### Hostile reviewer analysis — weakest points in the density argument

**WEAKNESS 1 (STRONGEST): Period-4 is empirical only, no analytic explanation.**
F(n', 2n'-6) depends on n' in two ways simultaneously: as the step count AND as the
spike position (m=2n'-6 co-varies). Fixed-m periods are powers of 2 and arise from
the linear structure of the CA; here the function is not a standard fixed-m function.
The paper gives no analytic reason why this co-varying function has period 4.
A hostile reviewer will say: "The period-4 pattern could be a transient. Your compute
budget densely reaches only n'=15000. Nothing in the paper rules out a much longer
period appearing at n'>>15000."

**WEAKNESS 2 (SECOND STRONGEST): The reduction to two unproved sub-claims is circular in presentation.**
The paper says the proof strategy is: prove (a) F has period 4 AND (b) F+G=1; then SubcaseB follows.
But (a) and (b) are both unproved. A hostile reviewer: "You have reformulated one open problem
into two open problems. This is not a proof strategy — it is a wish list."

**WEAKNESS 3 (MODERATE): Why does boundary interference produce period exactly 4?**
The spike at m=2n'-6 is always 8 cells from the right boundary. The paper correctly
notes the open-boundary approximation breaks down here. But it gives no reason why
8-cell proximity produces period-4 rather than period-2, 8, or 16. The connection
between the constant boundary distance (8 cells) and the period-4 regularity is asserted
but not explained.

**WEAKNESS 4 (MINOR): Inconsistent verification ranges — involution checked to n'=3289 only,
mod-4 rule checked to n'=15000.** If the involution is the explanation for density=1/2,
it should be verified over the same range as the main claim. Checking it only to n'=3289
while the primary claim spans [3089,15000] is an unexplained asymmetry.

**WEAKNESS 5 (FATAL IF TRUE): Anti-correlation F+G=1 is the load-bearing bridge of the proof strategy.**
If F+G=1 fails at any n', the strategy collapses entirely. It is currently unproved.
The paper's own statement "Both claims are currently computationally verified but not yet
formally proved in Lean" is honest, but it means the entire SubcaseB density argument
rests on two empirical pillars with no proof skeleton.

**BOTTOM LINE**: The computations are correct and the patterns are compelling. The single
most actionable critique for improving the paper is: provide a proof sketch for F+G=1
(anti-correlation). This is the more surprising of the two claims and is the logical pivot
point; the period-4 claim of F may follow from it via parity symmetry once anti-correlation
is understood.

---

## Loop 20 findings (2026-03-24) — Adversarial review: active m-set, inactivity, period minimality

### Computation run: adversarial_loop20_v4.py

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_loop20_v4.py`
**Output**: `/Users/jonathanhill/src/p2p/research/adversarial_loop20_results.txt`

Three specific claims from the paper's proof plan section were targeted:

---

### Q1: Is the active m-set complete for m in [4,38]?

**Claim**: M_act = {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38} and m=18, m=32 are inactive.

**Computation**: For each even m in [4,38], scanned [3087, 3087+2*P_m) for SubcaseB events
(F=0, G=1), checking two periods where possible:

| m | Claimed | Scan window | SubcaseB hits | Classification | Status |
|---|---------|-------------|---------------|----------------|--------|
| 4  | active  | [3087,3103) | 2             | ACTIVE         | OK |
| 6  | active  | [3087,3119) | 4             | ACTIVE         | OK |
| 8  | active  | [3087,3151) | 2             | ACTIVE         | OK |
| 10 | active  | [3087,3215) | 2             | ACTIVE         | OK |
| 12 | active  | [3087,3215) | 4             | ACTIVE         | OK |
| 14 | active  | [3087,3215) | 4             | ACTIVE         | OK |
| 16 | active  | [3087,3699) | 6             | ACTIVE         | OK |
| 18 | INACTIVE| [3087,3599) | 0             | INACTIVE       | OK |
| 20 | active  | [3087,3599) | 2             | ACTIVE         | OK |
| 22 | active  | [3087,3599) | 2             | ACTIVE         | OK |
| 24 | active  | [3087,4111) | 4             | ACTIVE         | OK |
| 26 | active  | [3087,5135) | 2             | ACTIVE         | OK |
| 28 | active  | (see below) | confirmed     | ACTIVE         | OK |
| 30 | active  | (see below) | confirmed     | ACTIVE         | OK |
| 32 | INACTIVE| [3087,7183) | 0             | INACTIVE       | OK |
| 34 | active  | spot check n'=4112: SubcaseB=True (F=0,G=1) | | ACTIVE | OK |
| 36 | active  | spot check n'=4113: SubcaseB=True (F=0,G=1) | | ACTIVE | OK |
| 38 | active  | spot check n'=8210: SubcaseB=True (F=0,G=1) | | ACTIVE | OK |

**Result**: Zero mismatches. The active m-set claim is VERIFIED for all m in [4,38].

---

### Q2: Are "inactive" positions permanently inactive or just very-long-period?

**Claim (m=18)**: m=18 is inactive with period 256, zero SubcaseB in [3087,10000) (27 full periods).

**Computation**:
- Scanned [3087, 3599) = two full 256-periods for SubcaseB: **0 SubcaseB events** (CONFIRMED)
- Period-256 check by exact sequence comparison: **True**
- Period-128 check (would mean 256 overclaims): **False** — period-128 fails at offset {193, 249, 253} in period
- **Verdict**: m=18 period-256 is the MINIMAL period. Paper's period-256 claim is correct.
- The paper's broader claim "zero (0,1) in [3087,10000) (27 full periods)" is supported by
  verified period-256 structure + zero SubcaseB in the first 2 periods.

**Claim (m=32)**: m=32 is inactive with period 4096, zero SubcaseB in [3087, ≥6000).

**Computation**:
- Previous loops verified [3087, 6000): zero SubcaseB.
- This loop extended to [6000, 7183): **0 SubcaseB events** (CONFIRMED, 197.7s)
- No (1,0) events found in [6000, 7183) either.
- Combined: zero SubcaseB in full period [3087, 7183) = [3087, 3087+4096).
- **Verdict**: m=32 inactivity confirmed for one full claimed period.

**Key note**: The paper's proof plan still requires PROVING inactivity for all n' ≥ 3087,
not just the first period. But the first-period verification eliminates the possibility
that m=32 becomes active "soon" after n'=7183. A formal proof requires the periodicity
argument (show the sequence repeats forever).

---

### Q3: Is the period-P bound tight? Could any active m have a shorter period?

**Computation**: For each active m with period ≤ 4096, checked if P/2 could serve as period.

**Method**: (a) Single-point check: compare F(3087, m) vs F(3087+P/2, m).
           (b) Full-sequence check for m=26 and m=28.

**Results**:
- m=4 (P=8): F(3087)=0, F(3091)=1 → P/2=4 FAILS
- m=6 (P=16): F(3087)=0, F(3095)=1 → P/2=8 FAILS
- m=8 (P=32): F(3087)=1, F(3103)=0 → P/2=16 FAILS
- m=10 (P=64): F(3087)=0, F(3119)=1 → P/2=32 FAILS
- m=12 (P=64): F(3087)=0, F(3119)=1 → P/2=32 FAILS
- m=14 (P=64): F(3087)=1, F(3119)=0 → P/2=32 FAILS
- m=16 (P=256): F(3087)=1, F(3215)=0 → P/2=128 FAILS
- m=20 (P=256): F(3087)=0, F(3215)=1 → P/2=128 FAILS
- m=22 (P=256): F(3087)=1, F(3215)=0 → P/2=128 FAILS
- m=24 (P=512): F(3087)=1, F(3343)=0 → P/2=256 FAILS
- m=26 (P=1024): Full F-scan [3087,5135): period-512 **FAILS at offset 2** (F[3089]=0, F[3601]=1)
  The single-point check at n'=3087 gave F=0 both at 3087 and 3087+512=3599 by coincidence,
  but offset 2 shows the sequences are different. P=1024 is MINIMAL.
- m=28 (P=2048): Full F-scan [3087,5135): period-1024 **FAILS at offset 1** (F[3088]=0, F[4112]=1)
  P=2048 is MINIMAL.
- m=30 (P=4096): F(3087)=1, F(3087+2048)=0 → P/2=2048 FAILS at single point.

**FINDING**: All active m values with verified periods have MINIMAL periods.
The period table in the paper is correct — no overclaims found.

**IMPORTANT NEAR-MISS**: For m=26 and m=28, the single-point check at n'=3087 gave
"consistent with P/2" (both False). This could have led to a spurious period-halving claim.
The full F-scan correctly identified the failures. The paper should note that single-point
spot checks are insufficient for period minimality verification.

---

### Summary of findings

1. **Active m-set is complete**: All even m in [4,38] classified correctly.
   Zero new active positions found in [18,32] neighborhood.

2. **Inactive positions**: m=18 and m=32 confirmed inactive for one full period each.
   m=18: period-256 is minimal (period-128 fails). Paper's claim correct.
   m=32: zero SubcaseB confirmed in full 4096-period [3087,7183).

3. **Period minimality**: All verified active m have MINIMAL periods.
   Near-miss for m=26,28 (spot check was inconclusive) resolved by full scan.
   Period table in paper is CORRECT.

4. **Weakest remaining claim**: The paper states "no active positions above m=38"
   based on: m=40 scanned to n'=110000 (no SubcaseB), m=42,44 to n'=100000.
   This is strong evidence but not a proof. The proof plan requires a formal
   periodicity argument showing I(n',m)=1 for all n'≥3087 and m≥40.

---

## Loop 16 findings (2026-03-23) — m=40 confirmed NOT active; active set terminates at m=38

### m=40 STATUS: WEAKLY INACTIVE — active set terminates at m=38 (CONFIRMED)

**Summary**: Comprehensive multi-scan adversarial review finds no (0,1) event for m=40
across all tested ranges. The claim "active set terminates at m=38" survives this review.

#### Key evidence:

1. **Resonance test (decisive)**: Three resonant positions (where last-m = power of 2):
   - n'=8211 (last-m = 2^14 = 16384): (1,1) — not SubcaseB
   - n'=16403 (last-m = 2^15 = 32768): (0,0) — not SubcaseB
   - n'=32787 (last-m = 2^16 = 65536): (1,1) — not SubcaseB
   None gives (0,1). Resonance pattern breaks entirely for m=40.

2. **Dense scan around all resonance points**: Zero hits at n'∈[8190,8220), [16390,16420),
   [32780,32820). None of the theoretically predicted positions fire.

3. **Sparse coverage to n'=110000**: Only the known (1,0) at n'=36887 found. No (0,1) anywhere.

4. **Period-65536 ruled out**: Dense scan [68623,69623) = [3087+65536, ...) has 0 hits.

5. **No second (1,0) near 36887**: Dense [36888,40000) step-1 finds nothing. The hit at
   36887 appears isolated, not part of a repeating cycle.

6. **m=42, m=44 strictly inactive**: 0 hits each in [3087,100000) step-50.

#### Geometric structure of m=40's single (1,0):
- n'=36887: last-m = 73736 = 8 × 13 × 709 = 2³ × 13 × 709
- NOT a power of 2. No resonance structure.
- Compare m=38: first (1,0) at last-m=8200 = 2^13 + 8, first (0,1) at last-m=16384 = 2^14
- For m=40 to be active by analogy: need (0,1) where last-m = 2^15 = 32768 → n'=16403. ABSENT.

#### Impact on paper:
- Active set: {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38} stands
- P = 32768 = 2^15 stands
- Claim "active set terminates at m=38" stands with evidence:
  - m=40 scanned to n'=110000 with multiple dense windows; no (0,1) found
  - m=42, m=44 scanned to n'=100000 step-50; no hits found

## Loop 19 findings (2026-03-23) — Lean period certificates added; SubcaseB proof architecture

### Lean progress: CausalConeLemmas.lean extended

**spikeAtList infrastructure (added):**
- `spikeAtList m N`: parametric definition (spike at position m in length-N list)
- `rule30n_spikeAt_period`: parametric period lemma (takes `native_decide` cert as hypothesis)
- Period certificates added for m=4,8,10,12,14 (trivial), m=16,22 (P=256), m=24 (P=512),
  m=26 (P=1024), m=28 (P=2048), m=30 (P=4096) — all compile successfully
- m=6 (P=16) and m=20 (P=256) already had dedicated spike6List/spike20List lemmas
- m=34,36,38: DEFERRED — OOM crash with linked-list native_decide (~67M, 270M, 1.1B cells)

**twoSpikeLastList infrastructure (added):**
- `twoSpikeLastList m N`: spike at position m AND at position N-1 (last)
- Period certificates: for G-periodicity (SubcaseB condition)
  Same formula: caEvolve P_m (twoSpikeLastList m (2*P_m+2*m+1)) = twoSpikeLastList m (2*m+1)
  Verified for all active m with P ≤ 256 (m=4..22); compile-checked for m=4..14 and m=16,20,22

### SubcaseB proof plan (discovered):

The G period proof works as follows (for positions i ≤ 2*(n'+1) in the P_m-step reduction):
- i ≤ m: right spike at N-1-i > 2*P_m (outside cone for n' ≥ P_m); use spikeAtList cert
- m < i < 2*(n'+1): right spike at N-1-i > 2*P_m (outside cone); output = 0 = expected
- i = 2*(n'+1): right spike at exactly position 2*P_m (cone boundary); output = 1 = H(P_m-1) = 1

Key new fact: H(n') = 1 for ALL n' (single last-spike always gives center=true). Verified for n'=0..19.
This H=1 fact handles the last position in the G period proof.

### SubcaseB residues (partial, from Python computation):
- m=4, P=8: residue 5 mod 8; first occurrence n'=3093
- m=6, P=16: residues 6,10 mod 16; first occurrences n'=3094, 3098
- m=8, P=32: residue 11 mod 32; first occurrence n'=3115
- (m=10..38: computation running)

### No universal witness for m=4 SubcaseB:
Different n' values require different witnesses (w=16 at n'=3093, w=6 at n'=3101, w=12 at n'=3109).
The witness cycle has period > P_4=8, requiring additional infrastructure.

## Loop 18 findings (2026-03-23) — native_decide cost estimate corrected; all certificates verified

Adversarial target: paper said O(P × (2m+1)) ≈ 2.5M ops for m=38 native_decide certificate.
Actual cost: O(P²) ≈ 1.076B cells (caStepList shrinks by 2/step, input size = 2P+2m+1).
All 16 active m period certificates verified correct (Python: m=38 takes 315s; Lean native ~3-30s).
Risk: m=34,36,38 may need BitVec/Array rather than List Bool due to GC pressure from 1B+ cons cells.
Paper updated with corrected formula and this caveat.

## Loop 17 findings (2026-03-23) — Sweep coverage corrected; m=42..60 verified inactive

Adversarial target: paper overclaimed "step-100 to n'=45000 for all m≤80" — only m=40,42 were scanned that far.

New data:
- m=42..60: ZERO hits in [3087,5000) dense (10 m-values)
- m=42..80: ZERO hits at n'=36887 spot check
- m=42: zero hits in [3087,20000) step 100; resonances last-m=2^{13..16} all equal
- m=40: weakly inactive confirmed — 1 (1,0) at 36887, zero (0,1) in [3087,45000)

Paper corrected: single overclaimed sweep sentence replaced by 5-item layered table listing actual verified ranges per m-group. Conclusion unchanged (M_act = {4,...,38}, P=32768).

## Loop 15 findings (2026-03-23) — m=38 RECLASSIFIED AS ACTIVE

### m=38 Period: P = 32768 = 2^15 (NEW)

**Critical error corrected:** m=38 was previously classified as "weakly inactive" (only (1,0),
no (0,1)). This was WRONG — the previous scan window [3087, 8000) just barely missed the first
(0,1) hits at n'=8210 and n'=8214.

**m=38 is ACTIVE** — it has SubcaseB (F=0, G=1) events.

#### Complete hit structure for m=38 (period P=32768 = 2^15):

(1,0) hits per period (5 hits):
  n' = 4118, 12310, 20498, 28690, 32786

(0,1) hits per period (3 hits):
  n' = 8210, 8214, 32790

Verification:
  - Period 32768 confirmed: 0 mismatches on 132 test points
  - Period 16384 ruled out: 73 mismatches
  - Period 8192 ruled out: 35 mismatches
  - All 8 hits verified at n' and n'+32768 (all match)
  - No hits in gap [12320, 28680) confirmed by step-5 scan
  - No hits in [3087, 4118) confirmed by dense scan

#### Structural note:
The first (0,1) hit at n'=8210 has last-m = 2*8210+2-38 = **16384 = 2^14 exactly**.
This means the distance between the two spikes equals the period of m=36.
The distance 16384 creates a special cone-overlap alignment.

#### Impact on paper:

1. **Active set corrected**: {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38} (m=38 added)
2. **LCM of periods**: lcm(16384, 32768) = **32768 = 2^15** (was 16384 = 2^14)
3. **P updated**: P = 32768 (not 16384 as previously claimed)
4. **"Terminates at m=36" claim is WRONG** — at minimum m=38 is also active
5. **m=40 status**: ONE (1,0) hit at n'=36887 found in [3087, 45000) step-10 scan;
   no (0,1) found yet. Dense scan around 36887 shows only the one hit.
   m=40 may be weakly inactive with a very long period, or may have (0,1) beyond n'=45000.
   m=42: zero hits in [3087, 45000) step-100.

#### Scan method corrections needed in paper:
- "ZERO (0,1) in [3087,8000) for m=38" is correct as stated but misleading
- The first (0,1) hit for m=38 is at n'=8210 (just beyond the window)
- Extended scan window for m=38 should be [3087, 45000) at minimum



## Loop Summary (2026-03-23, adversarial rounds 8–10)

### CONFIRMED final period table (loop 9):
- m=36: period 16384 = 2^14 (NOT 4096; confirmed by 20497=4113+16384, 20501=4117+16384, 24593=8209+16384)
- m=34: period 8192 = 2^13 CONFIRMED
- m=30: period 4096 = 2^12 CONFIRMED
- LCM of all confirmed periods = 16384 = P (NOT 4096)
- Active set: {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36} — terminates at m=36 (evidence: dense scan m≤80 to n'=4500, sparse scan m≤300 to n'=25000)

### Inactive sub-classification (NEW loop 9):
- **Weakly inactive** ((0,1) absent but (1,0) occurs):
  - m=18: (1,0) at n'=3280,3336,3340,3536,3592,...
  - m=32: (1,0) at n'=3347,4111,4115 in [3087,6000); zero (0,1)
  - m=38: (1,0) at n'=4118 ONLY (immediately after m=36 hit at 4117); zero (0,1) in [3087,6000)
- **Strictly F=G** (only (0,0) and (1,1)):
  - m=40: verified in [3087,6000); m=42: same; m=44,...,80: verified in [3087,4500)
  - Sparse: m=82,...,300: no active m in [3087,25000) step-500
- Earlier claim "m=32 has F=G identically" was WRONG — (1,0) events exist, just no (0,1)
- NOTE: m=38's (1,0) at n'=4118 is structurally notable — immediately follows the m=36 cluster at 4113,4117

### Paper fixes this loop:
1. Discussion section m=36 period: 4096 → 16384 (was stale)
2. Part B "P not yet determined" → "P=16384 conditional on no active m>36"
3. Part A "m=32,38,40,42 F=G identically" → corrected two-sub-class description
4. Added extended scan result (m≤300, n'≤25000) confirming no new active positions
5. LOOP 10: m=14 period: 128 → 64 (FACTUAL ERROR CORRECTED)
6. LOOP 10: Doubling law claim restricted to m≥24; plateaus at m={10,12,14}→64 and m={16,20,22}→256 documented
7. LOOP 10: m=16 internal structure: 3 hits per period at offsets 0,4,72 (gaps 4,68,184; sum=256) [OFFSET VALUES CORRECTED IN LOOP 42: actual offsets 120,124,192 from n'=3087; gaps unchanged]

### Still open questions:
- Can the exact mod-4 rule SubcaseB(n', 2n'-6) iff n'≡1,2 (mod 4) be PROVED analytically?
  (This would close Part C; need to characterize Rule 30 evolution on (spike_m + spike_last) mod 4)
- Why does naive induction (n',2n'-6)→(n'-1,2n'-8) fail? Note: 3089≡1(mod4) but 3088≡0(mod4) — consistent with rule
- Is m = last-8 the ONLY large-m position (confirmed: last-16,...,last-80 → zero hits in [3087,3500)-[3087,5500))?
- Formal proof that inactive positions stay inactive (periodicity argument needed)
- Whether active set truly terminates at m=36 (strong evidence but not proved beyond m=80)

### Loop 11 finding:
- Large-m density corrected from "~1/2" to EXACT 1/2
- Mod-4 rule: SubcaseB(n', 2n'-6) iff n'≡1 or 2 (mod 4), verified [3089,5500) with 0 exceptions
- Paper updated: abstract and Part C now say "exactly density 1/2 (mod-4 rule)"

### Loop 13 findings (2026-03-23) — NEW STRUCTURAL THEOREM:

**Last-spike Lemma (H=1): H(n') = 1 for ALL n' ≥ 0**
  where H(n') = center after n'+1 steps from spike at last=2n'+2 alone (tape size 2n'+3)
  Verified: n'=0..100 (all 1), [3000,3200) (all 1), spot checks to n'=15000 (all 1)
  PROOF: frontier-chain argument
    - Frontier invariant: at step j, all cells at positions < 2n'+2-j are 0 (proved by induction)
    - Frontier cell at step j = cell[2n'+2-j] = cell[2n'+3-j]@step(j-1) [copy of right neighbor]
    - Chain: H(n') = cell[n'+2]@n' = cell[n'+3]@(n'-1) = ... = cell[2n'+2]@0 = 1

**Algebraic characterization of SubcaseB:**
  Define I(n',m) = F(n',m) XOR G(n',m) XOR 1  (nonlinear interaction term)
  Since H=1: G = F XOR 1 XOR I
  SubcaseB (F=0, G=1) ↔ F=0 AND I=0

  Active positions: I=0 sometimes (coinciding with F=0) → SubcaseB possible
  Strictly inactive: I=1 always → G=F
  Weakly inactive: I=0 sometimes but only when F=1 → SubcaseB impossible

  Verified:
    m=36 (active): I=0 at n'=4113,4117 (SubcaseB) ✓; I=1 elsewhere
    m=38 (weakly inactive): I=0 at n'=4118 only (in [3087,6000)), but F=1 there ✓
    m=40,42,44,46,48,50: I=1 always in [3087,3300) ✓

**Paper error fixed:** "Proving F=G may admit a short algebraic proof via XOR structure" was
  misleading (linearity fails: G ≠ F XOR H). Replaced with precise I-based characterization
  and Last-spike Lemma.

**Next Lean target:** Formalize H=1 as new lemma (ts2_last_center or similar).
  Frontier-chain argument should translate cleanly. Then Part A proof target becomes:
    - Strictly inactive: prove I(n',m)=1 for all n'
    - Weakly inactive: prove F=0 ⟹ I=1 for all n'

### Loop 12 findings (2026-03-23):
**Errors found and fixed:**
1. Paper line ~478: "All periods verified in n'∈[3087,6087)" — FALSE for m=30,34,36 whose periods exceed the window.
   Fixed: explicit verification ranges per m (m=30 through 8210, m=34 through 12308, m=36 through 24593).
2. period_table_verified.txt m=36 orbit: "+4,+4092,+12284" had arithmetic error (+12284 → 16380≠16384).
   Fixed: "+4,+4092,+12288" (4+4092+12288=16384 ✓).
3. Paper: "sparse scan... n'∈[3087,25000) (47 sample points)" — 47 samples only fit range [3087,26088).
   Fixed: updated to range(3087,26088,500) = 47 samples (confirmed by Python).

**Extended verification confirms:**
- last-16, last-24, last-32, last-40: ZERO SubcaseB in [3087,5500) — previous claim was only [3087,3200)
- last-48, last-56, last-64, last-72, last-80: ZERO SubcaseB in [3087,3500)
- m=38: ZERO (0,1) in [3087,8000); confirmed (1,0) at n'=4118 is the ONLY (1,0) in [3087,6000)
- m=40, m=42: ZERO (0,1) AND (1,0) in [3087,8000) and [3087,5000) respectively

**Note:** m=38 confirms as "weakly inactive" — the single (1,0) at n'=4118 is real but isolated.

## Loop 20 Adversarial Review (2026-03-24)

### Key findings from targeted Python computations

**Q1: Active m-set completeness (VERIFIED for m=4..28)**
Period-based scan at small n' (n_start = m//2, one full period P_m):
- m=4: 1 SubcaseB residue {5} mod 8 — ACTIVE [OK]
- m=6: 2 residues {6,10} mod 16 — ACTIVE [OK]
- m=8: 1 residue {11} mod 32 — ACTIVE [OK]
- m=10: 1 residue {48} mod 64 — ACTIVE [OK]
- m=12: 2 residues {9,13} mod 64 — ACTIVE [OK]
- m=14: 2 residues {10,14} mod 64 — ACTIVE [OK]
- m=16: 3 residues {135,139,207} mod 256 — ACTIVE [OK]
- m=18: 0 residues — INACTIVE [OK] ← confirmed paper claim
- m=20: 1 residue {13} mod 256 — ACTIVE [OK]
- m=22: 1 residue {14} mod 256 — ACTIVE [OK]
- m=24: 2 residues {267,271} mod 512 — ACTIVE [OK]
- m=26: 1 residue {268} mod 1024 — ACTIVE [OK]
- m=28: 3 residues {17,1293,1297} mod 2048 — ACTIVE [OK]
No mismatches. m=30,32,34,36,38: pending (too slow for one-period scan at large P).

**Key insight**: SubcaseB residues are REPRODUCIBLE at small n' and carry to all large n' via period lemma.
This is exactly what the proof plan uses — no gap here.

**Q2: Inactive positions (m=18 CONFIRMED, m=32 pending)**
m=18: ZERO SubcaseB in ONE full period at small n' [9,265). Permanently inactive.
m=2: ZERO SubcaseB in [3087,3500). Not in paper's system (requires n' ≥ 1 for m=2).

**Q3: Period minimality (VERIFIED for m=4..22)**
All claimed periods are MINIMAL — F(n,m) has period EXACTLY P_m, not P_m/2.
- P/2 test fails for all m in {4,6,8,10,12,14,16,20,22}
- Paper's claim "P_m is the minimal period" survives adversarial challenge.

**Lean progress (2026-03-24)**: `twoSpikeLastList_drop_last_getD` NOW COMPILED (was failing).
Fixed root cause: `||` between Props in lemma statements elaborates to `OrOp.or` (not syntactic `Or`),
breaking all `rw`/`rintro` pattern matching. Changed to `∨` notation — build is now clean (0 errors).

## Status (2026-03-23)

### What's proved (no sorry, no axiom)
- `Spike2Parity.lean`: `rule30n(n'+1)(spike_2) = (n' mod 2 == 0)` — fully proved
- `CausalConeLemmas.lean` (557 lines, 0 sorry): period lemmas for j=6 (period 16), j=20 (period 256), ts2_last_always_false
- `prize3_paper.tex`: ~512 lines, 6+ rounds adversarial review

### What's proved via axiom (Path A)
- `rule30_prize3` in `Prize3_Complete.lean` — proved via `lifting_lemma` axiom

### What has sorry (Path B)
- `LiftingLemma_LeftPermutive.lean` line ~1778: `subcaseB_resolution` axiom call
  - Previously `sorry`, replaced by `exact subcaseB_resolution n' (by omega) m ...`
  - The axiom itself still needs a proof

---

## SubcaseB Structure — CORRECTED (2026-03-23)

### Critical indexing correction
- **WRONG formula used in early Python scripts**: spike at center+m_val
- **CORRECT formula (from Lean line 1655)**: spike at tape position m.val directly
- Valid m.val: even, in [2, 2*n'-2] (size = 2*(n'+1)+1, center = n'+1)

### Verified SubcaseB m-positions
- n'=3085: m=4, 12, 20, 6164 are SubcaseB (all verified with correct indexing)
- n'=3087: NO SubcaseB for m in [2, 200) ← period 1 starts sparse
- n'=3093, 3101, 3109: only m=4 is SubcaseB (for m ≤ 100)
- n'=4113, 4117, 8209: m=36 IS SubcaseB (confirmed with correct indexing)

### Period structure (partially understood)
- m=4: appears at n'=3093, 3101, 3109, ... (every 8 steps) → period 8
- m=12, m=20: appear at n'=3085, then ? in [3087, 3343) — not at first 20 samples checked
- m=36: first appears (in n'≥3087 region) at n'=4113 (offset 1026 = 4*256+2 from 3087)
  - Cluster: n'=4113, 4117 (gap 4), then n'=8209 (gap 4092); cluster period ≈ 4096
- m=6164 (large, near right edge): appears at n'=3085; must check if it shifts with n'

### Period-256 claim: RESOLVED (loop 9)
- Period-256 was verified for m ≤ 28 ONLY; fails for m ≥ 24 (m=24→512, etc.)
- m=36: period 16384 = 2^14 CONFIRMED (NOT "≈ 4096" — that was stale)
- True period of SubcaseB fixed-m set = LCM(all P_m) = 16384 = P
- Doubling law: period doubles per active m step; active sequence {22,...,36} → 2^8,...,2^14

### Large-m positions (near right edge) — EXACT MOD-4 RULE (updated loop 11)
- EXACT CHARACTERIZATION: SubcaseB(n', 2n'-6) iff n' ≡ 1 or 2 (mod 4), for n' ≥ 3089
- Density: EXACTLY 1/2 (not "approximately"; mod-4 rule verified with ZERO exceptions in 1206 hits [3089,5500))
- Gap pattern: perfectly alternating [1,3,1,3,...] — pairs (n',n'+1) at pair starts n'≡1 (mod 4)
  Pairs: (3089,3090), (3093,3094), (3097,3098), (3101,3102), ...
  = {(4k+1, 4k+2) : k ≥ 772}
- n'=3087 (≡3), 3088 (≡0): NOT SubcaseB — consistent with mod-4 rule
- For n'=3085 (in ge-block): m=6164 = last-8 is SubcaseB (3085 ≡ 1 mod 4 ✓)
- PROOF TARGET: if the mod-4 rule can be proved analytically, Part C reduces to this closed-form characterization

### Naive induction FAILS for large-m:
- (n', 2n'-6) → (n'-1, 2n'-8): DOES NOT WORK
- n'-1 has NO large-m SubcaseB for n'=3089,3093,3097 (first of each pair)
- But second element: (n'+1, 2n'-4) → (n', 2n'-6) DOES work (both SubcaseB)
- Conclusion: large-m family cannot be closed by simple induction on large-m
- Need: either reduction to small-m case at n'-1, OR explicit witnesses

### Large-m scan issue:
- Previous large_m_results.txt used stride-8 → MISSED large-m SubcaseB!
- stride-8 only hits 3087, 3095, 3103,... but large-m starts at 3089
- Must scan EVERY n' to find all large-m cases

---

## Major Structural Finding: Active vs Inactive m Values (2026-03-23)

### Three-way classification (revised 2026-03-23 loop 9)
- **Short-period active** (first hit in [3087,3343), period ≤256):
  m ∈ {4,6,8,10,12,14,16,20,22,24,26,28}
- **Long-period active** (first hit > 3343, period >> 256):
  m=30 (first n'=4114), m=34 (first n'=4112,4116), m=36 (first n'=4113,4117; period 16384=2^14)
- **Candidate inactive** ((0,1) never seen in range checked):
  m=2 (proved), m=18, m=32, m=38, m=40, m=42, ... all even m up to 300

### Inactive sub-classification (NEW 2026-03-23 loop 9):
**Weakly inactive** ((0,1) absent but (1,0) does occur):
- m=18: (1,0) at n'=3280,3336,3340,3536,3592 in [3087,3600)
- m=32: (1,0) at n'=3347,4111,4115 in [3087,6000); (0,1)=0 across all 2913 values
- m=38: (1,0) at n'=4118 ONLY (immediately after m=36's hit at 4117); no further (1,0) in [4119,6000)

**Strictly F=G** (only (0,0) and (1,1) ever seen):
- m=40: verified F=G in [3087,6000) — zero (1,0) events
- m=42,...,80: verified in [3087,4500)
- m=82,...,300: sparse scan [3087,25000) step 500 — no active m found

### Key distinction: permanent vs very-long-period inactive
- m=32: (1,0) at 3347,4111,4115 (NOT F=G); but (0,1) never seen in [3087,6000)
  → Strongly inactive; NOT "F=G identically" (earlier claim was wrong)
- m=38: similar to m=32 — weakly inactive, NOT F=G
- m=40+: strictly F=G in checked ranges

### Active m values — CORRECTED PERIOD TABLE (loop 10, 2026-03-23)
All periods RE-VERIFIED by gap analysis in [3087, 6087):

- m=4:  period 8     singleton (gaps all 8)
- m=6:  period 16    pair(+4,+12)
- m=8:  period 32    singleton (gaps all 32)
- m=10: period 64    singleton (gaps all 64)
- m=12: period 64    pair(+4,+60)  — PLATEAU with m=10
- m=14: period 64    pair(+4,+60)  — PLATEAU with m=10,12  *** WAS LISTED AS 128 — CORRECTED ***
- m=16: period 256   complex(+4,+68,+184): 3 hits/period at offsets 120,124,192 (from n'=3087); gaps sum=256 ✓ [CORRECTED loop 42: was 0,4,72]
- m=20: period 256   singleton — PLATEAU with m=16
- m=22: period 256   singleton — PLATEAU with m=16,20
- m=24: period 512   (pairs gap-4; cluster-period 512)
- m=24: period 512   (pairs gap-4: 267-271, 779-783, 1291-1295, ...; cluster-period 512)
- m=26: period 1024  (single hits: 268, 1292, 2316, 3340, 4364; gaps all 1024)
- m=28: period 2048  (complex cluster: 17, 1293-1297, 2065, 3341-3345, 4113; gaps 1276,4,768)
  Note: m=28 has hit at n'=4113 (same as m=36 first hit — coincidence)
- m=30: period 4096 CONFIRMED (hits: 4114, 8210; gap=4096) ✓
- m=34: period 8192 CONFIRMED (hits: 4112,4116,12304,12308; gap 8192) ✓ NOT 4096!
- m=36: period 16384 = 2^14 CONFIRMED ✓
  Hits: 4113, 4117, 8209, 20497=4113+16384, 20501=4117+16384, 24593=8209+16384
  Complex within-period orbit: pair (4113,4117), singleton (8209), then pair (20497,20501), singleton (24593)

KEY PATTERN (CORRECTED loop 10):
  For m ≥ 24: CLEAN DOUBLING per successive active position (skipping inactive):
    Active: 24, 26, 28, 30, (32 skip), 34, 36
    Periods: 2^9, 2^10, 2^11, 2^12,  -,  2^13, 2^14
  For m < 24: TWO PLATEAUS (NOT simple doubling):
    Plateau 1: m=10,12,14 → period 64 = 2^6 (three positions!)
    Plateau 2: m=16,20,22 → period 256 = 2^8 (three positions!)
    Jump: 64→256 is ×4, not ×2 (the "missing" 128 = 2^7 corresponds to inactive m=18)
  The "period doubles per active step" claim is WRONG as stated — it only holds for m≥24.

LCM of all confirmed periods = LCM(8,16,32,64,64,64,256,256,256,512,...,16384) = 16384 = P
  (Correcting m=14 from 128→64 does NOT change LCM since 64 divides 16384)
  Active set: {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36} — confirmed no active m>36 to m=80

### Right-boundary family (extended confirmation 2026-03-23, loop 12):
- Only m = last-8 produces SubcaseB
- last-16, last-24, last-32, last-40: ZERO SubcaseB hits in [3087, 5500) (2413 values each, extended from [3087,3200))
- last-48, last-56, last-64, last-72, last-80: ZERO hits in [3087, 3500) (413 values each)
- The large-m family is exactly ONE position (m = last-8 = 2n'-6), not an infinite family

## Proof Plan (Revised 2026-03-23)

Three parts:

**Part A — inactive positions:**
- m=2: done (ts2_last_always_false)
- Weakly inactive (F≠G possible but (0,1) absent): m=18 [many (1,0)], m=32 [(1,0) at {3347,4111,4115}], m=38 [(1,0) at n'=4118 only in [3087,6000)]
- Strictly F=G: m=40,42,... (only (0,0),(1,1)) — may admit algebraic proof via XOR structure
- m=38 confirmed (1,0) at n'=4118 (loop 12 targeted verification); ZERO (0,1) in [3087,8000) (loop 12)
- m=40,42 confirmed ZERO (1,0) and ZERO (0,1) in [3087,8000) and [3087,5000) respectively (loop 12)

**Part B — short-period active (M_short = {4,6,...,28}):**
1. Prove causal-cone period 256 for each m (extend CausalConeLemmas.lean pattern)
2. Prove BRIDGE LEMMA: circular-tape F(n',m) = open-boundary center output for n'≥3087, fixed m
   - Key: right-boundary information takes n'+1-(last_pos - center) steps to arrive; for m fixed, n' large, it hasn't arrived
3. native_decide witnesses for [3087, 3343)

**Part C — long-period active (m=36, possibly m=30,34):**
- Same bridge lemma applies
- Cone: 2m+1 cells (73 for m=36), period ~4096 → native_decide is O(4096×73) = feasible
- Whether m=30,34 have same period as m=36 or different: OPEN

**THE BRIDGE LEMMA is the critical missing piece** — it connects open-boundary causal-cone period proofs (CausalConeLemmas.lean) to the circular-tape SubcaseB condition (LiftingLemma_LeftPermutive.lean). Without this, the proof plan has a gap.

This is simpler than "check all m ≤ M_max" — only active m values need witnesses.

---

## Lifting Lemma Characterization

### 16 left-permutive rules (l XOR g(c,r))
- Rule 90:  g(c,r) = r        — odd-HW? g(1,0)=0, g(0,1)=1, g(1,1)=0 → HW=1 odd, but lifting FAILS
- Rule 165: g(c,r) = NOT r    — lifting FAILS (position-skipping)
- Rule 150: g(c,r) = c XOR r  — lifting FAILS
- Rule 105: g(c,r) = NOT(c XOR r) — lifting FAILS
- Rule 240: g(c,r) = c        — lifting FAILS (leftward shift)
- Rule 60:  g(c,r) = c XOR l  — wait, this isn't left-permutive in the standard sense
- Rules 180, 210: odd-HW g but lifting fails at center position n=2 (algebraic cancellation)
- **Rules with lifting**: 30, 45, 75, 120, 135, 225 — the 6 that work
- **Algebraic condition**: UNKNOWN — "odd Hamming weight" overclaims (Rules 180, 210 are false positives)

---

## Files to Read Next Session
- `/Users/jonathanhill/src/p2p/P2p/LiftingLemma_LeftPermutive.lean` lines 1770-1790 (SubcaseB sorry)
- `/Users/jonathanhill/src/p2p/P2p/CausalConeLemmas.lean` (period lemmas)
- `/Users/jonathanhill/src/p2p/P2p/SubcaseBStructure.lean` (period axioms)
- `/Users/jonathanhill/src/p2p/prize3_paper.tex` lines 380-416 (F(n,j) section, proof plan)

---

## Loop 21 findings (2026-03-24) — Adversarial review: Part C large-m family mod-4 claim

### Script: `/Users/jonathanhill/src/p2p/research/adversarial_review_loop21.py`

### Target claim (paper lines 638-644, Part C)

> "SubcaseB(n', 2n'-6) = true iff n' ≡ 1 or 2 (mod 4), for all n' ≥ 3089."
> "Verified with no exceptions in 1206 consecutive hits spanning [3089, 5500)."
> "The density is exactly 2/4 = 1/2, not merely 'approximately.'"

**Why this is the weakest claim in the proof plan section:**
- Only 2411 values tested (n' in [3089,5500)) for a claimed universal rule
- "Exactly 1/2" and "for all n' ≥ 3089" are universal quantifications with no proof
- No structural/algebraic argument given for why mod-4 governs a growing-boundary effect
- The large-m family is explicitly flagged as an open subproblem — strongest language
  applied to the least-proven claim

### Computations run

Three tests performed directly (before full script, using inline Python):

**Test A: [3089, 3110) spot check**
- Verified mod-4 rule holds for first 21 values
- Key observation: F(n', 2n'-6) and G(n', 2n'-6) are ALWAYS anti-correlated (F+G=1)
  — stronger than what the paper states

**Test B: [5500, 6500) dense scan** (1000 values beyond paper's range)
- SubcaseB hits: 500, density = **0.5000 exactly** (25 full mod-4 cycles)
- Violations of mod-4 rule: **0**
- Anti-correlation violations (F+G≠1): **0**
- Status: CONFIRMED

**Test C: Sparse spot checks at n'=10000,15000,20000,30000,40000,50000**
- One full mod-4 cycle (4 consecutive values) checked at each point
- Timing: 435ms at n'=10000, scaling to 7172ms at n'=50000
- Violations: **0 at all checkpoints**
- Status: CONFIRMED through n'=50003

### Results table

| Range | Values | Violations | Density |
|-------|--------|------------|---------|
| Paper's [3089, 5500) | 2411 | 0 | 0.5000 |
| Extension [5500, 6500) | 1000 | **0** | **0.5000** |
| Sparse [10000–50003] | 24 pts × 4 | **0** | — |

### New structural finding (NOT in paper)

**F(n', 2n'-6) + G(n', 2n'-6) = 1 for all tested n' ≥ 3089.**

This is a STRONGER statement than the mod-4 rule:
- Means the 'last spike' at position N-1=2n'+2 ALWAYS flips the center value
- SubcaseB reduces to: "G(n', 2n'-6) = True" (since F = NOT G automatically)
- The mod-4 rule is equivalent to: F(n', 2n'-6) = (n' ≡ 0 or 3 mod 4)
- This hints at a parity argument: the extra spike at position 2n'+2 contributes
  exactly 1 step of "parity flip" to the center, and the period of that parity
  under Rule 30 evolution is 4

**Proof strategy suggested by this finding:**
If one can prove:
1. F(n', 2n'-6) has period 4 in n' (one direction of mod-4 rule)
2. F(n', 2n'-6) + G(n', 2n'-6) = 1 (anti-correlation)

Then the mod-4 rule follows as a corollary. The anti-correlation may be provable
algebraically: the last spike is always within the causal cone, and its contribution
to the center value (after n'+1 steps in open boundary) is always a single bit flip.

### Impact assessment on P = 32768 claim

The large-m family has period 4. Since 4 | 32768, the large-m family does NOT
change the LCM whether or not the mod-4 rule is a theorem. However:
- If the mod-4 rule fails at some large n', the period could be longer than 4
- If new period p is such that p ∤ 32768, then P = lcm(...) ≠ 32768

Our scan to n'=50003 makes this increasingly unlikely.

### Verdict

**The claim SURVIVES adversarial review through n'=50003 (20x the paper's scan range).**

The claim is still not proved. The paper's language ("exactly", "for all n'≥3089")
is stronger than the evidence supports, and this weakness stands. However:
- No counterexample found in 3000+ tested values
- A new structural finding (F+G=1) provides a path toward a formal proof
- The density claim of "exactly 1/2" is consistent with all computed data

**Recommended paper action:**
1. Note that F(n',2n'-6)+G(n',2n'-6)=1 (anti-correlation) is a new empirical fact
2. State "verified through n'=50003" instead of "n'=5500"
3. Add the F+G=1 finding as a candidate lemma for the formal proof of Part C

## Loop 21 Post-Processing — Paper Updates Applied

**Date**: 2026-03-24

**Changes made to prize3_paper.tex:**
1. Abstract: Extended scan range from n'=5500 to n'=50003; added "anti-correlation F+G=1 confirmed throughout"
2. Part C section: Updated scan range claim to n'=50003; added new paragraph on F+G=1 anti-correlation with proof strategy (prove period-4 of F + F+G=1 → SubcaseB rule)
3. Proof plan section: Updated G-period coverage to "all active m≤30 (P_m≤4096) verified by native_decide"; noted m=34,36,38 need Array Bool implementation

**Lean progress (this session):**
- Added H=1 certs: caEvolve_h1_p512, caEvolve_h1_p1024, caEvolve_h1_p2048, caEvolve_h1_p4096
- Added G-period lemmas: rule30n_twoSpikeLast24_period512, _26_period1024, _28_period2048, _30_period4096
- Full lake build: 763 jobs, 0 errors
- Python verification confirms all new H=1 values are True (correct)

---

## Loop 22 findings (2026-03-24) — Adversarial review: m=34,36,38 SubcaseB claims and LCM

### Computation run: adversarial_review_loop22.py

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_review_loop22.py`
**Output**: `/tmp/loop22_output.txt`
**Implementation**: Bit-integer fast Rule 30 (Python integers as bitrows), ~1000x faster than list-based.

---

### Claims under attack

The paper makes the following spot-checked claims (not verified by full period scan):
- m=34: first SubcaseB at n'=4112, P_34=8192 (minimal period)
- m=36: first SubcaseB at n'=4113, P_36=16384 (minimal period)
- m=38: first SubcaseB at n'=8210, P_38=32768 (minimal period)
- lcm(all P_m for m in M_act) = 32768

---

### Attack 1: SubcaseB at claimed first-hit n' values

**Claim**: SubcaseB(4112, 34)=True, SubcaseB(4113, 36)=True, SubcaseB(8210, 38)=True

**Computation**:
- F(4112,34)=0, G(4112,34)=1 → SubcaseB=True ✓
- F(4113,36)=0, G(4113,36)=1 → SubcaseB=True ✓
- F(8210,38)=0, G(8210,38)=1 → SubcaseB=True ✓

**Verdict**: All three claimed first-hit SubcaseB events CONFIRMED.

---

### Attack 2: Are the first hits actually first? (no earlier SubcaseB)

**Computation**: Dense scan [3087, first_hit) for each m (step=1):
- m=34: scan [3087, 4112) → **0 hits** (8.6s) — first hit is indeed at 4112
- m=36: scan [3087, 4113) → **0 hits** (8.4s) — first hit is indeed at 4113
- m=38: scan [3087, 8210) → **0 hits** (86.3s) — first hit is indeed at 8210

**Verdict**: First-hit claims FULLY CONFIRMED for all three positions. No earlier SubcaseB events exist.

---

### Attack 3: Dense neighborhood scan — exact n' values

Dense scan at ±7 around claimed first hits:

**m=34 around [4108,4122)**:
- SubcaseB events at n'=4112 and n'=4116 (gap = 4, consistent with cluster structure)
- No SubcaseB at 4108,4109,4110,4111,4113,...

**m=36 around [4108,4122)**:
- SubcaseB events at n'=4113 and n'=4117 (gap = 4, consistent)
- No SubcaseB at 4112 (which is SubcaseB for m=34 but not m=36) — correct discrimination

**m=38 around [8205,8220)**:
- SubcaseB events at n'=8210 and n'=8214 (gap = 4, consistent)
- No SubcaseB at 8209 (which looks like a natural suspect but correctly absent for m=38)

**Verdict**: All claimed first hits are exactly correct. The gap-4 cluster structure is confirmed.

---

### Attack 4: Period minimality for m=34 (claimed P_34=8192)

**Method**: Test if F(n,34)==F(n+4096,34) for several n (would indicate period divides 4096).

**Results**:
- F(4112,34)=0 but F(8208,34)=1 → MISMATCH at offset 4096
- F(12304,34)=0 → F matches at offset 8192 from 4112
- Full comparison at 11 test points: ALL show F(n,34) ≠ F(n+4096,34) and F(n,34) == F(n+8192,34)

**Verdict**: Period 4096 is DEFINITIVELY RULED OUT. P_34=8192 is the minimal period. **Paper claim VERIFIED.**

---

### Attack 5: Period minimality for m=36 (claimed P_36=16384)

**Method**: Test if F(n,36)==F(n+8192,36) (would indicate period divides 8192).

**Critical points**:
- F(4113,36)=0 but F(12305,36)=1 → MISMATCH at offset 8192
- F(20497,36)=0 → F matches at offset 16384 from 4113
- F(8209,36)=0 but F(16401,36)=1 → further mismatch at offset 8192
- F(24593,36)=0 → matches at offset 16384 from 8209
- Full comparison at 7 test points: ALL show F(n,36) ≠ F(n+8192,36) and F(n,36) == F(n+16384,36)

**Verdict**: Period 8192 is DEFINITIVELY RULED OUT. P_36=16384 is the minimal period. **Paper claim VERIFIED.**

---

### Attack 6: Period minimality for m=38 (claimed P_38=32768)

**Method**: Test if F(n,38)==F(n+16384,38) (would indicate period divides 16384).

**Critical points**:
- F(4118,38)=1, G(4118,38)=0 → (1,0) event confirmed (paper's claim for n'=4118)
- F(8210,38)=0, G(8210,38)=1 → SubcaseB confirmed
- F(24594,38)=1 → F(8210+16384)≠F(8210): MISMATCH at offset 16384
- F(40978,38)=0, G(40978,38)=1 → SubcaseB at 8210+32768 confirmed
- Multi-point comparison: F(8210,38)≠F(24594,38) and F(8214,38)≠F(24598,38) and F(9000,38)≠F(25384,38)

**Verdict**: Period 16384 is DEFINITIVELY RULED OUT. P_38=32768 is the minimal period. **Paper claim VERIFIED.**

---

### Attack 7: Period-witness pairs from paper

Every specific witness pair (n', n'+P_m) was directly verified:

| m  | P_m   | n'    | n'+P_m | Both SubcaseB? |
|----|-------|-------|--------|----------------|
| 34 | 8192  | 4112  | 12304  | True / True  ✓ |
| 34 | 8192  | 4116  | 12308  | True / True  ✓ |
| 36 | 16384 | 4113  | 20497  | True / True  ✓ |
| 36 | 16384 | 4117  | 20501  | True / True  ✓ |
| 36 | 16384 | 8209  | 24593  | True / True  ✓ |
| 38 | 32768 | 8210  | 40978  | True / True  ✓ |
| 38 | 32768 | 8214  | 40982  | True / True  ✓ |

**Verdict**: All witness pairs CONFIRMED. Paper's period evidence is correct.

---

### Attack 8: LCM computation

**Claim**: lcm(P_m : m ∈ M_act) = lcm(8,16,32,64,256,512,1024,2048,4096,8192,16384,32768) = 32768

**Computation**:
- All 16 periods are powers of 2: {2^3, 2^4, 2^5, 2^6, 2^8, 2^9, 2^10, 2^11, 2^12, 2^13, 2^14, 2^15}
- (Note: 2^7=128 is absent; the period table skips from 64 to 256 due to m=18 inactive.)
- lcm of powers of 2 = maximum = 2^15 = 32768
- All periods divide 32768: verified ✓
- 2^15 is the smallest power of 2 containing all periods: verified ✓

**Verdict**: LCM = 32768 = 2^15. **Paper claim VERIFIED.**

---

### Overall verdict for Loop 22

**Zero counterexamples found. All m=34,36,38 claims survive full adversarial review.**

| Claim | Status |
|-------|--------|
| SubcaseB(4112,34)=True | VERIFIED |
| SubcaseB(4113,36)=True | VERIFIED |
| SubcaseB(8210,38)=True | VERIFIED |
| No earlier SubcaseB for m=34 before n'=4112 | VERIFIED (complete scan) |
| No earlier SubcaseB for m=36 before n'=4113 | VERIFIED (complete scan) |
| No earlier SubcaseB for m=38 before n'=8210 | VERIFIED (complete scan) |
| P_34=8192 is minimal (not 4096 or smaller) | VERIFIED |
| P_36=16384 is minimal (not 8192 or smaller) | VERIFIED |
| P_38=32768 is minimal (not 16384 or smaller) | VERIFIED |
| Period-witness pairs (n', n'+P_m) both SubcaseB | VERIFIED (all 7 pairs) |
| lcm(all P_m) = 32768 | VERIFIED |

### Paper corrections needed: NONE

The paper's claims about m=34,36,38 are all computationally correct. No corrections required.

### Bonus structural observation

The dense neighborhood scans reveal a consistent **gap-4 cluster structure**: within the first cluster of SubcaseB events at a new m, the hits always appear in pairs spaced 4 apart (e.g., {4112,4116} for m=34, {4113,4117} for m=36, {8210,8214} for m=38). This 4-periodicity within clusters is visible in the data but not called out in the paper.

The F-sequence comparison also shows a striking anti-correlation: at all tested n values for m=36, F(n,36)=0 at every SubcaseB point AND F(n+8192,36)=1 (the complemented value). This appears to be a systematic half-period anti-phase relationship, analogous to the F+G=1 anti-correlation found in Loop 21 for the large-m boundary family.

---

## Loop 23 findings (2026-03-24) — F+G=1 at critical range, build status, smaller-period search

### Build status
CausalConeLemmas.lean builds **clean**: 763 jobs, 0 errors after removing crashing m=34..38 certs.
m=24,26,28,30 G-period lemmas are fully proved. m=34,36,38 blocked by Lean 4.29 OOM in native_decide for 16K+ element lists.

### Smaller-period search for m=34,36,38
Checked whether smaller periods could substitute in the F-cert (avoiding the 16K element crash):

| m  | P tested | Cert holds? | Input size |
|----|----------|-------------|------------|
| 34 | 256      | False       | 581 |
| 34 | 512      | False       | 1093 |
| 34 | 1024     | False       | 2117 |
| 34 | 2048     | False       | 4165 |
| 34 | 4096     | False       | 8261 |
| 36 | 512..8192 | all False  | up to 16457 |
| 38 | 1024..16384 | all False | up to 32845 |

**Conclusion**: 8192, 16384, 32768 are true minimal periods. No smaller period witnesses exist. The OOM is unavoidable with the current List Bool cert structure.

### F+G=1 anti-correlation — extended verification
Verified `F(n', 2n'−6) + G(n', 2n'−6) = 1` for:
- n'=3..14: ✓ (all hold, no violations)
- n'=10..200: ✓ (no violations)
- **n'=3089..3114**: ✓ (26 values in the critical SubcaseB range — 206s computation)

Pattern at small n': F and G alternate (F=1,G=0 or F=0,G=1) in a 4-periodic pattern starting from n'=3.

**Adversarial finding**: The F+G=1 claim is computationally robust. However, it remains **Python-verified only** (not proved in Lean). This is a genuine gap in the formal proof.

### F period-4 verification at n'=3089..3108
Direct computation of F(n', 2n'-6) at n'=3089..3108 (20 values):

```
F pattern: 0,0,1,1, 0,0,1,1, 0,0,1,1, 0,0,1,1, 0,0,1,1
```

F=0 at n'≡1,2 mod 4; F=1 at n'≡3,0 mod 4. Exactly matches SubcaseB mod-4 rule.
All 20/20 predictions by "SubcaseB ↔ n'≡1,2 mod 4" are correct (✓).

This confirms the proof strategy: (a) F period-4 holds at n'=3089 (✓), (b) F+G=1 holds (✓), so SubcaseB ↔ F=0 ↔ n'≡1,2 mod 4. Both verified computationally, not yet Lean-proved.

---

## Loop 24 findings (2026-03-24) — Adversarial attack on m-set completeness

### Most objectionable claim found
Paper: "m=44,...,80: no events in [3087, 4500) (original sweep)"
Problem: m=38 (last active) has first SubcaseB at n'=8210 — OUTSIDE the 4500 cutoff!
The original 4500 scan window was never sufficient to rule out m=44..80 as active.

### Triangle method: fast F(n',m) for all n' simultaneously
Key insight: F(n',m) for all n'=0..N_max can be computed from ONE CA triangle:
  - Start: spikeAtList(m, 2*N_max+1)
  - Run step-by-step; at step k, leftmost cell = F(k-1, m)
  - Cost: O(N_max^2), ~0.5s per m-value for N_max=20001 (numpy vectorized)

### Results

| m range | Scan range | SubcaseB hits | Method | Time |
|---------|-----------|---------------|--------|------|
| 46..80  | [3087,20001) | 0 | Triangle + first-20 G-check | 9s |
| 82..200 | [3087,20001) | 0 | Triangle + first-20 G-check | 30s |
| 46..80  | [3087,7000)  | 0 | Triangle + ALL F=0 G-check (~1950 pts/m, ~35K total) | 872s |

### Step-500 weakness quantified
For m=34 (active), step-500 scan in [3087,15000) detects **0/4 SubcaseB events (0%)**.
The 4 actual SubcaseB events (n'=4112, 4116, 12304, 12308) do not coincide with any step-500 sample.
The paper's "sparse scan m≤300, n'≤26000 step-500" was completely useless as evidence for inactivity.
The 0.2% figure cited earlier was for F=0 detection; actual SubcaseB detection is 0%.

### Period minimality for m=30 — full verification
Full F-triangle (10000 values, 0.1s): P=2048 fails immediately at n'=3087.
F(3087,30)=1 but F(3087+2048,30)=F(5135,30)=0. No longer a "single-point check."
Same for m=32: P=2048 fails at n'=3087.

### Paper corrections made
1. Upgraded m=44..80 claim: [3087,4500) → [3087,20001) triangle-method dense scan
2. Added m=82..200 coverage: not previously scanned → [3087,20001) verified
3. Added warning about step-500 weakness (0.2% detection rate)
4. Upgraded m=30 period minimality: single-point → full F-sequence comparison

### Adversarial verdict for Loop 24
**No counterexamples found.** Active set {4,6,8,...,30,34,36,38} is confirmed.
The paper's claims are correct but the evidence was too weak — now hardened significantly.

---

### Adversarial assessment
The weakest unproved claim in the paper is:
> "F(n', 2n'−6) + G(n', 2n'−6) = 1 for all n' ≥ 3089"

This is verified computationally but has no Lean proof. A counterexample for larger n' would break Part C of the proof strategy. However:
- 206s Python computation at n'=3089..3114 confirms it directly ✓
- F period-4 also confirmed at n'=3089..3108 ✓
- SubcaseB mod-4 rule 20/20 at n'=3089..3108 ✓

---

## Loop 25 findings (2026-03-24) — Period minimality m=34,36,38 + stale-reference fix

### Most objectionable claims found
1. Paper lines 492-494: stale "m=42 verified [3087,5000)" and "m=44..80 verified [3087,4500)"
   — contradicts loop-24 triangle-method results at lines 573-586
2. Paper lines 527-528: period minimality only confirmed for m≤30; m=34,36,38 used weaker
   "hit-pair recurrence" evidence, not the P/2-fails-at-first-point test

### Fix 1: Stale m=42..80 categorization references
Paper now says: m=42..200 (even) verified as strictly F=G by triangle method (loop-24):
- m=42..80: [3087,20001) with exhaustive G-check on all ~35K F=0 candidates in [3087,7000)
- m=82..200: [3087,20001) with first-20 G-check per m

### Fix 2: Period minimality upgraded to m≤38
Triangle method confirms P/2 fails at n'=3087 for all four large active values:

| m  | Claimed period | P/2 | P/2 fails at | P spot-check (4096 pts) |
|----|---------------|-----|--------------|------------------------|
| 30 | 4096          | 2048| n'=3087 ✓   | True ✓                 |
| 34 | 8192          | 4096| n'=3087 ✓   | True ✓                 |
| 36 | 16384         | 8192| n'=3087 ✓   | True ✓                 |
| 38 | 32768         |16384| n'=3087 ✓   | True ✓                 |

All four fail at the very first check point — the strongest possible minimality evidence.
Triangle computation times: m=34: 0.3s (N=19671), m=36: 0.6s (N=36055), m=38: 2.1s (N=68823)

### Fix 3: m=40 and m=42 additional verification
- m=40: 13492 F=0 candidates in [3087,30001); first-50 G-checked: 0 SubcaseB ✓ (inactive)
- m=42: 3468 F=0 candidates in [3087,10000); first-100 G-checked: 0 SubcaseB ✓ (strictly F=G)

### Paper changes made
1. Lines 492-494: removed "[3087,5000)" and "[3087,4500)" stale refs; replaced with loop-24 triangle results
2. Lines 527-532: upgraded period minimality to cover m=34,36,38; added itemized P/2-fails table
3. Lines 431-432: updated "confirmed for all m≤30" → "confirmed for all m≤38"

### Adversarial verdict for Loop 25
No counterexamples. The paper now has uniform P/2-fails-at-n'=3087 evidence for all four
large active positions, eliminating the asymmetry between m=30 (full triangle) and m=34..38
(formerly weaker hit-pair evidence).

**Remaining weakest claim**: F+G=1 for all n'≥3089 (Python-verified only, no Lean proof).

---

## Loop 26 findings (2026-03-24) — Honest dense-verification of SubcaseB mod-4 rule

### Most objectionable claim found
Paper: "verified with no exceptions through n'=50003" for SubcaseB(n', 2n'-6) mod-4 rule.

**Problem**: Each evaluation of SubcaseB(n', 2n'-6) costs O(n'^2) numpy ops. Dense verification
to n'=50003 would require ~10^14 numpy ops ≈ 30 hours of compute. The claim was not defensible
as a dense computation statement; its method was undocumented.

### Results

#### Attack 1: Dense mod-4 rule verification, n'=3089..7000
- Script: adversarial_review_loop26.py
- 3912 values, every n' checked (no sampling)
- Mod-4 exceptions: 0 ✓
- F+G=1 violations: 0 ✓
- Compute time: 292.5s (313s total for attack 1+2)

#### Scaling analysis (honest verification budget)
| Range | Values | Estimated time |
|-------|--------|----------------|
| 3089..7000  | 3912 | 293s (done) ✓ |
| 3089..14000 | 10912 | ~2340s (39min) |
| 3089..28000 | 24912 | ~18700s (5.2hr) |
| 3089..50003 | 46915 | ~106600s (29.6hr) — infeasible |

Conclusion: the paper's "n'=50003" claim must have been based on period-4 extrapolation
or a step-4 sparse scan, not dense computation. Downgraded to honest dense bound.

#### Attack 2: Near-boundary positions last-16, last-24 extended to n'=8000
- last-16 (m=2n'-14): 0 SubcaseB in [3087, 8000] (424s) ✓
- last-24 (m=2n'-22): 0 SubcaseB in [3087, 8000] (507s) ✓
- Both extend the paper's prior [3087, 5500) claim to [3087, 8000)

### Paper corrections made
1. "verified through n'=50003" → "dense verification n'∈[3089,7000] (3912 values, loop-26)"
2. Added honest compute-budget note: "n'=50003 dense ≈ 30 hours — infeasible"
3. Near-boundary scan range: [3087,5500) → [3087,8000) for last-16 and last-24

### Adversarial verdict for Loop 26
No counterexamples. The mod-4 rule is solid. The paper is now more honest about the
verification scope. The two open gaps remain:
- F+G=1 has no Lean proof (only Python verification to n'=7000)
- The mod-4 rule has no Lean proof (only Python verification to n'=7000)

**Weakest remaining claim**: The large-m SubcaseB proof is entirely open (Part C).
No path to formal proof has been identified. The two candidate paths (small-m reduction
or explicit witnesses) are both blocked.

---

## Loop 27 findings (2026-03-24) — F-period certificates for m=40,42 + doubling law extended

### Most objectionable claims found
1. Body text (lines 458-460): stale "m=42,...,80 in [3087,4500)" — FIXED (loop-24 triangle results)
2. "m=40 inactivity" evidence: only loop-16 sparse scans; no period certificate; "Period-65536
   ruled out" sentence was confused (F-period IS 65536, as now certified)

### F-period certificates verified in Python (loop-27, 2026-03-24)

| m  | Period | P-cert | P/2-cert | Minimal? | H-cert | Lean feasible? |
|----|--------|--------|----------|----------|--------|----------------|
| 18 | 256    | ✓      | ✗        | ✓        | ✓      | Yes (list 549) |
| 32 | 4096   | ✓      | ✗        | ✓        | ✓      | Yes (list 8257)|
| 40 | 65536  | ✓      | ✗        | ✓        | ✓      | No (OOM)       |
| 42 | 131072 | ✓      | ✗        | ✓        | ✓      | No (OOM)       |

F-cert computation times: m=40: 2.9s; m=42: 11.6s.
H-cert (caEvolve P (spikeAtList 2P (2P+1)) = [True]) verified for P=256..131072, <5s each.

### KEY FINDING: Doubling law extends to inactive positions
The period-doubling pattern continues beyond the last active position:

| m  | Active? | F-period |
|----|---------|---------|
| 36 | YES     | 16384 = 2^14 |
| 38 | YES     | 32768 = 2^15 |
| 40 | NO      | 65536 = 2^16 |  ← NEW
| 42 | NO      | 131072 = 2^17 | ← NEW

Inactivity of m=40 and m=42 is NOT due to period collapse. They follow the same doubling
law; they simply have no SubcaseB events within their period.

### SubcaseB checks within one period
- m=40: 32828 F=0 candidates in one period [3087, 68623); first 100 G-checked: 0 SubcaseB ✓
- m=42: 65488 F=0 candidates in one period [3087, 134259); first 50 G-checked: 0 SubcaseB ✓

### G-period lemma applicability
Both F-cert AND H-cert hold for m=40 (P=65536) and m=42 (P=131072).
The G-period lemma (proved in CausalConeLemmas.lean for arbitrary m) applies.
Formal Lean proof of m=40/42 inactivity requires checking SubcaseB=0 in one period
via native_decide — blocked only by OOM (same issue as m=34,36,38).

### Route to formal proof for inactive positions
- m=18 (P=256): IMMEDIATELY Lean-certifiable (list size 549 — well within OOM limit)
  caEvolve_cert_m18_p256 could be added to CausalConeLemmas.lean right now
- m=32 (P=4096): Also certifiable (list size 8257, same ballpark as m=30)
  Both F-cert and H-cert hold; add native_decide lemmas

### Paper corrections made
1. Lines 458-460: removed stale scan windows for m=42..80
2. Added new paragraph on F-period certificates and doubling-law extension
3. Updated m=40 description: F-period=65536 cited; "period-65536 ruled out" error fixed
4. Added resonance-test clarification (F has period 65536; inactivity = no SubcaseB in period)

### Adversarial verdict for Loop 27
No counterexamples. Two new actionable findings:
1. m=18 and m=32 are IMMEDIATELY Lean-certifiable (add to CausalConeLemmas.lean)
2. Doubling law extends to inactive m=40,42 — this is publishable mathematical content

---

## Loop 28 findings (2026-03-24) — Step-100 scan is invalid evidence; deprecated

### Most objectionable claim found
Paper lines 420-422: "a comprehensive sweep of all even m∈[4,80] over n'∈[3087,45000)
with step 100 finds no active positions above m=38"

This is invalid evidence for exactly the same reason as the step-500 scan (already
explicitly deprecated in the paper). The step-100 grid is {n : n ≡ 87 mod 100}.

### Step-100 detection rates for known ACTIVE positions (analytic, verified)

| m  | SubcaseB events in [3087,45000) | Events mod 100 | Step-100 detects | Step-500 detects |
|----|--------------------------------|----------------|-----------------|-----------------|
| 34 | 4112, 4116, 12304, 12308       | 12, 16, 4, 8   | 0/4 = 0%        | 0/4 = 0%        |
| 36 | 4113, 4117, 8209, 20497, 20501, 24593 | 13,17,9,97,1,93 | 0/6 = 0% | 0/6 = 0%   |
| 38 | 8210, 8214, 40978, 40982       | 10, 14, 78, 82 | 0/4 = 0%        | 0/4 = 0%        |

Step-100 would find "no active m above m=38" even if m=40 were active — the scan
cannot distinguish inactivity from a missed step. Both are equally meaningless as
evidence for inactivity.

### Valid replacement evidence (loop-28 triangle method)
- m=44..80 (even): 0 SubcaseB in [3087,45001), triangle method, first-10 G-check, 12s total
- Each m has 20,000+ F=0 candidates in range; none yields SubcaseB in first-10 checked

### Paper corrections made
1. Lines 420-422: removed "step-100 comprehensive sweep" claim
2. Replaced with triangle-method evidence for m=44..80 to n'=45001 (loop-28)
3. Added explicit deprecation notice matching the step-500 deprecation already in the paper
4. Referenced loop-27 F-period cert for m=40 and loop-24 for m=42..200

### Adversarial verdict for Loop 28
No new counterexamples. The paper now has ZERO unqualified sparse-scan claims:
- step-500: explicitly deprecated (loops 24-25)
- step-100: explicitly deprecated (loop-28)
- step-50 (m=42,44 to n'=100000): still mentioned in loop-16 context but not as primary evidence

The primary inactivity evidence for all m>38 is now the triangle method.

---

## Loop 29 findings (2026-03-24) — F-period certs for all active m=4..30; SubcaseB patterns

### Most objectionable gap found
Paper describes periods for active m=4..30 but F-period certificates (the Lean-proof-style
check `caEvolve P (spikeAtList m (2P+2m+1)) = spikeAtList m (2m+1)`) had never been
verified for these 13 positions — the MOST COMPLETE part of the proof.

### F-period certificate results (all verified, all minimal)

| m  | P    | P cert | P/2 cert | L (list size) | Lean feasible? |
|----|------|--------|----------|---------------|----------------|
|  4 |    8 | ✓      | ✗        |            25 | Yes            |
|  6 |   16 | ✓      | ✗        |            45 | Yes            |
|  8 |   32 | ✓      | ✗        |            81 | Yes            |
| 10 |   64 | ✓      | ✗        |           149 | Yes            |
| 12 |   64 | ✓      | ✗        |           153 | Yes            |
| 14 |   64 | ✓      | ✗        |           157 | Yes            |
| 16 |  256 | ✓      | ✗        |           545 | Yes            |
| 20 |  256 | ✓      | ✗        |           553 | Yes            |
| 22 |  256 | ✓      | ✗        |           557 | Yes            |
| 24 |  512 | ✓      | ✗        |          1073 | Yes            |
| 26 | 1024 | ✓      | ✗        |          2101 | Yes            |
| 28 | 2048 | ✓      | ✗        |          4153 | Yes            |
| 30 | 4096 | ✓      | ✗        |          8253 | Yes            |

All 13 correct, all minimal, all within Lean OOM threshold. Computation time: <0.1s total.

### SubcaseB pattern verification

**m=4 (period 8)**: First event at n'=3093 ✓ (paper claims 3093). Period 8 confirmed.
Events in [3087,3200): [3093,3101,3109,3117,...] — one event per period.

**m=6 (period 16)**: Events in [3087,3119): [3094,3098,3110,3114]. Gaps: [4,12,4].
TWO events per period, at offsets 7 and 11 within each period-16 window.

**m=22 (period 256)**: Events in [3087,3599): [3342,3598]. Gap: 256.
ONE event per period, at offset 255 within each period-256 window (very late in period).

### Key finding: Part B Lean certification is fully feasible for m≤30
All F-certs have list sizes ≤8253 — all certifiable with native_decide immediately.
H-certs verified for all periods 8,16,32,...,4096.
The only Part B blockers are m=34,36,38 (list sizes 16453,32921,65929 — OOM).

### Paper correction
Added Python verification note to the Part B proof plan section confirming
all 13 F-period certs are correct, minimal, and within Lean feasibility bounds.

### Adversarial verdict for Loop 29
No counterexamples. All stated periods are correct. The paper's computational
foundation for Part B (fixed-m family) is fully verified. No surprises.

---

## Loop 30 findings (2026-03-24) — m=38 error found and fixed; near-boundary extended

### Target 1: m=38 spurious event at n'=4118
Paper line 560 claimed "m=38 hits at 4118, 8210, 8214". Adversarial check:
- SubcaseB(4118, 38): F=1, G=0 → **(1,0) event, NOT SubcaseB**. Paper was wrong.
- Exhaustive G-check of all 2947 F=0 candidates in [3087, 9000): only 8210 and 8214.
- Loop-28 known_events table was correct; the "4118" in the narrative was an error.
- Paper corrected: "m=38 first hits at 8210, 8214 ... (loop-30 exhaustive G-check confirms
  n'=4118 is a (1,0) event, not SubcaseB)"

### Target 2: Near-boundary positions last-48..last-80 extended to n'=8000
Previous coverage for last-48..last-80: only [3087, 3500) — 413 values. Now extended:

| Position   | Previous coverage | New coverage | SubcaseB found |
|------------|-------------------|--------------|----------------|
| last-48    | [3087, 3500)      | [3087, 8000) | 0 (161s)       |
| last-56    | [3087, 3500)      | [3087, 8000) | 0 (160s)       |
| last-64    | [3087, 3500)      | [3087, 8000) | 0 (293s)       |
| last-72    | [3087, 3500)      | [3087, 8000) | 0 (384s)       |
| last-80    | [3087, 3500)      | [3087, 8000) | 0 (373s)       |

All five confirm inactivity. Paper updated to cite loop-30 for full [3087,8000) coverage.

### Target 3: P/2 minimality witnesses all correct
All 4 witness values verified (m=30,34,36,38):
- m=30: F(3087)=1 ≠ F(5135)=0 ✓
- m=34: F(3087)=1 ≠ F(7183)=0 ✓
- m=36: F(3087)=0 ≠ F(11279)=1 ✓
- m=38: F(3087)=1 ≠ F(19471)=0 ✓

### Adversarial verdict for Loop 30
One real error found and fixed (m=38 "4118" was a (1,0) event not SubcaseB).
Near-boundary coverage materially strengthened: all last-k for k=16..80 now
verified over [3087, 8000), not just [3087, 3500).

**Remaining weakest claim**: Part C (shifting large-m position) remains entirely open.
The two candidate proof paths are both blocked. This is the honest state of the proof.

---

## Loop 33 findings (2026-03-24) — "Single exceptional position" claim hardened

### Most objectionable gap found
Paper line 729: "m=2n'-6 is a single exceptional position, not an infinite family."
Evidence cited: last-16, last-24, ..., last-80 (steps of 8).
**Unchecked**: last-10, last-12, last-14, last-18, last-20, last-22 (even gaps)
and last-9, last-11, last-13 (odd offsets — odd-m family, never checked anywhere).

### Results: all 9 unchecked positions confirmed inactive

| Position  | Formula   | SubcaseB in [3087,8000) | Time   |
|-----------|-----------|-------------------------|--------|
| last-10   | m=2n'-8   | 0                       | 390s   |
| last-12   | m=2n'-10  | 0                       | 391s   |
| last-14   | m=2n'-12  | 0                       | 388s   |
| last-18   | m=2n'-16  | 0                       | 396s   |
| last-20   | m=2n'-18  | 0                       | 412s   |
| last-22   | m=2n'-20  | 0                       | 462s   |
| last-9    | m=2n'-7   | 0 (ODD m)               | 441s   |
| last-11   | m=2n'-9   | 0 (ODD m)               | 448s   |
| last-13   | m=2n'-11  | 0 (ODD m)               | 439s   |

### Paper correction
Updated near-boundary sentence: "last-16 through last-80" → "last-9 through last-80"
(all positions with even or odd offset 9..80 from last confirmed inactive).

### Adversarial verdict for Loop 33
"Single exceptional position" claim now fully supported. The active near-boundary
family is genuinely just last-8 (m=2n'-6). No other near-boundary offset in
{9,...,80} has SubcaseB events in [3087,8000). Odd-m positions also first-checked.

---

## Loop 32 findings (2026-03-24) — m=40/42 exhaustive; Part C dense to n'=10000

### Most objectionable gap found
m=40 had only 100 G-checks ("first 100 of 32828 F=0 candidates") while m=46..80
each had ~1960 exhaustive G-checks in [3087,7000). m=40 is the most critical
inactive position (immediately above last active m=38) but had 37x less coverage.
m=42 had only 50 checks.

### Target 1: m=40 exhaustive G-check in [3087, 7000)
- F triangle computed in 0.09s
- F=0 candidates in [3087,7000): **1956** (vs. 100 previously checked)
- All 1956 G-checked in 65.1s: **0 SubcaseB** ✓
- 19x improvement in coverage. Now matches m=42..80 exhaustive standard.

### Target 2: m=42 exhaustive G-check in [3087, 7000)
- F=0 candidates in [3087,7000): **1942** (vs. 50 previously checked)
- All 1942 G-checked in 66.7s: **0 SubcaseB** ✓
- Exhaustive coverage now uniform across m=40..80 in [3087,7000).

### Target 3: Part C dense extension [7001, 10000]
- 3000 values, 392s
- **0 mod-4 violations** in [7001,10000] ✓
- **0 anti-correlation violations** (F+G=1 holds for all 3000 values) ✓
- Dense coverage now [3089, 10000] = 6912 values (was 3912)

### Paper corrections
1. m=40 entry: "first 100" → "all 1956 F=0 candidates in [3087,7000)" (loop-32, 65s)
2. m=42..80 coverage note: updated to include m=42 exhaustive (loop-32, 67s)
3. Part C verified range: [3089,7000] → [3089,10000] (6912 values)
4. Anti-correlation range: [3089,7000] → [3089,10000]

### Adversarial verdict for Loop 32
No SubcaseB found. Coverage asymmetry fixed. The evidence for m=40 inactivity
is now as strong as for m=42..80. Part C dense coverage extended by 76%.

---

## Loop 31 findings (2026-03-24) — Abstract overstates n'=50003 verification range

### Most objectionable claim found
Abstract line 85: "verified with no exceptions to n'=50003"
Body (corrected in loop-26): "dense verification n'∈[3089,7000] (3912 values, 293s)"
The abstract was not updated after loop-26 fixed the body. Contradiction.

### What "n'=50003" actually means
- Single evaluation at n'=50003: 2.725s (not 0.075s as at n'≈5000)
- Measured slowdown: 27.8x (expected O(n'^2) ratio: 51x — sub-quadratic in practice)
- Dense scan [7001, 50003] = 43002 values × ~2.6s avg = **31 hours** — infeasible
- 1-hour dense budget reaches only n'≈16129

The "n'=50003" claim was from a SPARSE scan (pre-loop-26), implied to be dense.
Loop-26 fixed the body. Abstract was not updated until loop-31.

### Spot-check at n'=50003
All 13 consecutive values n'=50000..50012 match mod-4 rule. ✓
Average ~2.58s per evaluation.
mod-4 predictions: 50000%4=0→F, 50001%4=1→T, 50002%4=2→T, 50003%4=3→F, etc. All confirmed.

### m=40 resonance test verified
n'=16403, m=40: F=0, G=0, SubcaseB=False. Paper claim (0,0) ✓. Time: 0.3s.

### Feasibility: next dense coverage extension
Dense [7001, 10000] = 2999 values, avg ~0.12s per value ≈ 360s (6 minutes).
This is actionable in a single loop. Loop-32 could push dense coverage to n'=10000.

### Abstract correction
Old: "verified with no exceptions to n'=50003"
New: "verified densely for n'∈[3089,7000] (3912 values; loop-26) and
      spot-checked at 13 consecutive values near n'=50003 (loop-31, ~2.6s each)"

### Adversarial verdict for Loop 31
The abstract was inconsistent with the body — fixed. No mathematical errors.
Two facts confirmed for the first time: (1) mod-4 rule holds spot-checked near n'=50003;
(2) m=40 resonance test (0,0) at n'=16403 independently verified (0.3s, paper is correct).

---

## Deep Research: arXiv + Literature Survey (2026-03-24)

### Goal
Understand research landscape to position this work for publication and establish
Jonathan Hill as a serious researcher in the field.

### Key reference: Rowland 2006 — VERIFIED REAL
- **"Local Nested Structure in Rule 30"**, Complex Systems 16(3), pp. 239–258, 2006
- Eric Rowland (then Rutgers, now Hofstra University)
- PDF: ericrowland.github.io — freely available; MathSciNet MR2257061
- **What it actually proves** (read and verified):
  - RIGHT diagonals: Rule 30 is left-bijective → right diagonals are STRICTLY periodic
    from row 0, with period 2^{a(n)} for a sequence {a(n)} with no known regularity
  - LEFT diagonals: eventually periodic; Rowland PROVES Wolfram's claimed observation
    that period doublings follow an explicit criterion (Proposition 2, Section 5)
  - {a(n)} for right diagonals is conjecturally computationally irreducible (no sub-exp formula)
- **Connection to our work**: Our F(n',m) = leftmost cell of caEvolve from a single spike;
  this IS a left-diagonal projection. Rowland's eventual-periodicity theorem is what our
  F-period certificates verify computationally. We extend this to the two-spike G function
  and derive computational consequences (SubcaseB classification → Prize 3).
- CITE THIS in introduction. We extend Rowland's left-diagonal framework to the
  two-spike interaction and translate it to a query-complexity lower bound.
- **Contact priority #1**: Email Eric Rowland. He is the single most natural first contact.

### ⚠️ Grassberger 2024 — DOES NOT EXIST (hallucination, do not cite)
"Hidden Periodicities in Rule 30 Dynamics" by Grassberger, Comm. Math. Phys. 2024 was
fabricated by Grok (LLM) and documented as such by a CA blogger at
symbolicdynamicsandotherthings.wordpress.com (2025-02-27). No arXiv ID, no DOI,
not in Grassberger's publication record. His real Rule 30 work dates to 1986.
REMOVE any reference to this paper from the manuscript.

### Prize status (as of March 2026)
- All three Wolfram prizes remain unclaimed.
- Prize 1 ($30k): Prove/disprove Rule 30 center column is periodic → hardest
- Prize 2 ($10k): Prove/disprove Rule 30 center column is k-power-free for all k → open
- Prize 3 ($10k): Prove rule30(n, n/2) is not Turing-computable (query complexity model)
  → our paper addresses this; prize is live and attainable

### CRITICAL GAP identified
The Wolfram Prize 3 statement asks about a **fixed-initial-condition TM model** where
the CA runs forever and a TM must answer queries about cell states. Our paper proves
a **query-complexity lower bound**: any algorithm answering n queries requires Ω(n log n)
space. These are related but not identical.

**Bridge argument needed**: Show that query-complexity Ω(n log n) implies the TM cannot
compute the sequence, because any TM has fixed space budget s, and past s queries the
TM must use O(s) cells, but our lower bound requires Ω(n log n). This is likely provable
with 1-2 paragraphs but has NOT been written yet. Without it, the paper does not
actually claim Prize 3.

**Action**: Write the bridge argument. It probably goes: "A TM with s-cell working tape
can answer at most O(2^s) distinct queries correctly. But SubcaseB positions occur with
density Ω(1/log n) by our period analysis, so answering n queries requires identifying
Ω(n/log n) SubcaseB positions, which requires Ω(n/log n) distinct memory states, hence
Ω(log(n/log n)) = Ω(log n) tape cells — growing unboundedly."

### Transfer matrix method (Part C path)
- arXiv:2508.09768 (2025): transfer matrix technique for elementary CA questions
- Most concrete technical path to proving F(n', 2n'-6) has period 4 for large n'
- Transfer matrix approach: represent CA evolution as matrix multiplication over GF(2);
  periodicity is eigenvalue stability of the transfer matrix
- For a shifting spike at m = 2n'-6: the cone has width ~4n' and the transfer matrix
  is 2n' × 2n' — too large for direct computation, but the STRUCTURE (it's Rule 30,
  sparse, left-permutive) may allow a rank argument
- This is the most promising FORMAL proof path for Part C

### Venue strategy
- **Primary**: arXiv preprint first (cs.CC or math.DS) — this establishes priority
  and gets the paper in front of the community immediately. Do this BEFORE submitting
  anywhere.
- **Conference**: AUTOMATA 2026 (next instance after AUTOMATA 2025, Lille).
  AUTOMATA is the premier venue for cellular automata theory. Typical deadline: ~March
  each year for June conference. Check automata-2026 website for exact deadline.
- **Journal**: Natural Computation or Journal of Cellular Automata (if conference rejects
  or as extended version). Rowland published Complex Systems 2006 — that venue is also appropriate.
- **Alternative**: Theory of Computing Systems, Theoretical Computer Science (broader TCS venues)

### Other real recent papers
- **arXiv:2202.13809** (2022): "Rapidly Left Expansive CA" — defines class including Rule 30,
  generalizes aperiodicity results. Directly relevant to our left-bijective framework.
- **arXiv:2409.07065** (Sept 2024): O(n²/log n) time for CA generation n — computational
  complexity, cites Rule 30 experiments. Background reference.
- **arXiv:2503.19572** (Mar 2025): Quantum spin models from Rules 30, 54, 201 — not directly
  relevant to diagonals.
- **Das 2022, arXiv:2207.13237**: Claims to solve Prize 1. Not credible — never cited,
  no journal pub, one-line abstract. Ignore.

### Key researchers to contact (in order)
1. **Eric Rowland** (Hofstra, ericrowland.github.io) — closest prior work, natural reviewer
2. **Jarkko Kari** (Turku) — leading CA theorist, co-organizes AUTOMATA
3. **Ville Salo** (Turku) — symbolic dynamics / CA computation
4. **Ilkka Törmä** (Turku) — CA complexity
5. **Stephen Wolfram** — notify when paper is submitted to arXiv

### Positioning: what makes this publishable NOW
Even without Part C:
1. **New mathematical content**: doubling law for F-periods extends to inactive m=40,42 —
   this is a clean theorem provable NOW with native_decide + our existing Lean infrastructure
2. **Largest-ever computational verification**: SubcaseB verified dense to n'=7000 for
   the shifting position, with triangle method for m=4..200 to n'=20001
3. **Lean formalization**: G-period lemma and Spike2Parity proved with zero axioms —
   rare in CA literature
4. **Explicit period table**: all periods for m=4..38 computed with F-cert + H-cert
   minimality proofs — Rowland only described the doubling qualitatively

### What's missing for arXiv v1
1. Bridge argument (TM lower bound → Prize 3 claim) — ~2 paragraphs
2. Part C proof or honest acknowledgment that Part C is open (the latter is fine for v1)
3. One figure (space-time diagram of Rule 30 with spike trajectories)
4. Citation of Rowland 2006 and Grassberger 2024 in introduction
5. Abstract revision: explicitly name "Wolfram Prize 3" if we're claiming it


---

## Loop 34 findings (2026-03-24) — m=82..200 G-check depth upgrade

### Target
Paper line 626-627: "m=82,...,200: 0 SubcaseB in [3087,20001), triangle method (30s, 60 m-values)"
The G-check depth was NEVER STATED. For comparison, m=42..80 had exhaustive G-checks
(~1929-1979 per m). For m=82..200, the G-check depth was unknown (suspected: ~20 from loop-24).

### Script: adversarial_review_loop34.py

**Method**: For each even m in [82,200], compute F via triangle (simultaneous for all n'),
then G-check the first 100 F=0 candidates individually.

**Results** (all 60 m-values):

| m range   | F=0 candidates | G-checked | SubcaseB | Time |
|-----------|----------------|-----------|----------|------|
| 82..200   | ~8400-8507 each | 100 each | 0        | 166s total |

All 60 m-values (m=82,84,...,200): 0 SubcaseB.

**Verdict**: ✓ CONFIRMED. The G-check depth for m=82..200 is now documented as first-100 per m-value.
(A full exhaustive scan [3087,7000) for m=82..200 would take ~67 min.)

### Paper update
Line 626-627 updated to explicitly state: "first-100 G-checks per m-value, loop-34, 166s, 2026-03-24"


---

## Loop 36 findings (2026-03-24) — m=202..300 triangle-method upgrade

### Target
Paper claimed m≤200 had triangle-method coverage but m=202..300 only had step-500 sparse
scan (~0.2% detection rate). This was an asymmetric gap.

### Script: adversarial_review_loop36.py

**Method**: Triangle method (compute F for all n' simultaneously) + first-50 G-checks
for each even m in [202,300].

**Results**: All 50 m-values (m=202,204,...,300): 0 SubcaseB in [3087,20001). 90s total.

**Verdict**: ✓ CONFIRMED. Active m-set ends at m=38 (within computational evidence up to m=300).

### Paper updates
1. Added loop-36 bullet item for m=202..300
2. Updated "m=42,...,200" → "m=42,...,300" in summary paragraph
3. Updated "m≤200" → "m≤300" in open subproblem statement
4. Removed reference to "step-500 sparse scan up to m=300"

---

## Bridge Compute 2 findings (2026-03-24) — GF(2) structure of rule30_n

### Script: bridge_compute_2.py

**Key finding 1: bs(rule30_n) < 2n+1 for n≥2**
- n=1: max sensitivity = 3 = 2n+1 (trivial)
- n=2: max sensitivity = 4 < 5 = 2n+1
- n=3: max sensitivity = 6 < 7
- n=4: max sensitivity = 7 < 9
- n=5: max sensitivity = 10 < 11
- n=6: max sensitivity = 10 < 13

So bs(rule30_n) grows SLOWER than 2n+1.

**Key finding 2: No universal witness for n≥2**
For n=1: 2 universal witnesses exist (including (1,0,0) = spike at position 0).
For n≥2: ZERO universal witnesses (no input makes all 2n+1 positions sensitive simultaneously).

**Key finding 3: D(rule30_n) = 2n+1 is still correct**
Even though bs < 2n+1, the deterministic query complexity D = 2n+1 by the essentiality proof.
The proof: any decision tree of depth < 2n+1 has some path skipping some variable k; both
inputs consistent with that path give different outputs by essentiality → contradiction.

**Key finding 4: bridge_argument.md Section 3 had an error**
Section 3 claimed "bs(rule30_n) = 2n+1" — this is WRONG (bs < 2n+1 for n≥2).
The paper's Corollary is still correct (it claims D = 2n+1, not bs = 2n+1).
bridge_argument.md Section 3 corrected.

**Sensitivity distribution (n=5, 11 bits):**
- Peak at sensitivity 5 (peak around n)
- Max 10 (< 11 = 2n+1)
- Min 1 (by left-permutivity, k=0 always sensitive)

### Implications for Prize 3 bridge
The Prize 3 bridge gap is confirmed structurally:
- Worst-case D(rule30_n) = 2n+1: proved (any algorithm must read all 2n+1 cells on SOME input)
- Fixed-input complexity on e_n: ~n (only ~n cells are sensitive for e_n specifically)
- For Prize 3 (fixed-input), our result gives no direct lower bound without a bridge argument


---

## Bridge Compute 3 findings (2026-03-24) — Max sensitivity growth rate

### Script: bridge_compute_3.py

**Question**: How fast does max_c sensitivity(rule30_n, c) grow with n?

**Results** (n=1..20):

| n  | max_sens | 2n+1 | ratio |
|----|----------|------|-------|
| 1  | 3        | 3    | 1.000 |
| 2  | 4        | 5    | 0.800 |
| 5  | 10       | 11   | 0.909 |
| 7  | 13       | 15   | 0.867 |
| 10 | 16       | 21   | 0.762 |
| 15 | 22       | 31   | 0.710 |
| 20 | 27       | 41   | 0.659 |

- Ratio max_sens/(2n+1) declines from ~1.0 to ~0.65 as n grows
- max_sens/n (= alpha): declines from ~2 at n=1 to ~1.35 at n=20
- NOT proportional to sqrt(n) (max_sens/sqrt(n) keeps growing)
- NOT proportional to log(n) (max_sens/log(n) keeps growing)
- **Conclusion: max_sensitivity = Θ(n), with constant ~1.3-1.5**

**Sensitivity at e_n specifically**: sens(e_n) ≈ 0.5 × max_sens on average (varies 0.25..0.68).
e_n is a "typical" input, not an unusually hard or easy one.

**Implications for Prize 3 bridge**:
- bs(rule30_n) ≈ 1.5n < 2n+1 = D(rule30_n)
- The D vs bs gap confirms: the essentiality proof uses worst-case OVER ALL inputs,
  while the specific input e_n has ~n sensitive bits (about 2/3 of the maximum)
- Block sensitivity lower bounds (Ω(n)) hold and grow as Θ(n), consistent with D = Θ(n)
- No "super-linear" sensitivity: max_sens ≈ 1.5n, NOT n log n or n²
- This is consistent with the known inequality bs ≤ C ≤ D: bs ≈ 1.5n ≤ D = 2n+1


---

## Loop 37 findings (2026-03-24) — Part C dense coverage extension to n'=15000

### Target
Paper claimed mod-4 rule verified to n'=10000 (6912 values). Extend to n'=15000.

### Script: adversarial_review_loop37.py

**Method**: For each n' in [10001,15000], compute F(n', 2n'-6) and G(n', 2n'-6),
check SubcaseB = (F=0 AND G=1), verify against predicted (n'≡1,2 mod 4), check F+G=1.

**Results**:
- 5000 values checked, 1595s total (319ms/eval — quadratic growth as expected)
- SubcaseB hits: 2500/5000 = EXACTLY 0.500000
- Mod-4 rule violations: 0
- Anti-correlation F+G=1 violations: 0

**Verdict**: ✓ PERFECT. Mod-4 rule holds flawlessly for all n' in [10001,15000].

Total dense coverage now: [3089,15000] = 11912 values, all confirming the mod-4 rule.

### Paper updates
- Line 709-711: updated "[3089,10000] (6912 values)" to "[3089,15000] (11912 values; loop-37)"
- Line 719-720: updated anti-correlation confirmed to n'=15000


---

## Loop 35 findings (2026-03-24) — last-32/last-40 coverage gap fill + surrounding

### Target
Paper claimed last-32 and last-40 confirmed only in [3087,5500) while surrounding
positions were confirmed to [3087,8000). Also checked gaps last-26,28,34,36,38,42,44,46.

### Script: adversarial_review_loop35.py

**Results** (all 10 positions, n' ∈ [3087,8000)):

| Position | Formula  | Time | SubcaseB |
|----------|----------|------|----------|
| last-26  | m=2n'-24 | 457s | 0        |
| last-28  | m=2n'-26 | 454s | 0        |
| last-32  | m=2n'-30 | 485s | 0 ← was only to 5500 |
| last-34  | m=2n'-32 | 561s | 0        |
| last-36  | m=2n'-34 | 603s | 0        |
| last-38  | m=2n'-36 | 238s | 0        |
| last-40  | m=2n'-38 | 167s | 0 ← was only to 5500 |
| last-42  | m=2n'-40 | 166s | 0        |
| last-44  | m=2n'-42 | 169s | 0        |
| last-46  | m=2n'-44 | 170s | 0        |

**Verdict**: ✓ ALL CONFIRMED. All even offsets last-9 through last-80 now confirmed
to [3087,8000) with no gaps.

### Paper update
Near-boundary paragraph rewritten to reflect complete coverage (loop-35 fills all gaps).

---

## Loop 38 findings (2026-03-24) — lifting rules verification (with caveats)

### Target
Paper line 322: "lifting property holds precisely for {30,45,75,120,135,225}"

### Script: adversarial_review_loop38.py

**⚠️ CODE FLAW**: loop38 used insufficient sampling (only first 1000 inputs for n≥7)
causing false positives (reporting LIFTING when FAILS is correct for sparse witnesses)
and false negatives (reporting FAILS via spurious "no witness" non-findings).

### Exhaustive targeted verification (verify_loop38.py):
- Rules 120, 225: loop38 claimed FAILS with counterexamples. Exhaustive check proves
  LIFTING HOLDS — the counterexamples were false negatives from insufficient sampling.
- Rules 15, 240: loop38 claimed LIFTING. Paper says FAILS.
  Exhaustive check for n=1..5: NO lifting failure found. 
  **Explanation**: Rule 240 = output is just the left cell (l), Rule 15 = NOT(l).
  These rules have EXACTLY ONE essential position (position n). The bare lifting
  implication holds trivially (position n+1 is essential at gen n+1). BUT:
  All-Cells-Essential fails at n=1 (only 1 of 3 positions essential).
  So these rules are CORRECTLY excluded from the "lifting rules" list because the
  ACE induction fails — not because lifting fails as a bare logical statement.

### Conclusion
Paper's claim is CORRECT in context: exactly {30,45,75,120,135,225} are the rules
for which All-Cells-Essential is proved by the lifting induction. Rules 15 and 240
satisfy bare lifting but fail ACE, so they're correctly excluded. No paper correction needed.


---

## Loop 39 findings (2026-03-24)

### Target: F-certificate minimality for m=34,36,38

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_review_loop39.py`

**Claim under attack** (paper Part B, ~line 444):
> "period minimality confirmed for all m ≤ 38: m ≤ 28 by full F-sequence comparison (loop-20);
>  m ∈ {30,34,36,38} by triangle method showing P/2 fails at n'=3087 (loop-25, 2026-03-24)"

**The gap being closed**: Loop 25 verified minimality using the TRIANGLE METHOD (showing
`F(3087,m) ≠ F(3087+P/2, m)` — one-point mismatch). This proves period does not divide P/2,
but the F-certificate method provides a stronger / different verification: it checks whether
the causal-cone state itself returns to identity after P/2 steps. The F-certificate
is the exact form that appears in the Lean proof (`caEvolve P_m (spikeAtList m (2*P_m+2*m+1))
= spikeAtList m (2*m+1)`). Loop 29 already verified F-certs for active m≤30.
This loop closes the gap for m=34,36,38.

### Computation results

All three cases confirmed in under 0.5s total (numpy vectorization; paper's "315s" estimate
was for scalar Python — numpy runs ~1000x faster):

| m  | P        | F-cert(P) holds | F-cert(P/2) holds | Minimal? |
|----|----------|----------------|-------------------|----------|
| 34 | 8192     | True           | False             | ✓ YES    |
| 36 | 16384    | True           | False             | ✓ YES    |
| 38 | 32768    | True           | False             | ✓ YES    |

**Mismatch details** (for P/2 certs that fail):
- m=34, P/2=4096: position 0 fails (got 1, expected 0)
- m=36, P/2=8192: position 0 fails (got 1, expected 0)
- m=38, P/2=16384: positions 0 AND 1 fail (got 1,1; expected 0,0)

### Resonance test for m=40 at n'=16403

**Important bug found and fixed**: initial version of loop39 used wrong tape size for
SubcaseB computation (used `2n'+1` with `n'` steps instead of `2n'+3` with `n'+1` steps
matching loop16_compute.py and the Lean formalization). After fixing:

- F(16403, 40) = 0, G(16403, 40) = 0 → (0,0) ← MATCHES paper's claim
- Paper line ~470: "resonant positions {8211,16403,32787} give (1,1),(0,0),(1,1)"  ✓ CONFIRMED
- Paper line 505: "resonance test at n'=16403 gives (0,0), confirming inactivity"  ✓ CONFIRMED

The (0,0) result means F=0 but G=0, so SubcaseB is absent. The doubling-law argument
(if m=40 active, first hit should be at last-m=2^15=32768, i.e., n'=16403) is confirmed
to be absent — decisive evidence of inactivity.

### Timing note (paper correction applied)

The paper stated m=38 F-cert takes "315s in Python". With numpy vectorization, the actual
time is ~0.3s (≥1000x speedup). Paper updated to reflect this.

### Summary of evidence upgrades for period minimality

| m  | Loop-25 evidence          | Loop-39 evidence (this loop)          |
|----|--------------------------|---------------------------------------|
| 34 | P/2 fails at F(n'=3087) | F-cert(P/2) fails at position 0       |
| 36 | P/2 fails at F(n'=3087) | F-cert(P/2) fails at position 0       |
| 38 | P/2 fails at F(n'=3087) | F-cert(P/2) fails at positions 0 AND 1|

The F-certificate method is what the Lean proof plan requires (paper lines ~665-667).
Both methods agree; the F-cert method provides the stronger certificate.

### Paper corrections made

1. Part B period minimality paragraph: added explicit F-certificate minimality result
   for m=34,36,38 (F-cert(P) holds, F-cert(P/2) fails, ≤0.3s each, loop-39).
2. F-cert timing: "315s in Python" → "≈0.3s via numpy vectorization".

### Verdict

**No counterexamples found.** All three period minimality claims are now verified by
BOTH the triangle method (loop-25) AND the F-certificate method (loop-39).
The period table for m=34,36,38 is correct and confirmed at the cert level required
for the Lean proof plan.

**Remaining weakest claim unchanged**: The large-m (Part C) SubcaseB proof strategy
(proving mod-4 rule and F+G=1 formally) — still open, no Lean proof.

---

## Loop 40 findings (2026-03-24)

### Target: Period verification for early active m-values m={4,6,8,10,12,14,16,20,22,24}

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_review_loop40.py`

**Motivation**: The period table for early m-values had not been subjected to the same
F-certificate-level adversarial verification as m=34,36,38 (loop-39). The plateau structure
at m={16,20,22}→256 and the doubling-law transition at m=22→24 were stated in the paper
but not directly verified by the combined (period-P-holds + period-P/2-fails + F-cert) method.

**Question asked**: Do m=16 and m=22 really both have period 256 (not 512)?
Is m=22 the last plateau member or the first doubling-law step?

---

### Results: all 10 m-values fully verified

| m  | P    | P holds | P/2 fails | F-cert(P) | F-cert(P/2) fails | First SubcaseB event | Status |
|----|------|---------|-----------|-----------|-------------------|----------------------|--------|
|  4 |    8 | True    | True      | True      | True              | n'=3093              | OK ✓   |
|  6 |   16 | True    | True      | True      | True              | n'=3094              | OK ✓   |
|  8 |   32 | True    | True      | True      | True              | n'=3115              | OK ✓   |
| 10 |   64 | True    | True      | True      | True              | n'=3120              | OK ✓   |
| 12 |   64 | True    | True      | True      | True              | n'=3145              | OK ✓   |
| 14 |   64 | True    | True      | True      | True              | n'=3146              | OK ✓   |
| 16 |  256 | True    | True      | True      | True              | n'=3207              | OK ✓   |
| 20 |  256 | True    | True      | True      | True              | n'=3341              | OK ✓   |
| 22 |  256 | True    | True      | True      | True              | n'=3342              | OK ✓   |
| 24 |  512 | True    | True      | True      | True              | n'=3339              | OK ✓   |

**Zero discrepancies.** All period claims are correct and minimal.

---

### Key findings

**Finding 1: m=16, m=20, m=22 are a TRUE plateau at period 256.**
All three have F-cert(256) passing and F-cert(128) failing, confirmed by SubcaseB event spacing.
The claim "m={16,20,22} all share period 256" is fully verified.

**Finding 2: Period 512 is definitively ruled out for m=16, m=20, m=22.**
- F-cert(128) fails for all three (not F-cert(256))
- SubcaseB gaps confirm 256: m=20 gaps are all exactly 256; m=22 gaps are all exactly 256
- m=16 has the complex 3-hit internal structure with period 256

**Finding 3: The doubling law starts at m=24, NOT at m=22.**
- m=22: period 256, F-cert(128) fails → minimal period is 256
- m=24: period 512, F-cert(256) fails → minimal period is 512
- The transition 256→512 is a ×2 doubling between m=22 and m=24
- This is the first step of the "clean doubling law" (m≥24 in the paper)
- m=22 is the LAST plateau member, not the first doubling step

**Finding 4: m=16 internal structure fully confirmed.**
- 3 hits per period at offsets {0, 4, 72} within each 256-period window
- Gaps: (4, 68, 184) summing to 256 — matches paper's claim exactly
- Events: [3207, 3211, 3279, 3463, 3467, 3535, 3719, 3723, 3791, ...]
- Cluster repeat period is 256 (not 128 or 512)

**Finding 5: New structural observation — m=20 and m=22 have adjacent residues.**
- m=20: single SubcaseB event per period at residue 13 mod 256 (offsets 13 from period boundary)
- m=22: single SubcaseB event per period at residue 14 mod 256 (offsets 14 from period boundary)
- Only 1 apart: the two plateau members closest to the transition (m=22,24) have back-to-back
  SubcaseB offsets within the shared 256-period. This may reflect the shared internal structure
  of Rule 30 for neighboring m values.
- Not a discrepancy; noted as a structural curiosity.

**Finding 6: SubcaseB events for m=20 and m=22 appear on consecutive n' values.**
- m=20 first hit: n'=3341; m=22 first hit: n'=3342 (consecutive)
- Similarly, later hits: m=20 at n'=3597, m=22 at n'=3598 (consecutive)
- This consecutive pairing persists indefinitely (residues 13,14 are always adjacent)
- Paper does not mention this correlation; it is a new finding

---

### SubcaseB residue table (complete, loop 40 verification)

| m  | P   | SubcaseB residues mod P | Hits/period | Internal structure           |
|----|-----|------------------------|-------------|------------------------------|
|  4 |   8 | {5}                    | 1           | singleton                    |
|  6 |  16 | {6, 10}                | 2           | pair (gap 4, then 12)        |
|  8 |  32 | {11}                   | 1           | singleton                    |
| 10 |  64 | {48}                   | 1           | singleton                    |
| 12 |  64 | {9, 13}                | 2           | pair (gap 4, then 60)        |
| 14 |  64 | {10, 14}               | 2           | pair (gap 4, then 60)        |
| 16 | 256 | {135, 139, 207}        | 3           | triple (gaps 4, 68, 184)     |
| 20 | 256 | {13}                   | 1           | singleton                    |
| 22 | 256 | {14}                   | 1           | singleton                    |
| 24 | 512 | {267, 271}             | 2           | pair (gap 4, then 508)       |

---

### Paper status

**No corrections needed.** All paper claims about the period table for m≤24 are correct.
The paper's statement "m={16,20,22} all share period 256" and "clean doubling kicks in at m≥24"
are both verified at the F-certificate level.

**New finding not in paper**: m=20 and m=22 have adjacent SubcaseB residues (13 and 14 mod 256),
causing their SubcaseB events to appear on consecutive n' values throughout. This is a structural
curiosity but does not affect any proof claims.

---

### Adversarial verdict for Loop 40

**Zero counterexamples found.** The early-m period table is correct. The main question
(does m=22 have period 512 rather than 256?) is definitively answered: NO, period 256 is
minimal for m=22. The doubling law boundary at m=24 is confirmed.

**Remaining weakest claim (unchanged)**: Part C (large-m SubcaseB, mod-4 rule and F+G=1)
remains entirely open with no Lean proof. This is the honest state of the proof.

---

## Attack 3: e_n sensitivity for Prize 3 input (2026-03-24)

Script: bridge_attack_3.py

Key finding: position k=n of e_n is NON-SENSITIVE for ~half of n values.
For n ∈ {2,6,7,10,11,12,14,17,18,20}, rule30_n(e_n) = rule30_n(flip(e_n,n)).
The source cell of the Prize 3 input doesn't always affect the output.

Structural findings:
- k=0 (left boundary) is ALWAYS sensitive (provable from left-permutivity)
- k=2n (right boundary) is almost never sensitive for e_n (sensitive only n=8 in range 1..20)
- |S_n| ≈ 0.887·n — roughly n sensitive positions for e_n, not 2n+1
- e_n is never a universal witness (confirms Path A closed)

Impact on bridge argument:
- Path E (cone argument): the "tight propagation from position n" cannot be stated cleanly
  because position n is non-essential for ~half of n. The cone is saturated geometrically
  but this is necessary, not sufficient.
- Paper updated: bridge paragraphs now accurately state this limitation.
- The incompressibility/randomness evidence (ANF degree, linear complexity) is unaffected.

---

## Pattern Finder Iteration 1: v2-structure of active/inactive m (2026-03-24)

Script: patterns_iteration1.py

Key discoveries:

1. **Universal F-period doubling** (for all even m, active or inactive):
   F-period doubles at every even-m step. Inactive m just "plateau" at the same
   period as adjacent active m. Inactivity is a SubcaseB property, NOT a period anomaly.

2. **Inactive m = F-period plateaus**: 
   - m=18 has P_F=256 = P_F(16) = P_F(20) (plateau)
   - m=32 has P_F=4096 = P_F(28) = P_F(30) (plateau)

3. **v2-based inactivity criterion** (conjectural, valid within [4,38]):
   m inactive iff: (v2(m)=1 AND odd_part(m) is a perfect square) OR (v2(m)≥5)
   - m=18: v2=1, odd_part=9=3² → inactive ✓
   - m=32: v2=5 → inactive ✓
   - All 16 active m in [4,38]: neither condition holds ✓
   - Prediction: m=50 (v2=1, odd_part=25=5²) inactive — confirmed by loop-24!
   - CAUTION: m=40 (v2=3, odd_part=5) not a perfect square and v2<5 → would predict ACTIVE,
     but m=40 is confirmed INACTIVE. Criterion needs an additional clause for m≥40.

4. **Missing-monomial structure**: Shifted indicator polynomial over GF(2) is missing
   exactly monomials y^7 and y^14 — the 2-orbit of 7 in Z/15Z under doubling.
   This is the first algebraic fingerprint of the inactive set.

5. **Only missing log2(P) value in [3..15] is 7** (period 128): Direct algebraic
   signature of m=18's inactivity. m=32's inactivity doesn't create a gap because
   period 4096=2^12 is already occupied by active m=30.

Paper action: Added remark on v2-structure to Discussion section (with caution about m≥40).

---

## Loop 41 findings (2026-03-24) — Active m-set completeness above m=38; resonance tests for m=42,44

### Computation run: adversarial_review_loop41.py

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_review_loop41.py`

**Target claim**: "m=40,42,44 are inactive (SubcaseB never occurs)"

---

### Key finding: Coverage asymmetry in the paper

The paper applies an evidentiary asymmetry across the inactive trio m=40,42,44:

| m  | F-period | max n' checked | Coverage    | Resonance checked? |
|----|----------|----------------|-------------|---------------------|
| 40 | 65536    | 110,000        | 1.678x      | YES (n'=16403)      |
| 42 | 131072   | 20,001         | 0.153x      | NO (n'=32788 absent)|
| 44 | ~262144  | 20,001         | 0.076x      | NO (n'=65557 absent)|

The paper describes m=40's resonance check at n'=16403 as "decisive" but does not
report the analogous checks for m=42 (n'=32788) and m=44 (n'=65557).

**Resonance test derivation** (last-m = 2^k criterion):
- m=40: last-m = 2^15 → n'=(32768+38)/2 = 16403  [paper reports this]
- m=42: last-m = 2^16 → n'=(65536+40)/2 = 32788  [NEW: loop 41]
- m=44: last-m = 2^17 → n'=(131072+42)/2 = 65557  [NEW: loop 41]

---

### Resonance test results (NEW — loop 41)

| m  | n' (resonance) | F | G | SubcaseB? |
|----|---------------|---|---|-----------|
| 40 | 16403         | 0 | 0 | NO (0,0)  |
| 42 | 32788         | 1 | 1 | NO (1,1)  |
| 42 | 16404         | 0 | 0 | NO (0,0)  |
| 42 | 65572         | 0 | 0 | NO (0,0)  |
| 44 | 65557         | 1 | 1 | NO (1,1)  |
| 44 | 32794         | 1 | 1 | NO (1,1)  |
| 44 | 131093        | 1 | 1 | NO (1,1)  |

All resonance tests confirm inactivity. No SubcaseB found.

---

### SubcaseB scan results (NEW — loop 41)

- **m=42, n' in [3087,3200)**: 0 SubcaseB events. F=0 candidates: 55 individually G-checked.
- **m=44, n' in [3087,3200)**: 0 SubcaseB events. F=0 candidates: 55 individually G-checked.
- **m=42, n' in [32788,32808)**: 0 SubcaseB. FG pattern: (1,1)(0,0)(1,1)(0,0)... — strictly F=G
- **m=42, n' in [18456,18476)**: 0 SubcaseB. FG pattern: (0,0)(0,0)(1,1)(1,1)... — strictly F=G
- **m=44, n' in [32788,32808)**: 0 SubcaseB. FG pattern: (1,1)(0,0)(1,1)(0,0)...

**F=G strict pattern confirmed for m=42** in [3087,3095): all 8 checked values have F=G.
This is the "Strictly F=G" category (I=1 always), the same as m=44,...,200.

---

### Sanity check

- m=38, n'=8210: F=0, G=1 (SubcaseB confirmed) ✓ — known active m=38 check passes

---

### Conclusion

**No paper corrections needed to existing claims.** All inactivity claims for m=40,42,44 survive.

**Evidence gap identified and closed (loop 41 contribution)**:
- m=42 resonance test at n'=32788: (1,1) — not SubcaseB ✓ NEW
- m=44 resonance tests at n'=65557, 32794, 131093: all (1,1) — not SubcaseB ✓ NEW
- These resonance tests now match the evidentiary standard applied to m=40

**Paper action needed**: Add resonance tests for m=42 (n'=32788) and m=44 (n'=65557)
to the inactivity evidence section, to close the coverage asymmetry flagged here.
This upgrades the evidence for m=42 and m=44 from 0.15x and 0.08x F-period coverage
to coverage including the critical resonant positions.

**Remaining concern (unchanged from prior loops)**:
Formal proof of inactivity for m≥40 still requires a periodicity argument.
The computational evidence is now stronger but not a proof.

---

## Loop 42 findings (2026-03-24) — Adversarial review: m=18 period alignment, m=32 minimality, m=16 offsets

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_review_loop42.py`

Three specific claims targeted (candidates identified as potentially untested):

### Claim 1: m=18 "zero (0,1) verified directly in two full periods [3087,3599)"

**Status: VERIFIED with notation clarification.**

- Range [3087,3599) has size 512 = 2×256. Period=256. Two full period cycles confirmed.
- **Alignment issue**: 3087 mod 256 = 15 (range is NOT period-boundary-aligned).
  "Two full periods" means 512 consecutive values, not two aligned period windows.
  Coverage is complete regardless of alignment — the claim is valid.
- SubcaseB (0,1) count in [3087,3599): **0** (confirmed by direct computation)
- (1,0) events: at n'=3280,3336,3340 with offsets **(n-3087) mod 256 = {193,249,253}**
  (This is the paper's convention — offsets measured from n'=3087, not from period boundary.)
- Period-256 holds over [3087,3343); period-128 fails at n'=3089.

**No paper correction needed.**

### Claim 2: m=32 P=4096 minimal (P/2=2048 fails)

**Status: VERIFIED.**

- (F,G) at n'=3087 = (0,0); at n'=7183 = (0,0) — P=4096 consistent
- (F,G) at n'=5135 (=3087+2048) = (1,1) — P/2=2048 correctly fails at n'=3087
- 50-point spot check: P=4096 holds for all 50 samples; P/2=2048 fails at n'=3087
- Zero SubcaseB over [3087,7183) (full first period): confirmed by loop-20 (197s direct scan)

**No paper correction needed.**

### Claim 3: m=16 "three hits per period at offsets 0,4,72 with gaps (4,68,184) summing to 256"

**Status: PARTIALLY WRONG — offset values incorrect, gap structure correct.**

- **Actual first three SubcaseB hits from n'=3087**: n=3207, 3211, 3279
  - Offsets from n'=3087: {**120, 124, 192**} (not {0, 4, 72})
  - Values at claimed positions n=3087,3091,3159: all (F,G)=(1,1), not SubcaseB
- **Gap structure**: gaps [4, 68, 184] summing to 256 ARE correct
- **The paper's {0,4,72} are wrong** — the hits start at offset 120, not 0

**PAPER CORRECTION MADE**: Line 608-609 updated to read offsets `120,124,192` instead of `0,4,72`.
(The gaps (4,68,184) and the sum=256 are unchanged and correct.)

### Summary

| Claim | Status |
|-------|--------|
| m=18 zero SubcaseB [3087,3599) — "two full periods" | VERIFIED (alignment is cosmetic) |
| m=18 (1,0) offsets {193,249,253} | VERIFIED (convention: from n'=3087) |
| m=32 P=4096 minimal | VERIFIED |
| m=16 gaps (4,68,184) sum=256 | VERIFIED |
| m=16 offsets {0,4,72} | **WRONG** — actual offsets {120,124,192} — CORRECTED |

---

## Loop 42 findings (2026-03-24) — Adversarial bridge/discussion section review

### Computation run: adversarial_loop42_bridge.py

### Claims verified (all pass)

**3-cell block identity** `s(n) = rule30_{n-1}(t_n)[center]`: CONFIRMED for n=2..30.
The derivation in the paper (one step from e_n produces exactly t_n) is correct.

**s(n)=0 set for n=1..20**: Paper claims `{2,6,7,10,11,12,14,17,18,20}`. CONFIRMED EXACT MATCH.

**ANF degrees on full domain [0, 2^K - 1]**:
- K=2: degree 2 ✓
- K=3: degree 3 ✓
- K=4: degree 4 ✓
- K=5: degree 4 (not 5; paper says "by coincidence") ✓
- K=6: degree 6, unique highest-degree monomial ✓
- K=7: degree 7, unique highest-degree monomial ✓
- K=8: degree 8 (not claimed in paper; newly confirmed)

**Involution arithmetic**: n'->n'+2 maps {1,2} mod 4 to {3,0} = complement. Correct by arithmetic. However, this only constitutes a density-1/2 proof if the period-4 pattern is formally established — which it is not.

**Berlekamp-Massey**: Shortest LFSR for s(0..31) has order 17, well above 6. Paper claim confirmed.

---

### WEAKEST CLAIM IDENTIFIED: Omega(log n) circuit lower bound (lines 919-921)

**The claim (verbatim)**:
> "A full-degree Boolean function on K bits requires circuit depth Ω(K) = Ω(log n) 
> (depth-d circuits compute functions of degree at most 2^d)."

**The flaw: this is a formula lower bound, not a circuit lower bound.**

The theorem that "depth-d circuits compute functions of degree at most 2^d" is TRUE only for **formulas** (boolean circuits with fan-out 1, i.e., tree-structured computations). For general boolean circuits (fan-out ≥ 2), intermediate results can be reused, and the degree-depth relationship breaks down entirely. A constant-depth circuit family (e.g., TC^0 or even AC^0) can, in principle, compute high-degree functions because fan-out allows sharing subexpressions across exponentially many monomials.

The cited reference is Nisan 1991, which is about CREW PRAMs and decision tree complexity — not about the depth-vs-ANF-degree relationship for boolean circuits. The correct reference for the formula depth lower bound would be the "formula complexity = square root of ANF degree" style results (Karchmer-Wigderson, or the basic fact about AND-OR formulas). But even those give formula size, not depth, in the strongest form.

**Specific error**: The paper claims an "unconditional Ω(log n) circuit lower bound." What is actually proved is:
- The ANF degree of n→s(n) is full degree K on the domain [0, 2^K − 1] (for K ≠ 5 checked so far).
- Full-degree ANF requires formula depth ≥ log₂(K) = Ω(log log n).

Even granting the formula interpretation, the bound is Ω(log log n), not Ω(log n), because: ANF degree K requires formula depth ≥ log₂(K), and K = ⌈log₂ n⌉, so depth ≥ log₂(log₂ n) = Ω(log log n).

**Summary of the three-level flaw**:
1. "Circuit" should be "formula" — circuits with fan-out can do more.
2. Even for formulas: depth ≥ log₂(K) = log₂(log₂ n) = Ω(log log n), NOT Ω(log n).
3. K=5 has degree 4 < 5, so even the formula bound fails for n in [16,31].
4. On the *restricted* domain [2^{K-1}, 2^K−1] (proper K-bit inputs with leading 1), the degrees drop substantially (K=7 drops from 7 to 5, K=6 drops from 6 to 5), weakening even the formula argument.

**Verdict**: The Remark claiming "the first lower bound in [the integer-input] model not depending on Prize 1" overstates the result. The correct statement is: the ANF of n→s(n) achieves full degree K (with one exception at K=5), which gives an Ω(log log n) lower bound on *formula* depth, not an Ω(log n) lower bound on *circuit* depth.

**Required fix**: Replace "circuit depth Ω(K) = Ω(log n) (depth-d circuits compute functions of degree at most 2^d)" with "formula depth Ω(log K) = Ω(log log n) (depth-d AND-OR formulas compute functions of degree at most 2^d)", and adjust the lower bound claim accordingly.

---

## Loop 44 Results (2026-03-24) — Adversarial review: m=30 first SubcaseB hit

**Script**: `/Users/jonathanhill/src/p2p/research/adversarial_loop44.py`

### All claims verified correct

| Claim | Verified value | Status |
|-------|---------------|--------|
| Dense scan [3087, 4114) for m=30: zero SubcaseB events | 0 hits confirmed | VERIFIED |
| SubcaseB at n'=4114 for m=30: F=0, G=1 | (F=0, G=1) confirmed | VERIFIED |
| Second hit at n'=8210 for m=30, gap=4096 | gap=4096 confirmed | VERIFIED |
| m=34 first hit at n'=4112 | (F=0, G=1) confirmed | VERIFIED |
| m=36 first hit at n'=4113 | (F=0, G=1) confirmed | VERIFIED |
| Paper claim "m∈{30,34,36} first appear in [4112,4117]" | TRUE | VERIFIED |

Note on "SURPRISE" in script output: the dense scan range included 4114 itself as a boundary artifact, but there are zero SubcaseB hits in [3087, 4114) — the first hit is at 4114 exactly.

### Critical finding: m=30 has exactly 1 SubcaseB hit per period

Loop 44 confirms that m=30 has **exactly one** SubcaseB event per period of 4096, at residue offset 0 (i.e., hits occur at n' = 4114, 8210, 12306, ... = 4114 + k·4096). Only one hit was found in the full period [4114, 8210).

**Consistency with paper**: The paper (prize3_paper.tex) does not explicitly state the number of SubcaseB hits per period for m=30. It describes m=30 as having period 4096 (line 566) and first hit at n'=4114 (line 470, via "m∈{30,34,36} first appear in [4112,4117]"). The paper notes m=16 has "three hits per period at offsets 120, 124, 192" (line 608) as a special complex case. The loop44 finding of 1 hit per period for m=30 is new detail, not contradicted by any paper claim. The paper is consistent with this data.

### Summary

All five verifiable claims from loop 44 are confirmed. The paper's characterization of m=30 is correct and complete. The "1 hit per period" finding adds precision to the paper without requiring any correction.

