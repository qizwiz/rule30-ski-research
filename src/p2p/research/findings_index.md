# findings.md Section Index
# Total lines: 5830
# Format: TITLE (lines START-END): SUMMARY

## Adversarial Review Loop #2 (2026-03-26) — Period Doubling & Inactivity m=40,42 (lines 3-56): Paper line 704: "universal F-period doubling P{m+2}=2Pm holds for all even m in [2,42]"
## Adversarial Review Loop #1 (2026-03-26) — Active Set / Inactive m (lines 57-81): Lines 615-618 of prize3paper.tex: "m=82,...,200 confirmed over [3087,20001) with first-100
## Loop 72-73-74 Structural Witness Analysis (2026-03-25) (lines 82-154): Scripts: `adversarialloop72antidiagwitness.py`, `adversarialloop73witnessstructure.py`, `adversarialloop74largemwitness.
## SubcaseB Period Table — CORRECTED (2026-03-26) (lines 155-199): Script: `looplcmfast.py` + inline checks. All periods verified over 3× via simulation.
## Part C Dense Check COMPLETE (2026-03-24) (lines 200-211): Range: n' in [17001, 50001) — 33000 values
## Linearity Corridor Proof (2026-03-24) — G = 1-F on k=6 diagonal (lines 212-265): Result: `G(n', 2n'-6) = 1 - F(n', 2n'-6)` for all n'≥4.
## Ramanujan Deep Exploration (2026-03-24) — GF(2) structure of M_act (lines 266-298): Script: `research/ramanujandeep1774409643.py`
## C-Tool Inactive-m Coverage Extension (2026-03-24) (lines 299-317): Using `rule30subcaseB` C tool (220x speedup over Python):
## Loop 59 findings (2026-03-24) — Attack: Exhaustive G-check m=202..300 (even) in [3087,3500) (lines 318-366): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop59.py`
## Loop 58 findings (2026-03-24) — Attack: m=36 SubcaseB completeness in [3087,5000) + spot-checks (lines 367-440): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop58.py`
## Loop 57 findings (2026-03-24) — Attack: m=34 SubcaseB completeness within one period (lines 441-516): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop57.py`
## Loop 49 findings (2026-03-24) — Attack: period table plateau claims (lines 517-620): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop49.py`
## Loop 48 findings (2026-03-24) — Attack: discussion section and bridge argument (lines 621-750): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop48.py`
## Loop 47 findings (2026-03-24) — Attack 1: m in [40,60]; Attack 2: weakest sentence (lines 751-857): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop47.py`
## Loop 45 findings (2026-03-24) — Adversarial attack: are "inactive" m in [2,38] truly inactive? (lines 858-907): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop45.py`
## Loop 46 findings (2026-03-24) — Adversarial attack: can we find a fast algorithm for s(n)? (lines 908-966): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop46.py`
## Loop 45 findings (2026-03-24) — Fast inactive-m scan: m∈{2,18,32} (lines 967-1014): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop45.py`
## Loop 44 findings (2026-03-24) — Adversarial review: m=30 first SubcaseB hit; m∈{30,34,36} range claim (lines 1015-1079): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop44.py`
## Loop 43 findings (2026-03-24) — Adversarial density/involution review: m=2n'-6 SubcaseB (lines 1080-1148): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop43density.py`
## Loop 20 findings (2026-03-24) — Adversarial review: active m-set, inactivity, period minimality (lines 1149-1274): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop20v4.py`
## Loop 16 findings (2026-03-23) — m=40 confirmed NOT active; active set terminates at m=38 (lines 1275-1314): Summary: Comprehensive multi-scan adversarial review finds no (0,1) event for m=40
## Loop 19 findings (2026-03-23) — Lean period certificates added; SubcaseB proof architecture (lines 1315-1352): spikeAtList infrastructure (added):
## Loop 18 findings (2026-03-23) — native_decide cost estimate corrected; all certificates verified (lines 1353-1360): Adversarial target: paper said O(P × (2m+1)) ≈ 2.5M ops for m=38 nativedecide certificate.
## Loop 17 findings (2026-03-23) — Sweep coverage corrected; m=42..60 verified inactive (lines 1361-1372): Adversarial target: paper overclaimed "step-100 to n'=45000 for all m≤80" — only m=40,42 were scanned that far.
## Loop 15 findings (2026-03-23) — m=38 RECLASSIFIED AS ACTIVE (lines 1373-1421): Critical error corrected: m=38 was previously classified as "weakly inactive" (only (1,0),
## Loop Summary (2026-03-23, adversarial rounds 8–10) (lines 1422-1513): - m=36: period 16384 = 2^14 (NOT 4096; confirmed by 20497=4113+16384, 20501=4117+16384, 24593=8209+16384)
## Loop 20 Adversarial Review (2026-03-24) (lines 1514-1550): Q1: Active m-set completeness (VERIFIED for m=4..28)
## Status (2026-03-23) (lines 1551-1567): - `Spike2Parity.lean`: `rule30n(n'+1)(spike2) = (n' mod 2 == 0)` — fully proved
## SubcaseB Structure — CORRECTED (2026-03-23) (lines 1568-1617): - WRONG formula used in early Python scripts: spike at center+mval
## Major Structural Finding: Active vs Inactive m Values (2026-03-23) (lines 1618-1687): - Short-period active (first hit in [3087,3343), period ≤256):
## Proof Plan (Revised 2026-03-23) (lines 1688-1715): Three parts:
## Lifting Lemma Characterization (lines 1716-1730): - Rule 90:  g(c,r) = r        — odd-HW? g(1,0)=0, g(0,1)=1, g(1,1)=0 → HW=1 odd, but lifting FAILS
## Files to Read Next Session (lines 1731-1738): - `/Users/jonathanhill/src/p2p/P2p/LiftingLemmaLeftPermutive.lean` lines 1770-1790 (SubcaseB sorry)
## Loop 21 findings (2026-03-24) — Adversarial review: Part C large-m family mod-4 claim (lines 1739-1829): > "SubcaseB(n', 2n'-6) = true iff n' ≡ 1 or 2 (mod 4), for all n' ≥ 3089."
## Loop 21 Post-Processing — Paper Updates Applied (lines 1830-1846): Date: 2026-03-24
## Loop 22 findings (2026-03-24) — Adversarial review: m=34,36,38 SubcaseB claims and LCM (lines 1847-2016): Script: `/Users/jonathanhill/src/p2p/research/adversarialreviewloop22.py`
## Loop 23 findings (2026-03-24) — F+G=1 at critical range, build status, smaller-period search (lines 2017-2061): CausalConeLemmas.lean builds clean: 763 jobs, 0 errors after removing crashing m=34..38 certs.
## Loop 24 findings (2026-03-24) — Adversarial attack on m-set completeness (lines 2062-2116): Paper: "m=44,...,80: no events in [3087, 4500) (original sweep)"
## Loop 25 findings (2026-03-24) — Period minimality m=34,36,38 + stale-reference fix (lines 2117-2160): 1. Paper lines 492-494: stale "m=42 verified [3087,5000)" and "m=44..80 verified [3087,4500)"
## Loop 26 findings (2026-03-24) — Honest dense-verification of SubcaseB mod-4 rule (lines 2161-2211): Paper: "verified with no exceptions through n'=50003" for SubcaseB(n', 2n'-6) mod-4 rule.
## Loop 27 findings (2026-03-24) — F-period certificates for m=40,42 + doubling law extended (lines 2212-2272): 1. Body text (lines 458-460): stale "m=42,...,80 in [3087,4500)" — FIXED (loop-24 triangle results)
## Loop 28 findings (2026-03-24) — Step-100 scan is invalid evidence; deprecated (lines 2273-2313): Paper lines 420-422: "a comprehensive sweep of all even m∈[4,80] over n'∈[3087,45000)
## Loop 29 findings (2026-03-24) — F-period certs for all active m=4..30; SubcaseB patterns (lines 2314-2366): Paper describes periods for active m=4..30 but F-period certificates (the Lean-proof-style
## Loop 30 findings (2026-03-24) — m=38 error found and fixed; near-boundary extended (lines 2367-2406): Paper line 560 claimed "m=38 hits at 4118, 8210, 8214". Adversarial check:
## Loop 33 findings (2026-03-24) — "Single exceptional position" claim hardened (lines 2407-2439): Paper line 729: "m=2n'-6 is a single exceptional position, not an infinite family."
## Loop 32 findings (2026-03-24) — m=40/42 exhaustive; Part C dense to n'=10000 (lines 2440-2476): m=40 had only 100 G-checks ("first 100 of 32828 F=0 candidates") while m=46..80
## Loop 31 findings (2026-03-24) — Abstract overstates n'=50003 verification range (lines 2477-2516): Abstract line 85: "verified with no exceptions to n'=50003"
## Deep Research: arXiv + Literature Survey (2026-03-24) (lines 2517-2631): Understand research landscape to position this work for publication and establish
## Loop 34 findings (2026-03-24) — m=82..200 G-check depth upgrade (lines 2632-2660): Paper line 626-627: "m=82,...,200: 0 SubcaseB in [3087,20001), triangle method (30s, 60 m-values)"
## Loop 36 findings (2026-03-24) — m=202..300 triangle-method upgrade (lines 2661-2683): Paper claimed m≤200 had triangle-method coverage but m=202..300 only had step-500 sparse
## Bridge Compute 2 findings (2026-03-24) — GF(2) structure of rule30_n (lines 2684-2725): Key finding 1: bs(rule30n) < 2n+1 for n≥2
## Bridge Compute 3 findings (2026-03-24) — Max sensitivity growth rate (lines 2726-2763): Question: How fast does maxc sensitivity(rule30n, c) grow with n?
## Loop 37 findings (2026-03-24) — Part C dense coverage extension to n'=15000 (lines 2764-2790): Paper claimed mod-4 rule verified to n'=10000 (6912 values). Extend to n'=15000.
## Loop 35 findings (2026-03-24) — last-32/last-40 coverage gap fill + surrounding (lines 2791-2821): Paper claimed last-32 and last-40 confirmed only in [3087,5500) while surrounding
## Loop 38 findings (2026-03-24) — lifting rules verification (with caveats) (lines 2822-2852): Paper line 322: "lifting property holds precisely for {30,45,75,120,135,225}"
## Loop 39 findings (2026-03-24) (lines 2853-2934): Script: `/Users/jonathanhill/src/p2p/research/adversarialreviewloop39.py`
## Loop 40 findings (2026-03-24) (lines 2935-3049): Script: `/Users/jonathanhill/src/p2p/research/adversarialreviewloop40.py`
## Attack 3: e_n sensitivity for Prize 3 input (2026-03-24) (lines 3050-3072): Script: bridgeattack3.py
## Pattern Finder Iteration 1: v2-structure of active/inactive m (2026-03-24) (lines 3073-3107): Script: patternsiteration1.py
## Loop 41 findings (2026-03-24) — Active m-set completeness above m=38; resonance tests for m=42,44 (lines 3108-3192): Script: `/Users/jonathanhill/src/p2p/research/adversarialreviewloop41.py`
## Loop 42 findings (2026-03-24) — Adversarial review: m=18 period alignment, m=32 minimality, m=16 offsets (lines 3193-3249): Script: `/Users/jonathanhill/src/p2p/research/adversarialreviewloop42.py`
## Loop 42 findings (2026-03-24) — Adversarial bridge/discussion section review (lines 3250-3305): 3-cell block identity `s(n) = rule30{n-1}(tn)[center]`: CONFIRMED for n=2..30.
## Loop 44 Results (2026-03-24) — Adversarial review: m=30 first SubcaseB hit (lines 3306-3333): Script: `/Users/jonathanhill/src/p2p/research/adversarialloop44.py`
## Loop 49 (simulation bug found) + Loop 50 (fix + reconfirmation) (lines 3334-3360): Loop 49 verdict: FALSE ALARM — the script had a simulation bug.
## Loop 51: Large-m period doubling law (lines 3361-3375): Verified period doubling for m=24..34 using correct diagonal-read simulation:
## Loop 52: Part C mod-4 rule extended (lines 3376-3382): Verified SubcaseB(n', 2n'-6) = (n'≡1,2 mod 4) for ALL n'∈[15001,15100] (dense, 60s) with 0 violations.
## SubcaseB G-check for active m (lines 3383-3396): Verified actual SubcaseB (F=0 AND G=1) occurs in one period for each active m:
## Loop 54 + CausalConeLemmas.lean (2026-03-24) (lines 3397-3428): lcm(Pm : m ∈ Mact) = 32768 = 2^15 CONFIRMED.
## Loop 54 — Full Results (2026-03-24) (lines 3429-3449): - All 50 m-values have F=0 candidates (~8440-8460 per m in [3087,20001))
## Loop iteration-4 findings (2026-03-24) — Ramanujan pattern search (lines 3450-3485): Script: `research/patternsiteration4.py`
## Ramanujan Opus Agent findings (2026-03-24) — patterns_ramanujan.md (lines 3486-3536): Most important: algebraic characterization of lifting lemma
## Loop 57 + Ramanujan binomial findings (2026-03-24) (lines 3537-3569): - All 4096 F=0 candidates in [3087,11279) individually G-checked (659s)
## Fermat denominator theorem (2026-03-24) — VERIFIED (lines 3570-3593): At period-starts (m where Lm = Pm/2 + 1), the 2-adic fraction αm/(2^{Pm}-1)
## Fermat denominator mechanism (2026-03-24) — COMPLETE THEOREM (lines 3594-3622): Source: ramanujanloop1774399697.md (a0f3cf903 agent)
## Three-class structure of F-sequences (abf0be06 agent, 2026-03-24) (lines 3623-3648): Source: ramanujanloop1774400235.md
## Loop 61 findings (2026-03-24) — m=38 SubcaseB re-verification with correct simulation (lines 3649-3676): Gap: m=38 SubcaseB at {8210,8214} was documented in loop-30, but loop-30 predates the
## Ramanujan Diagonal Structure Theorem (2026-03-24) — (F,G) joint distribution on diagonals m=2n'-k (lines 3677-3736): Computed (F,G) joint distribution across 200 samples on each diagonal m=2n'-k for k=2..14.
## Loop 59, 62, 63 findings (2026-03-24) — coverage upgrades (lines 3737-3785): Gap closed: loop-36 verified [3087,20001) with first-50 G-checks. Loop-59 adds exhaustive G-check of ALL F=0 in [3087,35
## Small-m SubcaseB re-verification (2026-03-24) — correct simulation (lines 3786-3819): Active m ∈ {4,6,8,10,12,14,16,20,22} SubcaseB positions were documented pre-loop-50.
## Adversarial Loop 1774413233 (2026-03-24): Period Table Error + BM Convergence (lines 3820-3878): The period table in `prize3paper.tex` lists:
## Adversarial Loop 1774415697 (2026-03-25) — BM warning, density, Lucas, anti-diagonal (lines 3879-3923): Script: `research/adversarialloop1774415697.py`
## Adversarial Loop 2026-03-25 — Termination Formula Corrected (lines 3924-3976): Scripts: `research/adversarialterminationformula.py`, `research/adversarialterminationdeep.py`
## LFSR Defect Arithmetic Progression (2026-03-25) (lines 3977-4006): Source: Ramanujan script bksj75qdh Part H output
## Mod-8 Termination Formula — Full Verification (2026-03-25) (lines 4007-4027): Source: adversarialterminationdeep.py (btdndp59d), runtime 921s
## Adversarial M_act Completeness Verification (2026-03-25) (lines 4028-4061): Script: `research/adversarialmactcompleteness.py`
## Large-m SubcaseB Hit Verification (2026-03-25) (lines 4062-4088): Attack: verify the claimed first SubcaseB hits for m=34,36,38 (the three largest active m).
## L_34 = 4097 CONFIRMED — LFSR Plateau-Start Pattern (2026-03-25) (lines 4089-4126): Script: `research/loop1774421888VERIFY.py`
## Run C LFSR Table COMPLETED — L_36=8193, L_38=24578 (2026-03-25) (lines 4127-4166): Script: `research/loop1774422600VERIFY.py`
## Extended M_act Completeness — m∈[2,60] Confirmed (2026-03-25) (lines 4167-4198): Source: background task b8gcuzgm3 (fastmactcheck.py), runtime 4653s
## Attack: SubcaseB per period + L_32 (loop 1774428000, 2026-03-25) (lines 4199-4241): Script: `research/loop1774428000ATTACK.py`
## SubcaseB Periodicity Extended to m=34,36 (adversarial loop 1774432000, 2026-03-25) (lines 4242-4276): Script: `research/loop1774432000ATTACK.py`
## Inactive m=40 BM Result: L_40=57347, d_40=8189 (loop 1774432000, 2026-03-25) (lines 4277-4303): L40 = 57347, P40 = 65536, d40 = 8189 = d38 - 1
## Adversarial Verification of Structural Claims (loop 1774435000, 2026-03-25) (lines 4304-4338): 1. Complement-half condition for m=34,36 (attack loop 1774435000)
## CRITICAL CORRECTION: Period-doubling law (loop 1774435000, 2026-03-25) (lines 4339-4364): Finding: The paper claimed m={18,32} are the ONLY even m violating period-doubling. This is WRONG.
## d_42=8188 CONFIRMED: step-(-1) law through inactive m=42 (loop 1774435000, 2026-03-25) (lines 4365-4384): L42 = 122884, P42 = 131072, d42 = 8188
## EXPLORE: d_actual Threshold Criterion + Full LFSR Table (loop 1774433717, 2026-03-25) (lines 4385-4435): Key theorem discovered: `dactual(m) ≤ 4 ↔ flat chain; dactual(m) ≥ 5 ↔ period doubles.`
## ATTACK: m=32 conn poly confirmed — Mersenne-inner + Run-B inapplicability (2026-03-25) (lines 4436-4456): Question: Why d32=4 instead of d=251 (Run-B formula d=267-m/2=267-16=251)?
## ATTACK: Threshold criterion scope fix + Run-A text contradiction (loop 1774444000, 2026-03-25) (lines 4457-4471): Bug found: The criterion "d≤4 ↔ flat chain for m∈[4,42]" was wrong.
## ATTACK: m=44 NOT a plateau start (loop 1774444000-B, 2026-03-25) (lines 4472-4494): Hypothesis: (+1,+4) log2 P pattern predicts m=44 as next plateau start (log2 P=18).
## ATTACK: m=36 SubcaseB count table correction (loop 1774444000-C, 2026-03-25) (lines 4495-4509): Bug found: Constant-count table said "m=36: 2 SBs/period" but actual count is 3.
## SYNTHESIZE: Three LFSR defect regimes (2026-03-25) (lines 4510-4532): The defect dm = Pm - Lm follows THREE distinct regimes, not a universal step-(-1) law:
## EXPLORE: Unified LFSR formula (loop 1774460000, 2026-03-25) (lines 4533-4557): Discovery: All six doubling regimes governed by single formula:
## ATTACK: m=36 SubcaseB count WRONG AGAIN — 4th found (loop 1774461800, 2026-03-25) (lines 4558-4589): Bug found: Paper said "m=36: 3 SBs/period" (corrected from 2 in prev loop). Actual is ≥4.
## EXPLORE: m=34 does NOT have the {a,a+4,a+P/4,a+4+3P/4} singletons (loop 1774461800-B) (lines 4590-4602): Question: Does m=34 also have extra SBs at a+P/4=3073 and a+4+3P/4=7173?
## ATTACK: m=16,24 exhaustive re-verification + m=36 exactly 4 SBs (loop 1774463600, 2026-03-25) (lines 4603-4621): m=16 (P=256) full sweep: 3 SBs at offsets {120,124,192} — CONFIRMED, no hidden SBs. ✓
## VERIFY: lcm(P_m for active m) = 32768 confirmed (loop 1774463600-B, 2026-03-25) (lines 4622-4631): Claim: The overall SubcaseB witness period is lcm of individual active m periods = 32768 = 2^15.
## CRITICAL BUG FOUND: Active m-Set Classification (2026-03-25) (lines 4632-4677): Status: The classification lemma `subcaseBonlyactivem` in SubcaseBPeriod.lean was WRONG.
## SubcaseB Proof Architecture — Full Complexity Assessment (2026-03-25) (lines 4678-4714): - Active m-set has EXPONENTIALLY GROWING periods: 512, 1024, 2048, 4096, ...
## m=22 Sorry Close: n''=2830 / w=32 / P=4096 (2026-03-31) (lines 4715-4804): The sorry at SubcaseBPeriod.lean line 2344 (j≡1 mod 2 subcase, n'=35598+32768l)
## m=4 SubcaseB Axiom — Tree Structure Analysis (2026-03-31) (lines 4805-4958): `subcaseBm4ge3087` remains the only unproved component theorem.
## Session 2026-03-31 — Visualization + Linearity Corridor Corrections (lines 4959-5042): The proof document `research/linearitycorridorproof.md` claims lemma 3:
## CA_Array_m4 build completed (2026-03-31, loop60) (lines 5043-5050): CAArraym4.lean built successfully: 765 jobs, 2444 seconds.
## m=4 SubcaseB hierarchy NOT bounded (2026-03-31, loop60) (lines 5051-5075): CORRECTION: Prior session claimed "max minw=42, bounded oscillation."
## m=4 Level 3 Period Measurements (loop61, 2026-03-31) (lines 5076-5150): | Config | Period divides | Minimal period | Tape size at cert |
## Rule 90 Embedding & Algebraic Proof Structure (loop62, 2026-03-31) (lines 5151-5271): Rule 30 decomposes over GF(2) as:
## m=22 l≡0 sorry CLOSED: w=6, P=256 (loop63, 2026-03-31) (lines 5272-5342): The m=22 l≡0 sorry at SubcaseBPeriod.lean line 2354 (n'=35598+65536s) is now proved.
## Loop 64 (2026-03-31) — Build Analysis, Ski-Prize Assessment, m28/m30 Residue Plan (lines 5343-5625): CAArray.lean build COMPLETED successfully at 11:43AM (5.4h, 765 jobs).
## Loop 76 (2026-04-01) — Loop63 claim refuted; m=22 sorry algebraic barrier confirmed (lines 5626-5698): Loop63 claimed the sorry at SubcaseBPeriod.lean:2281 (n'=35598+65536s, m=22) was closed
## Track B3: Prize 2 / Prize 3 Connection Analysis (loop82, 2026-04-01) (lines 5699-5761): Question: Is the Prize 2 center-column sequence the same as our F(n', m=4) sequence?
## Track B4: m=22 LFSR Analysis — Algebraic Barrier Confirmed (loop84) (lines 5762-5830): Question: Can the sorry at line 2417 (n'=35598+65536s, s≡0 mod 2) be closed by
