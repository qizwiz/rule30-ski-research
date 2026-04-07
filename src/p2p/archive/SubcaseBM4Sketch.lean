/-
SubcaseBM4Sketch.lean — Type-holed proof skeleton for subcaseB_m4_ge3087
==========================================================================

PURPOSE: Expose the exact Lean goals for the m=4 algebraic proof using
type holes (?_). This file WILL NOT compile — that's intentional. Running
  lake build P2p.SubcaseBM4Sketch
prints every open goal. This maps the full proof landscape without OOM.

PROOF STRUCTURE:
  subcaseB_m4_ge3087
  ├── Level 0 (n'≡5 mod 8, n'≢42 mod 64, n'≢5 mod 512): sensitivity_transfer w=6, P=8
  │     └── ?goal_period_cert_ts64_p8          ← twoSpike(6,4) period=8 cert needed
  ├── Level 0b (n'≡42 mod 64): sensitivity_transfer w=32, P=4096
  │     └── ?goal_period_cert_ts324_p4096       ← twoSpike(32,4) period=4096 cert needed
  ├── Level 1 (n'≡5 mod 1024, n'≢5 mod 4096): sensitivity_transfer w=30, P=4096
  │     └── ?goal_period_cert_ts304_p4096       ← twoSpike(30,4) period=4096 cert needed
  ├── Level 2 (n'≡5 mod 4096, n'≢5 mod 16384): sensitivity_transfer w=34, P=16384
  │     └── ?goal_period_cert_ts344_p16384      ← twoSpike(34,4) period=16384 cert needed
  └── Level 3+ (n'≡5 mod 16384): ?goal_algebraic_d_field  ← D-field / Rule 90 proof
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas

namespace P2p

/-
==============================================================================
SECTION 1: What we need from hcase + hts
==============================================================================

SubcaseB fires at m=4 means:
  hcase : rule30n (n'+1) (spike_at_4) = false   -- F_4(n') = 0
  hts   : rule30n (n'+1) (spike_4 ∨ spike_last) = true  -- G_{4,last}(n') = 1

These translate to:
  hcase₄ : caEvolve (n'+1) (spikeAtList 4 N) center = false
  hts₄   : caEvolve (n'+1) (twoSpikeLastList 4 N) center = true

Key fact: hcase₄ tells us spike_4 evolves to 0 at center at step n'+1.
-/

/-
==============================================================================
SECTION 2: Period certs NOT YET IN THE CODEBASE
==============================================================================

These are the missing pieces for levels 0-2:
-/

-- NEEDED: twoSpike(6,4) period=8 cert (for Level 0, n'≡5 mod 8 base cases)
-- Tape size: 2*8 + 2*(max 6 4) + 1 = 16 + 12 + 1 = 29
-- Expected: caEvolve 8 (twoSpikeList 6 4 29) = twoSpikeList 6 4 13
-- Verify: caEvolve 8 [F,F,F,F,F,F,T,F,F,T,F,F,F,F,F,F,F,F,F,F,F,F,F,F,F,F,F,F,F] = [...]
-- (need to check if period is actually 8 or something larger)
lemma caEvolve_cert_ts64_p8 :
    caEvolve 8 (twoSpikeList 6 4 29) = twoSpikeList 6 4 13 := by
  ?_caEvolve_cert_ts64_p8_goal  -- EXPOSE GOAL: is this even true?

-- NEEDED: spike(32) period=4096 cert (for Level 0b, n'≡42 mod 64)
lemma caEvolve_cert_sp32_p4096 :
    caEvolve 4096 (spikeAtList 32 8257) = spikeAtList 32 65 := by
  ?_sp32_p4096_goal

-- NEEDED: twoSpike(32,4) period=4096 cert (for Level 0b)
lemma caEvolve_cert_ts324_p4096 :
    caEvolve 4096 (twoSpikeList 32 4 8257) = twoSpikeList 32 4 65 := by
  ?_ts324_p4096_goal

-- NEEDED: spike(30) period=4096 cert (for Level 1, n'≡5 mod 1024)
-- (may already exist in CausalConeLemmas under different name)
-- caEvolve_cert_m30_p4096 ?
lemma caEvolve_cert_sp30_p4096 :
    caEvolve 4096 (spikeAtList 30 8253) = spikeAtList 30 61 := by
  ?_sp30_p4096_goal

-- NEEDED: twoSpike(30,4) period=4096 cert (for Level 1)
lemma caEvolve_cert_ts304_p4096 :
    caEvolve 4096 (twoSpikeList 30 4 8253) = twoSpikeList 30 4 61 := by
  ?_ts304_p4096_goal

-- NEEDED: spike(34) period=16384 cert (for Level 2, n'≡5 mod 4096)
lemma caEvolve_cert_sp34_p16384 :
    caEvolve 16384 (spikeAtList 34 32837) = spikeAtList 34 69 := by
  ?_sp34_p16384_goal

-- NEEDED: twoSpike(34,4) period=16384 cert (for Level 2)
lemma caEvolve_cert_ts344_p16384 :
    caEvolve 16384 (twoSpikeList 34 4 32837) = twoSpikeList 34 4 69 := by
  ?_ts344_p16384_goal

/-
==============================================================================
SECTION 3: Base sensitivity certs for each level's base case
==============================================================================

These need to be verified: at the specific base n'' for each level,
does the chosen witness w give actual sensitivity?
-/

-- Level 0: base n'=3085, w=6 (already exists as subcaseB_m4_base_sens)
-- Level 0b: base n'=3429, w=32 — NEEDS VERIFICATION
-- Is 3429 ≡ 42 mod 64? 3429 = 53*64 + 37. Hmm, 3429 mod 64 = 37, not 42.
-- Actually per CLAUDE.md: j=42 means n'=3429 (k=42 in k≡42 mod 64 starting from some base)
-- Let's expose what the actual residue is:
lemma subcaseB_m4_base_sens_level0b :
    (caEvolve 3430 (spikeAtList 32 6861)).getD 0 false ≠
    (caEvolve 3430 (twoSpikeList 32 4 6861)).getD 0 false := by
  ?_level0b_base_goal  -- native_decide once cert confirmed

-- Level 1: bases at n'=5125 and n'=7173 (per CLAUDE.md), w=30
lemma subcaseB_m4_base_sens_level1a :
    (caEvolve 5126 (spikeAtList 30 10253)).getD 0 false ≠
    (caEvolve 5126 (twoSpikeList 30 4 10253)).getD 0 false := by
  ?_level1a_base_goal

lemma subcaseB_m4_base_sens_level1b :
    (caEvolve 7174 (spikeAtList 30 14349)).getD 0 false ≠
    (caEvolve 7174 (twoSpikeList 30 4 14349)).getD 0 false := by
  ?_level1b_base_goal

-- Level 2: bases at n'=4101, 8197, 12293 (per CLAUDE.md), w=34
lemma subcaseB_m4_base_sens_level2a :
    (caEvolve 4102 (spikeAtList 34 8205)).getD 0 false ≠
    (caEvolve 4102 (twoSpikeList 34 4 8205)).getD 0 false := by
  ?_level2a_base_goal

lemma subcaseB_m4_base_sens_level2b :
    (caEvolve 8198 (spikeAtList 34 16397)).getD 0 false ≠
    (caEvolve 8198 (twoSpikeList 34 4 16397)).getD 0 false := by
  ?_level2b_base_goal

lemma subcaseB_m4_base_sens_level2c :
    (caEvolve 12294 (spikeAtList 34 24589)).getD 0 false ≠
    (caEvolve 12294 (twoSpikeList 34 4 24589)).getD 0 false := by
  ?_level2c_base_goal

/-
==============================================================================
SECTION 4: Level 3+ algebraic lemma (the hard part)
==============================================================================

For n'≡5 mod 16384, n'≥16389: no finite w works via native_decide.
Need: algebraic proof that sensitivity holds for all such n'.

THE KEY LEMMA: D-field zero at center.

For twoSpike configuration (spikes at w and 4), the "interaction term"
  D[i][t] := evolve(spike_w ⊕ spike_4)[i][t] ⊕ evolve(spike_w)[i][t] ⊕ evolve(spike_4)[i][t]
evolves by Rule 90. D first appears at position ≥ n'+3 (computationally verified),
and Rule 90 spreads the left boundary by ≤ 1 per step.

At step T-1 = n', the left boundary of D is ≥ n'+3 - 1 = n'+2 > center = n'+1.
So D[center][T-1] = 0, meaning:
  evolve(twoSpike_{w,4})[center][T-1] = evolve(spike_w)[center][T-1] ⊕ evolve(spike_4)[center][T-1] ⊕ 0

Combined with hcase (evolve(spike_4)[center][T] = 0):
  ...this gives the sensitivity at step T, not T-1.

[TODO: clarify the exact step arithmetic and which configuration gives the final center bit]

The LEAN GOALS that need to be filled:
-/

/-- Rule 90: D_{t+1}[i] = D_t[i-1] ⊕ D_t[i+1].
    (This needs to be proved using caEvolve properties — expose the goal.) -/
lemma rule90_step (A B : List Bool) (t : Nat) (i : Nat) :
    let D := fun s => List.zipWith xor (caEvolve s (List.zipWith xor A B))
                        (List.zipWith xor (caEvolve s A) (caEvolve s B))
    (D (t+1)).getD i false =
    xor ((D t).getD (i-1) false) ((D t).getD (i+1) false) := by
  ?_rule90_goal  -- this is the main algebraic content; expose the goal type

/-- D-field left boundary: for twoSpike(6,4) with n'≥5, the D-field at step n'
    has all-zero positions up to n'+2 (inclusive). -/
lemma d_field_left_zero_m4 (n' : Nat) (hn' : 5 ≤ n') :
    ∀ i ≤ n' + 2,
    let N := 2*(n'+1)+1
    let D := fun t => List.zipWith xor (caEvolve t (twoSpikeList 6 4 N))
                        (List.zipWith xor (caEvolve t (spikeAtList 6 N)) (caEvolve t (spikeAtList 4 N)))
    (D n').getD i false = false := by
  ?_d_field_left_zero_goal  -- EXPOSE GOAL: what does Lean want here?

/-- Consequence: sensitivity at center for level 3+ (algebraic). -/
lemma subcaseB_m4_sensitivity_level3 (n' : Nat) (hn' : 16389 ≤ n') (h_mod : n' % 16384 = 5) :
    (caEvolve (n' + 1) (spikeAtList 6 (2*(n'+1)+1))).getD 0 false ≠
    (caEvolve (n' + 1) (twoSpikeList 6 4 (2*(n'+1)+1))).getD 0 false := by
  ?_level3_sensitivity_goal  -- EXPOSE GOAL: the full statement Lean needs

/-
==============================================================================
SECTION 5: Full type-holed proof of subcaseB_m4_ge3087
==============================================================================

With all pieces in place (even as holes), we can write the full proof structure.
This shows exactly what the proof WOULD look like when all holes are filled.
-/

/-- Full type-holed proof of the m=4 SubcaseB axiom. -/
theorem subcaseB_m4_ge3087_typehole (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1)) (hm4 : m.val = 4)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Witness selection depends on level; we use different w per level.
  -- For the SKELETON, use w=6 (works at levels 0, 3+; others need different w).
  -- A production proof would use omega-style case splits to pick w.
  --
  -- STEP 1: Level triage via n' mod 16384
  --   (exposing the case split goals)
  by_cases h3 : n' % 16384 = 5
  · -- Level 3+: algebraic proof with w=6
    use spikeConfig 6 n'
    refine ⟨spikeConfig_odd_false 6 (by norm_num) n', ?_⟩
    rw [rule30n_spikeConfig_eq 6 n',
        rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
    simp only [hm4]
    -- GOAL HERE: expose the exact goal Lean sees after simp only [hm4]
    exact ?_level3_goal
  · by_cases h2 : n' % 4096 = 5
    · -- Level 2: w=34, P=16384
      use spikeConfig 34 n'
      refine ⟨spikeConfig_odd_false 34 (by norm_num) n', ?_⟩
      rw [rule30n_spikeConfig_eq 34 n',
          rule30n_flipCell_spikeConfig_eq' 34 n' m (by omega) (by omega)]
      simp only [hm4]
      -- Period reduce to base and apply sensitivity_transfer
      obtain ⟨k, hn'_eq⟩ := periodReduce_diff 4101 16384 n' (by omega) ?_hge
      -- GOAL: expose what periodReduce gives us
      exact ?_level2_transfer_goal
      · ?_level2_hge  -- n' ≥ 4101
    · by_cases h1 : n' % 1024 = 5
      · -- Level 1: w=30, P=4096
        use spikeConfig 30 n'
        refine ⟨spikeConfig_odd_false 30 (by norm_num) n', ?_⟩
        rw [rule30n_spikeConfig_eq 30 n',
            rule30n_flipCell_spikeConfig_eq' 30 n' m (by omega) (by omega)]
        simp only [hm4]
        exact ?_level1_transfer_goal
      · -- Level 0: further split on n' mod 64
        by_cases h0b : n' % 64 = 42
        · -- Level 0b: n'≡42 mod 64, use w=32, P=4096
          use spikeConfig 32 n'
          refine ⟨spikeConfig_odd_false 32 (by norm_num) n', ?_⟩
          rw [rule30n_spikeConfig_eq 32 n',
              rule30n_flipCell_spikeConfig_eq' 32 n' m (by omega) (by omega)]
          simp only [hm4]
          exact ?_level0b_transfer_goal
        · -- Level 0 proper: n'≡5 mod 8 (all remaining), use w=6, P=8
          -- Check: does twoSpike(6,4) have period 8? If not, need different approach.
          use spikeConfig 6 n'
          refine ⟨spikeConfig_odd_false 6 (by norm_num) n', ?_⟩
          rw [rule30n_spikeConfig_eq 6 n',
              rule30n_flipCell_spikeConfig_eq' 6 n' m (by omega) (by omega)]
          simp only [hm4]
          -- GOAL EXPOSED: caEvolve (n'+1) (spikeAtList 6 N) ≠ caEvolve (n'+1) (twoSpikeList 6 4 N)
          -- for n'≡5 mod 8, n'≢42 mod 64, n'≢5 mod 1024 ...
          -- Apply sensitivity_transfer if period cert exists, else expose the gap:
          have h_F_cert : caEvolve 8 (spikeAtList 6 (2*8+2*6+1)) = spikeAtList 6 (2*6+1) :=
            ?_spike6_period8_cert  -- check if this is caEvolve_cert_m6_p16 or similar
          have h_H_cert : caEvolve 8 (twoSpikeList 6 4 (2*8+2*(max 6 4)+1)) =
                          twoSpikeList 6 4 (2*(max 6 4)+1) :=
            ?_ts64_period8_cert  -- THIS IS THE KEY MISSING CERT
          obtain ⟨k, hn'_eq⟩ := periodReduce_diff 3085 8 n' (by omega) hn'
          exact ?_level0_transfer_goal

end P2p
