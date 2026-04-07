/-
SpinePass.lean — Delta-constant proof of subcaseB_mgt38_witness
================================================================

KEY INSIGHT (Knurl):
  The spike at position 2 marches on a fixed period-2 schedule.
  At SubcaseB events, the delta
    Δ(T, m) = center(twoSpike 2 m, T) XOR center(spikeAt 2, T)
  is ALWAYS 1.

  We don't track F_2 and G_{2,m} separately.
  We prove Δ = 1 directly from dChain T m = false (the SubcaseB condition).
  Same m-row. One pass.

PROOF STRUCTURE:
  1. dChain: the spine D_k[T], defined by the recurrence at the left.
  2. dChain_2_parity: dChain T 2 = T % 2 == 1 (the ###/..# clock) [PROVED]
  3. twoSpike_center_complement: with all SubcaseB conditions, Δ(T,m) = 1 [SORRY — needs LFSR]
  4. rule30n_spike_dChain: rule30n T (spikeAt k) = dChain T k [PROVED — via spikeAtList_center_recurrence]
  5. subcaseB_mgt38_witness_proved: the axiom becomes a theorem (modulo #3 only).
-/

import P2p.Prize3_Complete
import P2p.SubcaseB_Firewall
import P2p.CausalConeLemmas
import Mathlib.Data.List.GetD

set_option maxHeartbeats 800000

/-
================================================================================
SECTION 1: THE SPINE
================================================================================
-/

/-- D-chain: D_k[T] = center value after T steps from spikeAt k.
    D_0[T] = true always (rightmost boundary spike → center always 1).
    D_k[0] = false for k ≥ 1 (width-1 tape, spike outside).
    D_k[T+1] = rule30Local(D_k[T], D_{k-1}[T], D_{k-2}[T]) -/
def dChain : Nat → Nat → Bool
  | _, 0     => true
  | 0, _     => false
  | t + 1, 1 => rule30Local (dChain t 1) true false
  | t + 1, k + 2 => rule30Local (dChain t (k + 2)) (dChain t (k + 1)) (dChain t k)

@[simp] lemma dChain_k0 (t : Nat) : dChain t 0 = true := by
  cases t <;> simp [dChain]

@[simp] lemma dChain_t0 (k : Nat) (hk : 0 < k) : dChain 0 k = false := by
  cases k with | zero => omega | succ k => simp [dChain]

@[simp] lemma dChain_step_1 (t : Nat) :
    dChain (t + 1) 1 = rule30Local (dChain t 1) true false := by simp [dChain]

@[simp] lemma dChain_step_k (t k : Nat) :
    dChain (t + 1) (k + 2) =
    rule30Local (dChain t (k + 2)) (dChain t (k + 1)) (dChain t k) := by simp [dChain]

/-
================================================================================
SECTION 2: THE CLOCK — spikeAt 2 has period 2
================================================================================
-/

/-- D_2[T] alternates: false for even T, true for odd T. -/
lemma dChain_2_parity (T : Nat) : dChain T 2 = (T % 2 == 1) := by
  induction T with
  | zero => simp [dChain]
  | succ T ih =>
    simp only [dChain_step_k]
    -- dChain (T+1) 2 = rule30Local (dChain T 2) (dChain T 1) (dChain T 0)
    --               = rule30Local (dChain T 2) (dChain T 1) true
    -- dChain T 1 alternates too; let's evaluate
    -- rule30Local a b c = a XOR (b OR c)
    -- rule30Local (dChain T 2) (dChain T 1) true
    -- = (dChain T 2) XOR ((dChain T 1) OR true)
    -- = (dChain T 2) XOR true = NOT (dChain T 2)
    simp only [rule30Local]
    -- (dChain T 2) XOR ((dChain T 1) OR true) = NOT (dChain T 2)
    -- because (dChain T 1) OR true = true
    simp only [dChain_k0, Bool.or_true, Bool.xor_true]
    -- now: !(T % 2 == 1) = ((T+1) % 2 == 1); case-split on T % 2
    rw [ih]
    cases h : T % 2 with
    | zero => simp [h, show (T + 1) % 2 = 1 from by omega]
    | succ n =>
      have hn : n = 0 := by omega
      subst hn
      simp [h, show (T + 1) % 2 = 0 from by omega]

/-- D_1[T] alternates: false for even T, true for odd T. Same as D_2. -/
lemma dChain_1_parity (T : Nat) : dChain T 1 = (T % 2 == 1) := by
  induction T with
  | zero => simp [dChain]
  | succ T ih =>
    simp only [dChain_step_1, rule30Local]
    -- rule30Local (dChain T 1) true false = (dChain T 1) XOR (true OR false) = !(dChain T 1)
    simp only [Bool.or_false, Bool.xor_true]
    rw [ih]
    cases h : T % 2 with
    | zero => simp [h, show (T + 1) % 2 = 1 from by omega]
    | succ n =>
      have hn : n = 0 := by omega
      subst hn
      simp [h, show (T + 1) % 2 = 0 from by omega]

/-- D_3[T] = floor(T/2) % 2: doubles the period of D_2. -/
lemma dChain_3_parity (T : Nat) : dChain T 3 = (T / 2 % 2 == 1) := by
  induction T with
  | zero => simp [dChain]
  | succ T ih =>
    simp only [dChain_step_k, rule30Local]
    -- dChain (T+1) 3 = rule30Local (dChain T 3) (dChain T 2) (dChain T 1)
    --               = (dChain T 3) XOR ((dChain T 2) OR (dChain T 1))
    -- D_1[T] = D_2[T] = (T%2==1), so OR = (T%2==1)
    rw [dChain_2_parity, dChain_1_parity]
    -- goal: (dChain T 3) XOR ((T%2==1) OR (T%2==1)) = ((T+1)/2%2==1)
    simp only [Bool.or_self]
    rw [ih]
    -- goal: (T/2%2==1) XOR (T%2==1) = ((T+1)/2%2==1)
    -- case split on T % 2
    cases h2 : T % 2 with
    | zero =>
      -- T even: T%2=0, so (T%2==1)=false; XOR with false = id
      -- T/2 vs (T+1)/2: for even T, (T+1)/2 = T/2
      have hT1 : (T + 1) / 2 = T / 2 := by omega
      simp [hT1]
    | succ n =>
      have hn : n = 0 := by omega
      subst hn
      -- T odd: T%2=1, so (T%2==1)=true; XOR with true = Bool.not
      -- T/2 vs (T+1)/2: for odd T, (T+1)/2 = T/2 + 1
      have hT1 : (T + 1) / 2 = T / 2 + 1 := by omega
      simp [hT1]
      -- goal: !(T/2%2==1) = (T/2+1)%2==1
      cases h4 : T / 2 % 2 with
      | zero => simp [show (T / 2 + 1) % 2 = 1 from by omega]
      | succ n =>
        have hn2 : n = 0 := by omega
        subst hn2
        simp [show (T / 2 + 1) % 2 = 0 from by omega]

/-
================================================================================
SECTION 2b: CAUSAL HORIZON LEMMAS
================================================================================
-/

/-- Spike at position k ≥ 2*T+1 is outside the causal horizon: center = false. -/
lemma dChain_beyond_false : ∀ T k : Nat, 2 * T + 1 ≤ k → dChain T k = false := by
  intro T
  induction T with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => simp [dChain]
  | succ T ih =>
    intro k hk
    -- k ≥ 2*(T+1)+1 = 2*T+3, so k ≥ 3
    match k with
    | 0 => omega
    | 1 => omega
    | k' + 2 =>
      -- k'+2 ≥ 2*T+3 → k' ≥ 2*T+1
      simp only [dChain_step_k, rule30Local]
      have h1 : dChain T (k' + 2) = false := ih (k' + 2) (by omega)
      have h2 : dChain T (k' + 1) = false := ih (k' + 1) (by omega)
      have h3 : dChain T k' = false := ih k' (by omega)
      simp [h1, h2, h3]

/-- Spike at position 2*T (the rightmost in the causal cone) gives center = true.
    F_last = 1 universally. -/
lemma dChain_last_true (T : Nat) : dChain T (2 * T) = true := by
  induction T with
  | zero => simp [dChain]
  | succ T ih =>
    -- dChain (T+1) (2*(T+1)) = dChain (T+1) (2*T+2)
    -- = rule30Local (dChain T (2*T+2)) (dChain T (2*T+1)) (dChain T (2*T))
    show dChain (T + 1) (2 * T + 1 + 1) = true
    simp only [dChain_step_k, rule30Local]
    have hf1 : dChain T (2 * T + 1 + 1) = false :=
      dChain_beyond_false T (2 * T + 1 + 1) (by omega)
    have hf2 : dChain T (2 * T + 1) = false :=
      dChain_beyond_false T (2 * T + 1) (by omega)
    -- rule30Local false false true = false XOR (false OR true) = true
    simp [hf1, hf2, ih]

/-- D_3[T] OR D_2[T] = (T % 4 ≠ 0): the "not divisible by 4" clock. -/
private lemma dChain_3_or_2 (T : Nat) : (dChain T 3 || dChain T 2) = decide (T % 4 ≠ 0) := by
  rw [dChain_3_parity, dChain_2_parity]
  -- goal: (T/2%2==1) || (T%2==1) = decide (T%4 ≠ 0)
  -- Case split on T % 4
  have hd : T / 2 % 2 = (T % 4) / 2 := by omega
  have hm : T % 2 = (T % 4) % 2 := by omega
  rw [hd, hm]
  have h0123 : T % 4 = 0 ∨ T % 4 = 1 ∨ T % 4 = 2 ∨ T % 4 = 3 := by
    have := Nat.mod_lt T (show 0 < 4 by omega); omega
  rcases h0123 with h | h | h | h <;> simp [h]

/-- The 4-step telescoped XOR is always true:
    (T%4≠0) XOR ((T+1)%4≠0) XOR ((T+2)%4≠0) XOR ((T+3)%4≠0) = true -/
private lemma four_antiperiod_xor (T : Nat) :
    (decide (T % 4 ≠ 0) ^^ decide ((T + 1) % 4 ≠ 0) ^^
     decide ((T + 2) % 4 ≠ 0) ^^ decide ((T + 3) % 4 ≠ 0)) = true := by
  -- In any 4 consecutive naturals, exactly one is divisible by 4.
  -- Strategy: case-split on T % 4 ∈ {0,1,2,3} using omega + decide.
  have h1 : (T + 1) % 4 = (T % 4 + 1) % 4 := by omega
  have h2 : (T + 2) % 4 = (T % 4 + 2) % 4 := by omega
  have h3 : (T + 3) % 4 = (T % 4 + 3) % 4 := by omega
  rw [h1, h2, h3]
  have hlt : T % 4 < 4 := Nat.mod_lt T (by omega)
  -- Case split: T % 4 = 0, 1, 2, or 3
  have h0123 : T % 4 = 0 ∨ T % 4 = 1 ∨ T % 4 = 2 ∨ T % 4 = 3 := by omega
  rcases h0123 with h | h | h | h <;> simp only [h] <;> decide

/-- D_4[T] has anti-period 4: D_4[T+4] = !D_4[T]. Equivalently, D_4 has period 8. -/
lemma dChain_4_antiperiod (T : Nat) : dChain (T + 4) 4 = !dChain T 4 := by
  -- Step function: dChain (S+1) 4 = dChain S 4 XOR (dChain S 3 || dChain S 2)
  -- step : one-step recurrence for D_4
  -- Note: precedence issue — = binds tighter than ^^, so we must parenthesize the RHS.
  have step : ∀ S : Nat, dChain (S + 1) 4 = (dChain S 4 ^^ (dChain S 3 || dChain S 2)) := by
    intro S
    -- dChain (S+1) (2+2) = rule30Local (dChain S (2+2)) (dChain S (2+1)) (dChain S 2)
    -- rule30Local a b c = xor a (b || c) = a ^^ (b || c) definitionally.
    rfl
  -- rewrite using the clock lemma
  have step' : ∀ S : Nat, dChain (S + 1) 4 = (dChain S 4 ^^ decide (S % 4 ≠ 0)) := by
    intro S
    rw [step S, dChain_3_or_2]
  -- telescope 4 steps using calc
  calc dChain (T + 4) 4
      = (dChain (T + 3) 4 ^^ decide ((T + 3) % 4 ≠ 0)) := by
          rw [show T + 4 = T + 3 + 1 from by omega, step' (T + 3)]
    _ = ((dChain (T + 2) 4 ^^ decide ((T + 2) % 4 ≠ 0)) ^^ decide ((T + 3) % 4 ≠ 0)) := by
          rw [show T + 3 = T + 2 + 1 from by omega, step' (T + 2)]
    _ = (((dChain (T + 1) 4 ^^ decide ((T + 1) % 4 ≠ 0)) ^^ decide ((T + 2) % 4 ≠ 0)) ^^ decide ((T + 3) % 4 ≠ 0)) := by
          rw [show T + 2 = T + 1 + 1 from by omega, step' (T + 1)]
    _ = ((((dChain T 4 ^^ decide (T % 4 ≠ 0)) ^^ decide ((T + 1) % 4 ≠ 0)) ^^ decide ((T + 2) % 4 ≠ 0)) ^^ decide ((T + 3) % 4 ≠ 0)) := by
          rw [show T + 1 = T + 1 from rfl, step' T]
    _ = !dChain T 4 := by
          have hxor := four_antiperiod_xor T
          revert hxor
          generalize dChain T 4 = b
          generalize decide (T % 4 ≠ 0) = x
          generalize decide ((T + 1) % 4 ≠ 0) = y
          generalize decide ((T + 2) % 4 ≠ 0) = z
          generalize decide ((T + 3) % 4 ≠ 0) = w
          intro h
          cases b <;> cases x <;> cases y <;> cases z <;> cases w <;> simp_all

/-
================================================================================
SECTION 2c: D_5 PERIOD LEMMA
================================================================================

NOTE: The conjectured pattern "D_k has anti-period 2^(k-2)" is WRONG for k=5.
  D_2: anti-period 1  (period 2)
  D_3: anti-period 2  (period 4)
  D_4: anti-period 4  (period 8)
  D_5: period 8       (NO anti-period — XOR of D4|D3 clock over 8 steps = false)
  D_6: anti-period 8  (period 16)
  D_7: anti-period 16 (period 32)
The pattern is irregular; D_5 lands in the same phase after 8 steps.
-/

/-- D_4[T] OR D_3[T] = false only at T%8 ∈ {0,1}, true otherwise. -/
private lemma dChain_4_or_3 (T : Nat) :
    (dChain T 4 || dChain T 3) = decide (T % 8 ≠ 0 ∧ T % 8 ≠ 1) := by
  -- Express D_4 and D_3 in terms of T%8 using anti-period-4 and period-4.
  -- Strategy: reduce to T%8 via case split.
  -- D_3 has period 4; D_4 has period 8.
  -- We know D_4 values mod 8 from dChain_4_antiperiod + dChain_3_parity.
  -- Use native_decide for the 8 base cases, then induction by 8-step periodicity.
  -- Step 1: one-step recurrence for D_4
  have step4 : ∀ S : Nat, dChain (S + 1) 4 = (dChain S 4 ^^ (dChain S 3 || dChain S 2)) := by
    intro S; rfl
  -- Step 2: periodicity — after 8 steps, D_4 and D_3 return (since D_4 period=8, D_3 period=4)
  have period_d4 : ∀ S : Nat, dChain (S + 8) 4 = dChain S 4 := by
    intro S
    rw [show S + 8 = S + 4 + 4 from by omega]
    rw [dChain_4_antiperiod (S + 4), dChain_4_antiperiod S]
    simp
  have period_d3 : ∀ S : Nat, dChain (S + 8) 3 = dChain S 3 := by
    intro S
    -- D_3 has period 4: (S+4)/2 % 2 = S/2 % 2
    -- We prove period 4 first, then double it.
    have h_period4 : ∀ U : Nat, dChain (U + 4) 3 = dChain U 3 := by
      intro U
      rw [dChain_3_parity (U + 4), dChain_3_parity U]
      -- (U+4)/2 % 2 = U/2 % 2 because (U+4)/2 = U/2 + 2
      congr 1
      have : (U + 4) / 2 = U / 2 + 2 := by omega
      rw [this]
      omega
    rw [show S + 8 = S + 4 + 4 from by omega, h_period4 (S + 4), h_period4 S]
  -- Step 3: reduce to T % 8 case
  suffices h : ∀ r : Nat, r < 8 →
      (dChain r 4 || dChain r 3) = decide (r % 8 ≠ 0 ∧ r % 8 ≠ 1) by
    have hr : T % 8 < 8 := Nat.mod_lt T (by omega)
    have key := h (T % 8) hr
    -- now need (dChain T 4 || dChain T 3) = (dChain (T%8) 4 || dChain (T%8) 3)
    -- because both have period 8
    have hT_eq : T = T % 8 + 8 * (T / 8) := by omega
    conv_lhs => rw [hT_eq]
    -- apply periodicity T/8 times
    have hper : ∀ (k n : Nat),
        dChain (n + 8 * k) 4 = dChain n 4 ∧ dChain (n + 8 * k) 3 = dChain n 3 := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [show n + 8 * (k + 1) = n + 8 * k + 8 from by omega]
        exact ⟨by rw [period_d4 (n + 8*k), (ih n).1],
               by rw [period_d3 (n + 8*k), (ih n).2]⟩
    have hp := hper (T / 8) (T % 8)
    rw [hp.1, hp.2]
    rw [key]
    simp [Nat.mod_mod_of_dvd]
  -- Base case: verify for r ∈ {0,1,...,7} by case split + decide
  intro r hr
  have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- The 8-step telescoped XOR is false: D5 has period 8 (not anti-period). -/
private lemma eight_period_xor_D5 (T : Nat) :
    (decide (T % 8 ≠ 0 ∧ T % 8 ≠ 1) ^^
     decide ((T+1) % 8 ≠ 0 ∧ (T+1) % 8 ≠ 1) ^^
     decide ((T+2) % 8 ≠ 0 ∧ (T+2) % 8 ≠ 1) ^^
     decide ((T+3) % 8 ≠ 0 ∧ (T+3) % 8 ≠ 1) ^^
     decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1) ^^
     decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1) ^^
     decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1) ^^
     decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) = false := by
  -- In any 8 consecutive naturals, exactly 2 are ≡ 0 or 1 mod 8.
  -- So 6 are true and 2 are false → XOR = false (even number of trues).
  have h1 : (T + 1) % 8 = (T % 8 + 1) % 8 := by omega
  have h2 : (T + 2) % 8 = (T % 8 + 2) % 8 := by omega
  have h3 : (T + 3) % 8 = (T % 8 + 3) % 8 := by omega
  have h4 : (T + 4) % 8 = (T % 8 + 4) % 8 := by omega
  have h5 : (T + 5) % 8 = (T % 8 + 5) % 8 := by omega
  have h6 : (T + 6) % 8 = (T % 8 + 6) % 8 := by omega
  have h7 : (T + 7) % 8 = (T % 8 + 7) % 8 := by omega
  rw [h1, h2, h3, h4, h5, h6, h7]
  have hlt : T % 8 < 8 := Nat.mod_lt T (by omega)
  have h0to7 : T % 8 = 0 ∨ T % 8 = 1 ∨ T % 8 = 2 ∨ T % 8 = 3 ∨
               T % 8 = 4 ∨ T % 8 = 5 ∨ T % 8 = 6 ∨ T % 8 = 7 := by omega
  rcases h0to7 with h | h | h | h | h | h | h | h <;> simp only [h] <;> decide

/-- D_5[T] has period 8: dChain (T+8) 5 = dChain T 5. -/
lemma dChain_5_period (T : Nat) : dChain (T + 8) 5 = dChain T 5 := by
  -- Step function: dChain (S+1) 5 = dChain S 5 XOR (dChain S 4 || dChain S 3)
  have step : ∀ S : Nat, dChain (S + 1) 5 = (dChain S 5 ^^ (dChain S 4 || dChain S 3)) := by
    intro S; rfl
  -- Rewrite using the clock lemma
  have step' : ∀ S : Nat, dChain (S + 1) 5 =
      (dChain S 5 ^^ decide (S % 8 ≠ 0 ∧ S % 8 ≠ 1)) := by
    intro S; rw [step S, dChain_4_or_3]
  -- Telescope 8 steps
  calc dChain (T + 8) 5
      = (dChain (T + 7) 5 ^^ decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 8 = T + 7 + 1 from by omega, step' (T + 7)]
    _ = ((dChain (T + 6) 5 ^^ decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 7 = T + 6 + 1 from by omega, step' (T + 6)]
    _ = (((dChain (T + 5) 5 ^^ decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1)) ^^
          decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 6 = T + 5 + 1 from by omega, step' (T + 5)]
    _ = ((((dChain (T + 4) 5 ^^ decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1)) ^^
          decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1)) ^^
          decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 5 = T + 4 + 1 from by omega, step' (T + 4)]
    _ = (((((dChain (T + 3) 5 ^^ decide ((T+3) % 8 ≠ 0 ∧ (T+3) % 8 ≠ 1)) ^^
          decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1)) ^^
          decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1)) ^^
          decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 4 = T + 3 + 1 from by omega, step' (T + 3)]
    _ = ((((((dChain (T + 2) 5 ^^ decide ((T+2) % 8 ≠ 0 ∧ (T+2) % 8 ≠ 1)) ^^
          decide ((T+3) % 8 ≠ 0 ∧ (T+3) % 8 ≠ 1)) ^^
          decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1)) ^^
          decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1)) ^^
          decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 3 = T + 2 + 1 from by omega, step' (T + 2)]
    _ = (((((((dChain (T + 1) 5 ^^ decide ((T+1) % 8 ≠ 0 ∧ (T+1) % 8 ≠ 1)) ^^
          decide ((T+2) % 8 ≠ 0 ∧ (T+2) % 8 ≠ 1)) ^^
          decide ((T+3) % 8 ≠ 0 ∧ (T+3) % 8 ≠ 1)) ^^
          decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1)) ^^
          decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1)) ^^
          decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 2 = T + 1 + 1 from by omega, step' (T + 1)]
    _ = ((((((((dChain T 5 ^^ decide (T % 8 ≠ 0 ∧ T % 8 ≠ 1)) ^^
          decide ((T+1) % 8 ≠ 0 ∧ (T+1) % 8 ≠ 1)) ^^
          decide ((T+2) % 8 ≠ 0 ∧ (T+2) % 8 ≠ 1)) ^^
          decide ((T+3) % 8 ≠ 0 ∧ (T+3) % 8 ≠ 1)) ^^
          decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1)) ^^
          decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1)) ^^
          decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1)) ^^
          decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1)) := by
          rw [show T + 1 = T + 1 from rfl, step' T]
    _ = dChain T 5 := by
          have hxor := eight_period_xor_D5 T
          revert hxor
          generalize dChain T 5 = b
          generalize decide (T % 8 ≠ 0 ∧ T % 8 ≠ 1) = x0
          generalize decide ((T+1) % 8 ≠ 0 ∧ (T+1) % 8 ≠ 1) = x1
          generalize decide ((T+2) % 8 ≠ 0 ∧ (T+2) % 8 ≠ 1) = x2
          generalize decide ((T+3) % 8 ≠ 0 ∧ (T+3) % 8 ≠ 1) = x3
          generalize decide ((T+4) % 8 ≠ 0 ∧ (T+4) % 8 ≠ 1) = x4
          generalize decide ((T+5) % 8 ≠ 0 ∧ (T+5) % 8 ≠ 1) = x5
          generalize decide ((T+6) % 8 ≠ 0 ∧ (T+6) % 8 ≠ 1) = x6
          generalize decide ((T+7) % 8 ≠ 0 ∧ (T+7) % 8 ≠ 1) = x7
          intro h
          cases b <;> cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;>
            cases x4 <;> cases x5 <;> cases x6 <;> cases x7 <;> simp_all

/-
================================================================================
SECTION 3: THE DELTA — Δ(T, m) = G_{2,m}(T) XOR F_2(T) = 1 at SubcaseB events
================================================================================

KEY FACTS (verified computationally 2026-04-06):
1. All SubcaseB events for m≥40 in T=20..200 are RIGHT-MIRROR (m=2*T-8).
   Non-right-mirror SubcaseB fires first at T=40984 (m=40, n'=40983).
2. At right-mirror events, delta alternates: 0 (even T), 1 (odd T).
   ⇒ RIGHT-MIRROR EXCLUDED from this lemma (hm_not_rm).
3. At non-right-mirror SubcaseB events (T≥3088, m≥40, all exclusions):
   delta = G_{2,m}(T) XOR F_2(T) = 1.
   Verified: m=40@T=40984 (F_2=0, G_{2,m}=1), m=42@T=118805 (F_2=1, G_{2,m}=0),
             m=46@T=106523 (F_2=1, G_{2,m}=0).

PROOF OBLIGATION: The sorry below requires LFSR algebraic theory.
Proof path: The period of F_m for m≥40 is 2^{m/2}. SubcaseB fires when dChain T m = 0
and G_{m,last}(T) = 1 simultaneously. At those T values, the D-chain cascade from
position 2 to m ensures G_{2,m}(T) = !F_2(T). Formalization requires:
  (a) LFSR period characterization of F_m for active even m≥40
  (b) Phase-lock lemma: G_{m,last}=1 when F_m=0 implies D-chain activation
  (c) Flip-propagation: activated D-chain at m flips the parity contribution to center
-/

/-- The REAL content: at non-right-mirror SubcaseB events for m≥40 with n'≥3087,
    G_{2,m}(T) = !F_2(T), making twoSpike(2,m) a sensitivity witness.

    NOTE: hm_ge40 is ESSENTIAL. For m=4 at T≥3088, SubcaseB fires (T≡6 mod 8)
    and delta=0 — the lemma is FALSE without m≥40. Computationally verified:
    - m=4: delta=0 at ALL SubcaseB events (right-mirror excluded or not)
    - m=6,12,14: delta alternates 0/1 at SubcaseB events
    - m≥40: delta=1 at ALL SubcaseB events verified (T=40984, 106522, 118804)

    HYPOTHESES NEEDED (matching subcaseB_mgt38_witness exactly):
    - T ≥ 3088 (n' = T-1 ≥ 3087)
    - m ≥ 40, m even (hm_ge40, hm_even)
    - m ≠ 2*(T-1) = 2*n' (hm_ne_r: not right-boundary)
    - m ≠ 2*T - 8 = 2*(n'+1) - 8 (hm_not_rm: not right-mirror)
    - dChain T m = false (SubcaseB condition: F_m(T) = 0)
    - G_{m,last}(T) = true (SubcaseB condition: twoSpike with last = 1)

    Computational evidence: verified for all 3 known large SubcaseB events (m=40,42,46).
    Proof status: OPEN — requires LFSR/D-chain algebraic theory.

    Algebraic argument sketch:
    For m≥40, SubcaseB fires at T with T%2 = (m/2)%2 (parity lock from D-chain cascade).
    The D-chain cascade from position 2 to m is fully activated at SubcaseB events,
    which forces G_{2,m}(T) = !D_2[T] = !(T%2==1). -/
lemma twoSpike_center_complement (T m : Nat)
    (hT : 3088 ≤ T)
    (hm_ge40 : 40 ≤ m) (hm_even : m % 2 = 0)
    (hm_not_rm : m ≠ 2 * T - 8)
    (hm_ne_r : m ≠ 2 * (T - 1))
    (hSB : dChain T m = false)
    (hts : rule30n T (fun j : Fin (2 * T + 1) =>
             decide (j.val = m ∨ j.val = 2 * T)) = true) :
    rule30n T (fun j : Fin (2 * T + 1) => decide (j.val = 2 ∨ j.val = m)) =
    !dChain T 2 := by
  sorry  -- OPEN: LFSR/D-chain algebraic proof needed. See D-chain period theory below.

/-
================================================================================
SECTION 3b: TWO-SPIKE UNIVERSAL LEMMA — G_{2,last}(T) = false for T≥2
================================================================================

Computationally verified T=2..200. Proof via two-step recursion:
  caEvolve 2 (twoSpikeList 2 (2*T) (2*T+1)) = twoSpikeList 2 (2*(T-2)) (2*(T-2)+1) for T≥4
which follows from the explicit evolution:
  step1(twoSpike at {2, 2T}) = tape with 1s at {0,1,2,2*(T-1)}, T≥3
  step1 of the above = twoSpike at {2, 2*(T-2)}, T≥4
Base cases T=2,3 terminate to false.

NOTE: Uses twoSpikeList from CausalConeLemmas: twoSpikeList p q N (1s at p and q, width N).
-/

/-- configToList of the two-spike config equals twoSpikeList 2 (2*T) (2*T+1). -/
private lemma configToList_twoSpike2last (T : Nat) :
    configToList (fun j : Fin (2 * T + 1) => decide (j.val = 2 ∨ j.val = 2 * T)) =
    twoSpikeList 2 (2 * T) (2 * T + 1) := by
  simp [configToList, twoSpikeList]

-- Helper: drop i of twoSpikeList gives decide (i+j = p ∨ i+j = q) for in-bounds j
private lemma twoSpikeList_drop_getD' (p q N i j : Nat) (h : i + j < N) :
    (List.drop i (twoSpikeList p q N)).getD j false = decide (i + j = p ∨ i + j = q) := by
  rw [show ((List.drop i (twoSpikeList p q N)).getD j false) =
        (twoSpikeList p q N).getD (i + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [twoSpikeList_getD p q N (i + j) h]

-- Window agreement lemmas: show each position j ≤ 4 of (drop i input) agrees with canonical list
-- i=0: canonical [F,F,T,F,F]
private lemma agree_window_i0 (T : Nat) (hT : 4 ≤ T) (j : Nat) (hj : j ≤ 4) :
    (List.drop 0 (twoSpikeList 2 (2 * T) (2 * T + 1))).getD j false =
    [false, false, true, false, false].getD j false := by
  simp only [List.drop_zero]
  rw [twoSpikeList_getD _ _ _ _ (by omega)]
  match j with
  | 0 => simp only [show (0:Nat) ≠ 2 from by omega, show (0:Nat) ≠ 2*T from by omega, or_self, decide_false, List.getD_cons_zero]
  | 1 => simp only [show (1:Nat) ≠ 2 from by omega, show (1:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 2 => simp [show (2:Nat) = 2 from rfl]
  | 3 => simp only [show (3:Nat) ≠ 2 from by omega, show (3:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 4 => simp only [show (4:Nat) ≠ 2 from by omega, show (4:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | j+5 => omega

-- i=1: canonical [F,T,F,F,F]
private lemma agree_window_i1 (T : Nat) (hT : 4 ≤ T) (j : Nat) (hj : j ≤ 4) :
    (List.drop 1 (twoSpikeList 2 (2 * T) (2 * T + 1))).getD j false =
    [false, true, false, false, false].getD j false := by
  rw [twoSpikeList_drop_getD' _ _ _ _ _ (by omega)]
  match j with
  | 0 => simp only [show 1+(0:Nat) ≠ 2 from by omega, show 1+(0:Nat) ≠ 2*T from by omega, or_self, decide_false, List.getD_cons_zero]
  | 1 => simp [show 1+(1:Nat) = 2 from rfl]
  | 2 => simp only [show 1+(2:Nat) ≠ 2 from by omega, show 1+(2:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 3 => simp only [show 1+(3:Nat) ≠ 2 from by omega, show 1+(3:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 4 => simp only [show 1+(4:Nat) ≠ 2 from by omega, show 1+(4:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | j+5 => omega

-- i=2: canonical [T,F,F,F,F]
private lemma agree_window_i2 (T : Nat) (hT : 4 ≤ T) (j : Nat) (hj : j ≤ 4) :
    (List.drop 2 (twoSpikeList 2 (2 * T) (2 * T + 1))).getD j false =
    [true, false, false, false, false].getD j false := by
  rw [twoSpikeList_drop_getD' _ _ _ _ _ (by omega)]
  match j with
  | 0 => simp [show 2+(0:Nat) = 2 from rfl]
  | 1 => simp only [show 2+(1:Nat) ≠ 2 from by omega, show 2+(1:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 2 => simp only [show 2+(2:Nat) ≠ 2 from by omega, show 2+(2:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 3 => simp only [show 2+(3:Nat) ≠ 2 from by omega, show 2+(3:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 4 => simp only [show 2+(4:Nat) ≠ 2 from by omega, show 2+(4:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | j+5 => omega

-- middle (3≤i<2*(T-2)): canonical [F,F,F,F,F]
private lemma agree_window_mid (T : Nat) (hT : 4 ≤ T) (i : Nat)
    (hi_lo : 3 ≤ i) (hi_hi : i < 2 * (T - 2))
    (j : Nat) (hj : j ≤ 4) :
    (List.drop i (twoSpikeList 2 (2 * T) (2 * T + 1))).getD j false =
    [false, false, false, false, false].getD j false := by
  rw [twoSpikeList_drop_getD' _ _ _ _ _ (by omega)]
  simp only [show i+j ≠ 2 from by omega, show i+j ≠ 2*T from by omega, or_self, decide_false]
  match j, hj with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | j+5, hj => omega

-- i=2*(T-2): canonical [F,F,F,F,T]
private lemma agree_window_last (T : Nat) (hT : 4 ≤ T) (j : Nat) (hj : j ≤ 4) :
    (List.drop (2 * (T - 2)) (twoSpikeList 2 (2 * T) (2 * T + 1))).getD j false =
    [false, false, false, false, true].getD j false := by
  rw [twoSpikeList_drop_getD' _ _ _ _ _ (by omega)]
  match j with
  | 0 => simp only [show 2*(T-2)+(0:Nat) ≠ 2 from by omega, show 2*(T-2)+(0:Nat) ≠ 2*T from by omega, or_self, decide_false, List.getD_cons_zero]
  | 1 => simp only [show 2*(T-2)+(1:Nat) ≠ 2 from by omega, show 2*(T-2)+(1:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 2 => simp only [show 2*(T-2)+(2:Nat) ≠ 2 from by omega, show 2*(T-2)+(2:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 3 => simp only [show 2*(T-2)+(3:Nat) ≠ 2 from by omega, show 2*(T-2)+(3:Nat) ≠ 2*T from by omega, or_self, decide_false]; rfl
  | 4 => simp [show 2*(T-2)+(4:Nat) = 2*T from by omega]
  | j+5 => omega

-- Canonical 5-cell computation results
private lemma step2_canon_FFTff : (caEvolve 2 [false, false, true, false, false]).getD 0 false = false := by native_decide
private lemma step2_canon_FTfff : (caEvolve 2 [false, true, false, false, false]).getD 0 false = false := by native_decide
private lemma step2_canon_Tffff : (caEvolve 2 [true, false, false, false, false]).getD 0 false = true := by native_decide
private lemma step2_canon_fffFT : (caEvolve 2 [false, false, false, false, true]).getD 0 false = true := by native_decide
private lemma step2_canon_fffff : (caEvolve 2 [false, false, false, false, false]).getD 0 false = false := by native_decide

/-- After 2 evolution steps, twoSpikeList 2 (2*T) (2*T+1) reduces to
    twoSpikeList 2 (2*(T-2)) (2*(T-2)+1), for T≥4.
    This is the key 2-step recursion. Computationally verified T=4..19.

    Proof: pointwise getD equality. For each output position i ∈ [0, 2*(T-2)], use
    caEvolve_getD_shift to reduce to position-0 of a dropped input, then caEvolve_agree
    to reduce to a 5-cell canonical computation. Five cases by the spike positions:
      i=0: window [F,F,T,F,F] → false;  i=1: [F,T,F,F,F] → false;  i=2: [T,F,F,F,F] → true
      3≤i<2*(T-2): [F,F,F,F,F] → false;  i=2*(T-2): [F,F,F,F,T] → true -/
private lemma twoSpikeList_2_last_step2 (T : Nat) (hT : 4 ≤ T) :
    caEvolve 2 (twoSpikeList 2 (2 * T) (2 * T + 1)) =
    twoSpikeList 2 (2 * (T - 2)) (2 * (T - 2) + 1) := by
  have hlen_out : (caEvolve 2 (twoSpikeList 2 (2 * T) (2 * T + 1))).length = 2 * (T - 2) + 1 := by
    rw [caEvolve_length_le 2 _ (by rw [twoSpikeList_length]; omega), twoSpikeList_length]; omega
  have hlen_rhs : (twoSpikeList 2 (2 * (T - 2)) (2 * (T - 2) + 1)).length = 2 * (T - 2) + 1 :=
    twoSpikeList_length 2 (2 * (T - 2)) (2 * (T - 2) + 1)
  apply List.ext_getElem (by omega)
  intro i hi_lhs hi_rhs
  rw [← List.getD_eq_getElem _ false hi_rhs, ← List.getD_eq_getElem _ false hi_lhs]
  rw [caEvolve_getD_shift 2 (twoSpikeList 2 (2 * T) (2 * T + 1)) i]
  have hi_val : i < 2 * (T - 2) + 1 := by rw [hlen_rhs] at hi_rhs; exact hi_rhs
  rw [twoSpikeList_getD 2 (2 * (T - 2)) (2 * (T - 2) + 1) i hi_val]
  by_cases hi0 : i = 0
  · subst hi0
    rw [caEvolve_agree 2 _ [false, false, true, false, false]
        (by simp [twoSpikeList_length]; omega) (by simp) (agree_window_i0 T hT),
        step2_canon_FFTff]
    simp only [show (0:Nat) ≠ 2 from by omega, show (0:Nat) ≠ 2*(T-2) from by omega, or_self, decide_false]
  · by_cases hi1 : i = 1
    · subst hi1
      rw [caEvolve_agree 2 _ [false, true, false, false, false]
          (by rw [List.length_drop, twoSpikeList_length]; omega) (by simp) (agree_window_i1 T hT),
          step2_canon_FTfff]
      simp only [show (1:Nat) ≠ 2 from by omega, show (1:Nat) ≠ 2*(T-2) from by omega, or_self, decide_false]
    · by_cases hi2 : i = 2
      · subst hi2
        rw [caEvolve_agree 2 _ [true, false, false, false, false]
            (by rw [List.length_drop, twoSpikeList_length]; omega) (by simp) (agree_window_i2 T hT),
            step2_canon_Tffff]
        simp [show (2:Nat) = 2 from rfl]
      · by_cases hiL : i = 2 * (T - 2)
        · subst hiL
          rw [caEvolve_agree 2 _ [false, false, false, false, true]
              (by rw [List.length_drop, twoSpikeList_length]; omega) (by simp)
              (agree_window_last T hT),
              step2_canon_fffFT]
          simp [show 2*(T-2) = 2*(T-2) from rfl]
        · have hi_ge3 : 3 ≤ i := by omega
          have hi_lt : i < 2 * (T - 2) := by omega
          rw [caEvolve_agree 2 _ [false, false, false, false, false]
              (by rw [List.length_drop, twoSpikeList_length]; omega) (by simp)
              (agree_window_mid T hT i hi_ge3 hi_lt),
              step2_canon_fffff]
          simp only [show i ≠ 2 from by omega, show i ≠ 2*(T-2) from by omega, or_self, decide_false]

/-- Auxiliary lemma for dChain_2_last_false: induction by 2 using twoSpikeList_2_last_step2. -/
private lemma dChain_2_last_false_aux (n : Nat) :
    (caEvolve (n + 2) (twoSpikeList 2 (2 * (n + 2)) (2 * (n + 2) + 1))).getD 0 false = false := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 =>
      -- T = n+4; use: caEvolve (n+4) = caEvolve (n+2) ∘ caEvolve 2, then step2 reduction
      rw [show n + 2 + 2 = (n + 2) + 2 from by omega, caEvolve_add,
          twoSpikeList_2_last_step2 ((n + 2) + 2) (by omega),
          show (n + 2) + 2 - 2 = n + 2 from by omega]
      exact ih n (by omega)

/-- Two spikes at positions 2 and 2T always give center = false for T ≥ 2.
    Computationally verified T=2..200. Proof: 2-step recursion (no sorry). -/
lemma dChain_2_last_false (T : Nat) (hT : 2 ≤ T) :
    rule30n T (fun j : Fin (2 * T + 1) => decide (j.val = 2 ∨ j.val = 2 * T)) = false := by
  have key := dChain_2_last_false_aux (T - 2)
  rw [show T - 2 + 2 = T from by omega] at key
  unfold rule30n
  rw [configToList_twoSpike2last]
  exact key

/-
================================================================================
SECTION 4: CONNECT rule30n TO THE SPINE
================================================================================
-/

/-- configToList of a spikeAt function equals spikeAtList. -/
private lemma configToList_spikeAt (T k : Nat) :
    configToList (fun j : Fin (2 * T + 1) => decide (j.val = k)) =
    spikeAtList k (2 * T + 1) := by
  simp [configToList, spikeAtList]

/-- Spike-at-0 gives center = true at every time step. -/
private lemma spikeAtList0_always_true (T : Nat) :
    (caEvolve T (spikeAtList 0 (2 * T + 1))).getD 0 false = true := by
  induction T with
  | zero =>
    simp [caEvolve, spikeAtList, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  | succ T ih =>
    have hlen3 : (caEvolve T (spikeAtList 0 (2 * (T + 1) + 1))).length = 3 := by
      rw [caEvolve_length_le T _ (by rw [spikeAtList_length]; omega), spikeAtList_length]; omega
    rw [caEvolve_succ_comm, caStepList_getD_eq _ 0 (by omega)]
    have hp0 : (caEvolve T (spikeAtList 0 (2 * (T + 1) + 1))).getD 0 false = true :=
      (caEvolve_spikeAt_agree T 0 (2 * (T + 1) + 1) (2 * T + 1) 0 (by omega) (by omega)).trans ih
    have hp1 : (caEvolve T (spikeAtList 0 (2 * (T + 1) + 1))).getD 1 false = false := by
      rw [caEvolve_getD_shift T _ 1]
      exact caEvolve_allFalse T _ (spikeAtList_drop_allFalse 0 (2 * (T + 1) + 1) 1 (by omega))
    have hp2 : (caEvolve T (spikeAtList 0 (2 * (T + 1) + 1))).getD 2 false = false := by
      rw [caEvolve_getD_shift T _ 2]
      exact caEvolve_allFalse T _ (spikeAtList_drop_allFalse 0 (2 * (T + 1) + 1) 2 (by omega))
    rw [hp0, hp1, hp2]; simp [rule30Local]

/-- Core spine identity (unbounded): (caEvolve T (spikeAtList k (2*T+1))).getD 0 false = dChain T k.
    Proved by induction on T; the k=0 and k=1 boundary cases are handled separately. -/
private lemma dChain_eq_caEvolve (T k : Nat) :
    (caEvolve T (spikeAtList k (2 * T + 1))).getD 0 false = dChain T k := by
  induction T generalizing k with
  | zero =>
    -- T=0: caEvolve 0 l = l, spikeAtList k 1 = [decide(0=k)]
    simp only [caEvolve]
    rw [spikeAtList_getD k 1 0 (by omega)]
    cases k with
    | zero => simp [dChain]
    | succ k => simp [dChain]
  | succ T ih =>
    cases k with
    | zero =>
      -- k=0: dChain T 0 = true, spikeAtList0_always_true
      simp only [dChain_k0]
      exact spikeAtList0_always_true (T + 1)
    | succ k =>
      cases k with
      | zero =>
        -- k=1: dChain (T+1) 1 = rule30Local (dChain T 1) true false
        --      middle term is dChain T 0 = true; right term = 0 (no spike at -1)
        simp only [show (0 : Nat) + 1 = 1 from rfl]
        rw [dChain_step_1]
        have hlen3 : (caEvolve T (spikeAtList 1 (2 * (T + 1) + 1))).length = 3 := by
          rw [caEvolve_length_le T _ (by rw [spikeAtList_length]; omega), spikeAtList_length]; omega
        rw [caEvolve_succ_comm, caStepList_getD_eq _ 0 (by omega)]
        -- p0 = dChain T 1 (by IH and caEvolve_spikeAt_agree)
        have hp0 : (caEvolve T (spikeAtList 1 (2 * (T + 1) + 1))).getD 0 false = dChain T 1 := by
          rw [caEvolve_spikeAt_agree T 1 (2 * (T + 1) + 1) (2 * T + 1) 0 (by omega) (by omega)]
          exact ih 1
        -- p1 = true: drop-1 of spikeAtList 1 (2T+3) looks like spikeAtList 0 (2T+1)
        have hp1 : (caEvolve T (spikeAtList 1 (2 * (T + 1) + 1))).getD 1 false = true := by
          rw [caEvolve_getD_shift T _ 1]
          have heq : (caEvolve T ((spikeAtList 1 (2 * (T + 1) + 1)).drop 1)).getD 0 false =
              (caEvolve T (spikeAtList 0 (2 * T + 1))).getD 0 false :=
            caEvolve_agree T _ _ (by rw [List.length_drop, spikeAtList_length]; omega)
              (by rw [spikeAtList_length]; omega)
              (fun j hj => by
                rw [show ((spikeAtList 1 (2 * (T + 1) + 1)).drop 1).getD j false =
                    (spikeAtList 1 (2 * (T + 1) + 1)).getD (1 + j) false from by
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]]
                rw [spikeAtList_getD 1 (2 * (T + 1) + 1) (1 + j) (by omega)]
                rw [spikeAtList_getD 0 (2 * T + 1) j (by omega)]
                simp only [decide_eq_decide]; omega)
          rw [heq, ih 0, dChain_k0]
        -- p2 = false: drop-2 of spikeAtList 1 has spike before position 0
        have hp2 : (caEvolve T (spikeAtList 1 (2 * (T + 1) + 1))).getD 2 false = false := by
          rw [caEvolve_getD_shift T _ 2]
          exact caEvolve_allFalse T _ (spikeAtList_drop_allFalse 1 (2 * (T + 1) + 1) 2 (by omega))
        rw [hp0, hp1, hp2]
      | succ k =>
        -- k+2: use spikeAtList_center_recurrence (m=k, s=T)
        -- In this branch the input index is k+1+1; rename to k+2 for clarity
        simp only [show k + 1 + 1 = k + 2 from by omega] at *
        rw [dChain_step_k T k]
        rw [spikeAtList_center_recurrence k T]
        -- RHS terms: rewrite F_j(T) = dChain T j using IH
        rw [ih (k + 2), ih (k + 1), ih k]

/-- The spike-at-k center equals dChain T k.
    Proved: rule30n T (spikeAt k) = (caEvolve T (spikeAtList k (2*T+1))).getD 0 false = dChain T k. -/
lemma rule30n_spike_dChain (T k : Nat) (hk : k < 2 * T + 1) :
    rule30n T (fun j : Fin (2 * T + 1) => decide (j.val = k)) = dChain T k := by
  -- rule30n unfolds to caEvolve on configToList, which equals spikeAtList
  unfold rule30n
  rw [configToList_spikeAt T k]
  exact dChain_eq_caEvolve T k

/-
================================================================================
SECTION 5: THE THEOREM
================================================================================
-/

theorem subcaseB_mgt38_witness_proved
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_ge40 : 40 ≤ m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_not_rm : m.val ≠ 2 * (n' + 1) - 8)
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m) := by
  -- Witness: twoSpike(2, m)
  -- Parity-clean: positions 2 and m are both even; all odd positions = 0.
  -- Sensitivity: G_{2,m} = !F_2 ≠ F_2 (delta = 1, from twoSpike_center_complement)
  refine ⟨fun j => decide (j.val = 2 ∨ j.val = m.val), ?_, ?_⟩
  · -- Parity-clean: 2*k+1 is odd; positions 2 (even) and m (even, hm_even) never match
    intro k
    simp only [decide_eq_false_iff_not, not_or]
    exact ⟨by omega, by omega⟩
  · -- Sensitivity: rule30n(twoSpike 2 m) ≠ rule30n(flipCell(twoSpike 2 m) m)
    -- flipCell(twoSpike 2 m) at m: m goes from 1 → 0, leaving spikeAt(2)
    have h_flip : flipCell (fun j : Fin (2 * (n' + 1) + 1) =>
        decide (j.val = 2 ∨ j.val = m.val)) m =
        fun j => decide (j.val = 2) := by
      funext j
      simp only [flipCell]
      split_ifs with hj
      · -- j = m: flip true → false; since m ≥ 40 ≠ 2, decide(m=2 ∨ m=m)=true, !true=false=decide(m=2)
        have hval : j.val = m.val := congrArg Fin.val hj
        have hm_ne2 : ¬(m.val = 2) := by omega
        have hj_ne2 : ¬(j.val = 2) := hval ▸ hm_ne2
        -- decide(j=2 ∨ j=m) = decide(false ∨ true) = true; !true = false = decide(j=2)
        simp only [hval, or_true, decide_true, Bool.not_true]
        exact (decide_eq_false_iff_not.mpr hm_ne2).symm
      · -- j ≠ m: decide(j=2 ∨ j=m) = decide(j=2) since j ≠ m
        have hval : j.val ≠ m.val := fun h => hj (Fin.ext h)
        simp [hval]
    -- Get SubcaseB condition as dChain statement
    have hSB : dChain (n' + 1) m.val = false := by
      rw [← rule30n_spike_dChain (n' + 1) m.val (by omega)]
      exact hcase
    -- Convert hts to the form expected by twoSpike_center_complement
    -- (hts uses ∨ with m first; twoSpike_center_complement uses same order)
    have hts' : rule30n (n' + 1) (fun j : Fin (2 * (n' + 1) + 1) =>
        decide (j.val = m.val ∨ j.val = 2 * (n' + 1))) = true := hts
    -- Apply the delta lemma: G_{2,m} = !F_2
    -- T = n'+1, so hm_not_rm : m.val ≠ 2*(n'+1)-8 = 2*T-8,
    --                hm_ne_r  : m.val ≠ 2*n' = 2*(T-1)
    have h_lhs : rule30n (n' + 1) (fun j : Fin (2 * (n' + 1) + 1) =>
        decide (j.val = 2 ∨ j.val = m.val)) = !dChain (n' + 1) 2 :=
      twoSpike_center_complement (n' + 1) m.val (by omega) (by omega) hm_even
        hm_not_rm hm_ne_r hSB hts'
    -- Rewrite rhs: flipCell(twoSpike 2 m, m) = spikeAt(2)
    rw [h_flip]
    -- rhs = rule30n(spikeAt 2) = dChain (n'+1) 2 = F_2
    have h_rhs : rule30n (n' + 1) (fun j : Fin (2 * (n' + 1) + 1) => decide (j.val = 2)) =
        dChain (n' + 1) 2 :=
      rule30n_spike_dChain (n' + 1) 2 (by omega)
    rw [h_lhs, h_rhs]
    -- !b ≠ b for any Bool
    cases (dChain (n' + 1) 2) <;> simp
