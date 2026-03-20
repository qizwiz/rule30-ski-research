import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic
import P2p.Prize3_Complete

set_option maxHeartbeats 800000

/-!
# Causal Cone Lemmas for Rule 30

Imports definitions from P2p.Prize3_Complete and proves:
1. `caEvolve_add`: composition of caEvolve steps
2. `caStepList_length_eq` / `caEvolve_length_le`: length reduction by 2 per step
3. `caEvolve_agree`: causal cone — agreement on 0..2k implies same result at 0
4. `caEvolve_allFalse`: all-false input stays all-false
5. `caEvolve_drop_comm` + `caEvolve_getD_shift`: position-i result = drop-i then position-0
6. `rule30n_spike6_period16`: period-16 property for spike-at-6 initial condition
-/
lemma caStepList_getD_eq (xs : List Bool) (j : Nat) (h_bound : j + 2 < xs.length) :
    (caStepList xs).getD j false =
    rule30Local (xs.getD j false) (xs.getD (j + 1) false) (xs.getD (j + 2) false) := by
  match xs with
  | [] => exact absurd h_bound (by simp)
  | [_] => exact absurd h_bound (by simp)
  | [_, _] => exact absurd h_bound (by simp)
  | p :: q :: r :: rest =>
    cases j with
    | zero => simp [caStepList, List.getD]
    | succ j' =>
      simp only [caStepList, List.getD_cons_succ]
      have h_tail : j' + 2 < (q :: r :: rest).length := by simp at h_bound ⊢; omega
      exact caStepList_getD_eq (q :: r :: rest) j' h_tail

/-!
## Lemma 1: caEvolve_add
-/

/-- Composition: `caEvolve (a + b) l = caEvolve a (caEvolve b l)`. -/
lemma caEvolve_add (a b : Nat) (l : List Bool) :
    caEvolve (a + b) l = caEvolve a (caEvolve b l) := by
  induction b generalizing l with
  | zero => simp [caEvolve]
  | succ b ih =>
    simp only [Nat.add_succ, caEvolve_succ]
    exact ih (caStepList l)

/-!
## Lemma 2: caStepList_length_eq
-/

/-- caStepList reduces length by exactly 2, for length `>= 2`. -/
lemma caStepList_length_eq (l : List Bool) (h : l.length ≥ 2) :
    (caStepList l).length = l.length - 2 := by
  have key := caStep_length l h; omega

/-!
## Lemma 3: caEvolve_length_le
-/

/-- caEvolve n steps reduces length by 2*n, given input length `>= 2*n`. -/
lemma caEvolve_length_le (n : Nat) (l : List Bool) (h : l.length ≥ 2 * n) :
    (caEvolve n l).length = l.length - 2 * n := by
  induction n generalizing l with
  | zero => simp [caEvolve]
  | succ n ih =>
    simp only [caEvolve]
    have h2 : l.length ≥ 2 := by omega
    have hstep : (caStepList l).length = l.length - 2 := caStepList_length_eq l h2
    have hstep_ge : (caStepList l).length ≥ 2 * n := by omega
    rw [ih (caStepList l) hstep_ge]; omega

/-!
## Lemma 4: caEvolve_agree (causal cone)
-/

/-- Helper: if two lists agree on `0..j+2`, their caStepLists agree at `j`. -/
lemma caStepList_agree (l1 l2 : List Bool) (j : Nat)
    (hlen1 : j + 2 < l1.length) (hlen2 : j + 2 < l2.length)
    (hagree : ∀ i, i ≤ j + 2 → l1.getD i false = l2.getD i false) :
    (caStepList l1).getD j false = (caStepList l2).getD j false := by
  rw [caStepList_getD_eq l1 j hlen1, caStepList_getD_eq l2 j hlen2]
  rw [hagree j (by omega), hagree (j + 1) (by omega), hagree (j + 2) (by omega)]

/-- Causal cone: if two lists agree on `0..2k`, their `caEvolve k` results agree at position 0. -/
lemma caEvolve_agree (k : Nat) (l1 l2 : List Bool)
    (hlen1 : 2 * k < l1.length) (hlen2 : 2 * k < l2.length)
    (hagree : ∀ i, i ≤ 2 * k → l1.getD i false = l2.getD i false) :
    (caEvolve k l1).getD 0 false = (caEvolve k l2).getD 0 false := by
  induction k generalizing l1 l2 with
  | zero =>
    simp only [caEvolve]; exact hagree 0 (by omega)
  | succ k ih =>
    rw [caEvolve_succ, caEvolve_succ]
    have hstep1 : (caStepList l1).length ≥ 2 * k + 1 := by
      have := caStep_length l1 (by omega); omega
    have hstep2 : (caStepList l2).length ≥ 2 * k + 1 := by
      have := caStep_length l2 (by omega); omega
    apply ih
    · omega
    · omega
    · intro i hi
      apply caStepList_agree l1 l2 i
      · omega
      · omega
      · intro j hj; apply hagree; omega

/-!
## Lemma 5: caEvolve_allFalse
-/

/-- If all elements of a list are false, caStepList also produces all-false. -/
lemma caStepList_allFalse (l : List Bool)
    (h : ∀ i, i < l.length → l.getD i false = false) :
    ∀ i, i < (caStepList l).length → (caStepList l).getD i false = false := by
  intro i hi
  by_cases h2 : l.length ≥ 2
  · have hstep_len := caStep_length l h2
    have hi2 : i + 2 < l.length := by omega
    rw [caStepList_getD_eq l i hi2, h i (by omega), h (i + 1) (by omega), h (i + 2) (by omega)]
    rfl
  · have hempty : caStepList l = [] := by
      match l with
      | [] => rfl; | [_] => rfl; | _ :: _ :: _ => simp at h2
    simp [hempty] at hi

/-- If all elements of a list are false, `caEvolve k` produces false at position 0. -/
lemma caEvolve_allFalse (k : Nat) (l : List Bool)
    (h : ∀ i, i < l.length → l.getD i false = false) :
    (caEvolve k l).getD 0 false = false := by
  induction k generalizing l with
  | zero =>
    simp only [caEvolve]
    by_cases hl : 0 < l.length
    · exact h 0 hl
    · have hempty : l = [] := by rcases l with _ | _; rfl; simp at hl
      subst hempty; rfl
  | succ k ih =>
    rw [caEvolve_succ]; exact ih _ (caStepList_allFalse l h)

/-!
## Infrastructure: drop commutativity and position-i shift
-/

/-- caStepList commutes with List.drop. -/
lemma caStepList_drop_comm (l : List Bool) (i : Nat) :
    caStepList (l.drop i) = (caStepList l).drop i := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    match l with
    | [] => simp [caStepList]
    | [_] => simp [caStepList]
    | [a, b] =>
      simp only [List.drop_succ_cons]; rw [ih [b]]; simp [caStepList]
    | p :: q :: r :: rest =>
      simp only [List.drop_succ_cons, caStepList]; exact ih (q :: r :: rest)

/-- caEvolve commutes with List.drop. -/
lemma caEvolve_drop_comm (k : Nat) (l : List Bool) (i : Nat) :
    caEvolve k (l.drop i) = (caEvolve k l).drop i := by
  induction k generalizing l with
  | zero => simp [caEvolve]
  | succ k ih => simp only [caEvolve, ih, caStepList_drop_comm]

/-- Position `i` of caEvolve k l = position 0 of caEvolve k (l.drop i). -/
lemma caEvolve_getD_shift (k : Nat) (l : List Bool) (i : Nat) :
    (caEvolve k l).getD i false = (caEvolve k (l.drop i)).getD 0 false := by
  rw [caEvolve_drop_comm k l i]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-!
## Lemma 6: rule30n_spike6_period16
-/

-- The "spike at position 6" list of length N
def spike6List (N : Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val = 6))

lemma spike6List_length (N : Nat) : (spike6List N).length = N := by
  simp [spike6List, List.length_ofFn]

/-- getD of spike6List N at in-bounds position i = `decide (i = 6)`. -/
lemma spike6List_getD (N : Nat) (i : Nat) (hi : i < N) :
    (spike6List N).getD i false = decide (i = 6) := by
  simp [spike6List, List.getD_eq_getElem?_getD, hi]

/-- The fixed-size computation: caEvolve 16 of spike6List 45 = spike6List 13. -/
lemma caEvolve16_spike6_45 :
    caEvolve 16 (spike6List 45) = spike6List 13 := by
  native_decide

/-- Two spike6Lists agree on positions i..i+j when both have at least i+j+1 elements. -/
lemma drop_spike6_agree_general (N1 N2 : Nat) (i j : Nat)
    (h1 : i + j < N1) (h2 : i + j < N2) :
    (List.drop i (spike6List N1)).getD j false =
    (List.drop i (spike6List N2)).getD j false := by
  simp only [spike6List, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_ofFn]
  simp [h1, h2]

/-- spike6List N1 dropped by i and spike6List N2 dropped by i give the same caEvolve 16 at 0,
    provided both have at least i + 32 + 1 elements (the causal cone for 16 steps). -/
lemma caEvolve16_spike6_agree (N1 N2 : Nat) (i : Nat)
    (h1 : i + 32 < N1) (h2 : i + 32 < N2) :
    (caEvolve 16 (spike6List N1)).getD i false =
    (caEvolve 16 (spike6List N2)).getD i false := by
  rw [caEvolve_getD_shift 16 (spike6List N1) i, caEvolve_getD_shift 16 (spike6List N2) i]
  apply caEvolve_agree 16
  · rw [List.length_drop, spike6List_length]; omega
  · rw [List.length_drop, spike6List_length]; omega
  · intro j hj
    exact drop_spike6_agree_general N1 N2 i j (by omega) (by omega)

/-- spike6List N dropped by i (i >= 7) is all-false. -/
lemma spike6List_drop_allFalse (N : Nat) (i : Nat) (hi : i ≥ 7) :
    ∀ j, j < (List.drop i (spike6List N)).length →
         (List.drop i (spike6List N)).getD j false = false := by
  intro j hj
  simp only [List.length_drop, spike6List_length] at hj
  rw [show (List.drop i (spike6List N)).getD j false = (spike6List N).getD (i + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  by_cases h : i + j < N
  · rw [spike6List_getD N (i + j) h]; simp; omega
  · simp only [List.getD_eq_getElem?_getD, spike6List, List.getElem?_ofFn]
    simp [show ¬(i + j < N) from h]

/-- Period-16 property: caEvolve (n+1) on spike6List (2*(n+1)+1) gives the same result at 0
    as caEvolve (n+17) on spike6List (2*(n+17)+1).

    Proof:
    1. Write n+17 = (n+1)+16 and use caEvolve_add.
    2. Apply caEvolve_agree at scale n+1 to reduce to comparing:
       - LHS inner: spike6List (2*(n+1)+1)
       - RHS inner: caEvolve 16 (spike6List (2*((n+1)+16)+1))
    3. For positions i <= 12 (and i <= 2*(n+1)):
       - LHS = decide (i = 6)
       - RHS at i = caEvolve 16 (spike6List 45) at i [by caEvolve16_spike6_agree, cone fits]
             = spike6List 13 at i [by caEvolve16_spike6_45]
             = decide (i = 6)
    4. For positions 13 <= i <= 2*(n+1):
       - LHS = false (spike at 6, i >= 13)
       - RHS at i = caEvolve 16 (spike6List drop i) at 0 [by shift]
             = false [all-false input, spike < 7 <= i, so drop i misses the spike]
-/
lemma rule30n_spike6_period16 (n : Nat) :
    (caEvolve (n + 1) (spike6List (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve (n + 17) (spike6List (2 * (n + 17) + 1))).getD 0 false := by
  -- Fix syntactic form: n + 17 = (n + 1) + 16
  show (caEvolve (n + 1) (spike6List (2 * (n + 1) + 1))).getD 0 false =
       (caEvolve ((n + 1) + 16) (spike6List (2 * ((n + 1) + 16) + 1))).getD 0 false
  -- Pre-compute RHS length bound (before caEvolve_add rewrites it)
  have rhs_len : 2 * (n + 1) < (caEvolve 16 (spike6List (2 * ((n + 1) + 16) + 1))).length := by
    have hlen := caEvolve_length_le 16 (spike6List (2 * ((n + 1) + 16) + 1))
                (by rw [spike6List_length]; omega)
    rw [spike6List_length] at hlen; omega
  rw [caEvolve_add]
  -- Now: caEvolve (n+1) (spike6 ...) at 0 = caEvolve (n+1) (caEvolve 16 (spike6 ...)) at 0
  apply caEvolve_agree (n + 1)
  · rw [spike6List_length]; omega
  · exact rhs_len
  · intro i hi
    -- Use 'suffices' to avoid Lean reducing caEvolve 16 in the goal
    suffices h : (spike6List (2*(n+1)+1)).getD i false =
                 (caEvolve 16 (spike6List (2*(n+1+16)+1))).getD i false by exact h
    by_cases h12 : i ≤ 12
    · -- Positions 0..12: both equal decide (i = 6)
      rw [spike6List_getD _ i (by omega)]
      -- Compare RHS with spike6List 45 at position i via causal cone
      rw [caEvolve16_spike6_agree (2*(n+1+16)+1) 45 i (by omega) (by omega)]
      rw [caEvolve16_spike6_45]
      rw [spike6List_getD 13 i (by omega)]
    · -- Positions 13..2*(n+1): both are false
      have hi13 : i ≥ 13 := by omega
      have lhs_false : (spike6List (2*(n+1)+1)).getD i false = false := by
        rw [spike6List_getD _ i (by omega)]; simp; omega
      have rhs_false : (caEvolve 16 (spike6List (2*(n+1+16)+1))).getD i false = false := by
        rw [caEvolve_getD_shift 16 _ i]
        apply caEvolve_allFalse
        exact spike6List_drop_allFalse (2*(n+1+16)+1) i (by omega)
      rw [lhs_false, rhs_false]

/-!
## Lemma 7: rule30n_spike20_period256
-/

-- The "spike at position 20" list of length N
def spike20List (N : Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val = 20))

lemma spike20List_length (N : Nat) : (spike20List N).length = N := by
  simp [spike20List, List.length_ofFn]

/-- getD of spike20List N at in-bounds position i = `decide (i = 20)`. -/
lemma spike20List_getD (N : Nat) (i : Nat) (hi : i < N) :
    (spike20List N).getD i false = decide (i = 20) := by
  simp [spike20List, List.getD_eq_getElem?_getD, hi]

set_option maxHeartbeats 4000000000 in
/-- The fixed-size computation: caEvolve 256 of spike20List 533 = spike20List 21. -/
lemma caEvolve256_spike20_533 :
    caEvolve 256 (spike20List 533) = spike20List 21 := by
  native_decide

/-- Two spike20Lists agree on positions i..i+j when both have at least i+j+1 elements. -/
lemma drop_spike20_agree_general (N1 N2 : Nat) (i j : Nat)
    (h1 : i + j < N1) (h2 : i + j < N2) :
    (List.drop i (spike20List N1)).getD j false =
    (List.drop i (spike20List N2)).getD j false := by
  simp only [spike20List, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_ofFn]
  simp [h1, h2]

/-- spike20List N1 dropped by i and spike20List N2 dropped by i give the same caEvolve 256 at 0,
    provided both have at least i + 512 + 1 elements (the causal cone for 256 steps). -/
lemma caEvolve256_spike20_agree (N1 N2 : Nat) (i : Nat)
    (h1 : i + 512 < N1) (h2 : i + 512 < N2) :
    (caEvolve 256 (spike20List N1)).getD i false =
    (caEvolve 256 (spike20List N2)).getD i false := by
  rw [caEvolve_getD_shift 256 (spike20List N1) i, caEvolve_getD_shift 256 (spike20List N2) i]
  apply caEvolve_agree 256
  · rw [List.length_drop, spike20List_length]; omega
  · rw [List.length_drop, spike20List_length]; omega
  · intro j hj
    exact drop_spike20_agree_general N1 N2 i j (by omega) (by omega)

/-- spike20List N dropped by i (i >= 21) is all-false. -/
lemma spike20List_drop_allFalse (N : Nat) (i : Nat) (hi : i ≥ 21) :
    ∀ j, j < (List.drop i (spike20List N)).length →
         (List.drop i (spike20List N)).getD j false = false := by
  intro j hj
  simp only [List.length_drop, spike20List_length] at hj
  rw [show (List.drop i (spike20List N)).getD j false = (spike20List N).getD (i + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  by_cases h : i + j < N
  · rw [spike20List_getD N (i + j) h]; simp; omega
  · simp only [List.getD_eq_getElem?_getD, spike20List, List.getElem?_ofFn]
    simp [show ¬(i + j < N) from h]

/-- Period-256 property: caEvolve (n+1) on spike20List (2*(n+1)+1) gives the same result at 0
    as caEvolve (n+257) on spike20List (2*(n+257)+1).

    Proof structure mirrors rule30n_spike6_period16 with period=256, size=533, target=21.
    Cutoff: positions i ≤ 20 use the fixed computation; positions i ≥ 21 are all-false.
-/
lemma rule30n_spike20_period256 (n : Nat) :
    (caEvolve (n + 1) (spike20List (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve (n + 257) (spike20List (2 * (n + 257) + 1))).getD 0 false := by
  -- Fix syntactic form: n + 257 = (n + 1) + 256
  show (caEvolve (n + 1) (spike20List (2 * (n + 1) + 1))).getD 0 false =
       (caEvolve ((n + 1) + 256) (spike20List (2 * ((n + 1) + 256) + 1))).getD 0 false
  -- Pre-compute RHS length bound (before caEvolve_add rewrites it)
  have rhs_len : 2 * (n + 1) < (caEvolve 256 (spike20List (2 * ((n + 1) + 256) + 1))).length := by
    have hlen := caEvolve_length_le 256 (spike20List (2 * ((n + 1) + 256) + 1))
                (by rw [spike20List_length]; omega)
    rw [spike20List_length] at hlen; omega
  rw [caEvolve_add]
  apply caEvolve_agree (n + 1)
  · rw [spike20List_length]; omega
  · exact rhs_len
  · intro i hi
    suffices h : (spike20List (2*(n+1)+1)).getD i false =
                 (caEvolve 256 (spike20List (2*(n+1+256)+1))).getD i false by exact h
    by_cases h20 : i ≤ 20
    · -- Positions 0..20: both equal decide (i = 20)
      rw [spike20List_getD _ i (by omega)]
      -- Compare RHS with spike20List 533 at position i via causal cone
      rw [caEvolve256_spike20_agree (2*(n+1+256)+1) 533 i (by omega) (by omega)]
      rw [caEvolve256_spike20_533]
      rw [spike20List_getD 21 i (by omega)]
    · -- Positions 21..2*(n+1): both are false
      have hi21 : i ≥ 21 := by omega
      have lhs_false : (spike20List (2*(n+1)+1)).getD i false = false := by
        rw [spike20List_getD _ i (by omega)]; simp; omega
      have rhs_false : (caEvolve 256 (spike20List (2*(n+1+256)+1))).getD i false = false := by
        rw [caEvolve_getD_shift 256 _ i]
        apply caEvolve_allFalse
        exact spike20List_drop_allFalse (2*(n+1+256)+1) i (by omega)
      rw [lhs_false, rhs_false]

/-!
## Lemma 8: ts2_last_always_false

`ts2LastList (2*n+1)` has spikes at position 2 and position 2*n (the last cell).
After n caEvolve steps on a (2*n+1)-cell list, we get a 1-cell list.

Verification for small n:
- n=1: ts2LastList 3 = [F,F,T] (positions 2 and 2 coincide), caEvolve 1 = [T] → **true** (not false!)
- n=2: ts2LastList 5 = [F,F,T,F,T], caEvolve 2 → [F] → false ✓
- n≥2: consistently false

So the correct statement needs hypothesis `2 ≤ n`.

Proof strategy:
- Key recurrence: `caEvolve 2 (ts2LastList (2*n+5)) = ts2LastList (2*n+1)` (as getD-equal lists).
  This is proved by causal cone analysis: for each output position i ≤ 2n, the 5-element
  causal cone of caEvolve 2 at position i is determined by which spike (if any) falls within
  positions i..i+4 of the input ts2LastList(2n+5).
- This gives: `caEvolve (n+2) (ts2LastList (2*(n+2)+1))` at 0 = `caEvolve n (ts2LastList (2*n+1))` at 0.
- Base cases n=2, n=3 by native_decide. Strong induction completes the proof.
-/

-- The "spike at position 2 and last position" list of length N
-- ts2LastList N has true at position 2 and at position N-1
def ts2LastList (N : Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val = 2 || k.val = N - 1))

lemma ts2LastList_length (N : Nat) : (ts2LastList N).length = N := by
  simp [ts2LastList, List.length_ofFn]

/-- getD of ts2LastList N at in-bounds position i. -/
lemma ts2LastList_getD (N : Nat) (i : Nat) (hi : i < N) :
    (ts2LastList N).getD i false = decide (i = 2 || i = N - 1) := by
  simp [ts2LastList, List.getD_eq_getElem?_getD, hi]

-- Verification for n=1: result is TRUE (so n=1 is NOT covered by the false claim)
lemma ts2_last_n1_is_true :
    (caEvolve 1 (ts2LastList (2 * 1 + 1))).getD 0 false = true := by native_decide

-- 5-element causal-cone base computations for caEvolve 2
private lemma caEvolve2_TFFFF : (caEvolve 2 [true, false, false, false, false]).getD 0 false = true := by native_decide
private lemma caEvolve2_FTFFF : (caEvolve 2 [false, true, false, false, false]).getD 0 false = false := by native_decide
private lemma caEvolve2_FFTFF : (caEvolve 2 [false, false, true, false, false]).getD 0 false = false := by native_decide
private lemma caEvolve2_FFFFF : (caEvolve 2 [false, false, false, false, false]).getD 0 false = false := by native_decide
private lemma caEvolve2_FFFFT : (caEvolve 2 [false, false, false, false, true]).getD 0 false = true := by native_decide

/-- getD of (ts2LastList(2n+5)).drop i at position j (when i+j in range). -/
private lemma ts2Last_drop_getD (n : Nat) (i j : Nat) (hij : i + j < 2*n+5) :
    ((ts2LastList (2*n+5)).drop i).getD j false = decide (i + j = 2 || i + j = 2*n + 4) := by
  rw [show ((ts2LastList (2*n+5)).drop i).getD j false = (ts2LastList (2*n+5)).getD (i+j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [ts2LastList_getD (2*n+5) (i+j) hij]
  simp only [show (2*n+5) - 1 = 2*n+4 from by omega]

/-- Agreement between (ts2LastList(2n+5)).drop i and a canonical 5-element list on positions 0..4.
    There are 5 cases depending on where i falls relative to the left spike (pos 2). -/
private lemma ts2Last_agree5_i0 (n : Nat) (hn : n ≥ 2) :
    ∀ j ≤ 4, ((ts2LastList (2*n+5)).drop 0).getD j false =
             ([false, false, true, false, false] : List Bool).getD j false := fun j hj => by
  rw [ts2Last_drop_getD n 0 j (by omega)]
  simp only [show (0:Nat) + j = j from by omega]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [List.getD] <;> try omega

private lemma ts2Last_agree5_i1 (n : Nat) (hn : n ≥ 2) :
    ∀ j ≤ 4, ((ts2LastList (2*n+5)).drop 1).getD j false =
             ([false, true, false, false, false] : List Bool).getD j false := fun j hj => by
  rw [ts2Last_drop_getD n 1 j (by omega)]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [List.getD] <;> try omega

private lemma ts2Last_agree5_i2 (n : Nat) (hn : n ≥ 2) :
    ∀ j ≤ 4, ((ts2LastList (2*n+5)).drop 2).getD j false =
             ([true, false, false, false, false] : List Bool).getD j false := fun j hj => by
  rw [ts2Last_drop_getD n 2 j (by omega)]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [List.getD] <;> try omega

private lemma ts2Last_agree5_ige3 (n : Nat) (hn : n ≥ 2) (i : Nat) (hi3 : i ≥ 3) (hi' : i < 2*n) :
    ∀ j ≤ 4, ((ts2LastList (2*n+5)).drop i).getD j false =
             ([false, false, false, false, false] : List Bool).getD j false := fun j hj => by
  rw [ts2Last_drop_getD n i j (by omega)]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [List.getD] <;> try omega

private lemma ts2Last_agree5_i2n (n : Nat) (hn : n ≥ 2) :
    ∀ j ≤ 4, ((ts2LastList (2*n+5)).drop (2*n)).getD j false =
             ([false, false, false, false, true] : List Bool).getD j false := fun j hj => by
  rw [ts2Last_drop_getD n (2*n) j (by omega)]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [List.getD] <;> try omega

/-- Positional agreement: caEvolve 2 applied to ts2LastList(2n+5) at position i equals
    ts2LastList(2n+1) at position i, for all i ≤ 2n.

    Proof: Use caEvolve_getD_shift and caEvolve_agree 2 with a 5-element canonical list.
    The 5-element causal cone at position i of ts2LastList(2n+5) sees:
    - i ∈ {0,1,2}: left spike at position 2; window [F,F,T,...], [F,T,F,...], or [T,F,F,...]
    - 3 ≤ i ≤ 2n-1: no spike in the cone; window all-false
    - i = 2n: right spike at exactly position 4 of the window; window [F,F,F,F,T] -/
lemma caEvolve2_ts2Last_pos (n : Nat) (hn : n ≥ 2) (i : Nat) (hi : i ≤ 2*n) :
    (caEvolve 2 (ts2LastList (2*n+5))).getD i false = (ts2LastList (2*n+1)).getD i false := by
  rw [caEvolve_getD_shift 2 (ts2LastList (2*n+5)) i, ts2LastList_getD (2*n+1) i (by omega)]
  simp only [show (2*n+1) - 1 = 2*n from by omega]
  have hlen : ((ts2LastList (2*n+5)).drop i).length ≥ 5 := by
    rw [List.length_drop, ts2LastList_length]; omega
  rcases Nat.lt_or_eq_of_le hi with hi_lt | rfl
  · -- i < 2n
    rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with rfl | hi_pos
    · -- i = 0
      simp only [show (0:Nat) ≠ 2 from by omega, show (0:Nat) ≠ 2*n from by omega,
                 Bool.or_false, decide_false]
      exact (caEvolve_agree 2 _ _ hlen (by simp) (ts2Last_agree5_i0 n hn)).trans caEvolve2_FFTFF
    · rcases Nat.eq_or_lt_of_le hi_pos with rfl | hi2
      · -- i = 1
        simp only [show (1:Nat) ≠ 2 from by omega, show (1:Nat) ≠ 2*n from by omega,
                   Bool.or_false, decide_false]
        exact (caEvolve_agree 2 _ _ hlen (by simp) (ts2Last_agree5_i1 n hn)).trans caEvolve2_FTFFF
      · rcases Nat.eq_or_lt_of_le hi2 with rfl | hi3
        · -- i = 2
          simp only [show (2:Nat) = 2 from rfl, Bool.true_or, decide_true]
          exact (caEvolve_agree 2 _ _ hlen (by simp) (ts2Last_agree5_i2 n hn)).trans caEvolve2_TFFFF
        · -- i ≥ 3
          simp only [show i ≠ 2 from by omega, show i ≠ 2*n from by omega,
                     Bool.or_false, decide_false]
          exact (caEvolve_agree 2 _ _ hlen (by simp)
            (ts2Last_agree5_ige3 n hn i hi3 (by omega))).trans caEvolve2_FFFFF
  · -- i = 2n
    simp only [show 2*n = 2*n from rfl, Bool.or_true, decide_true]
    apply (caEvolve_agree 2 _ _ _ (by simp) (ts2Last_agree5_i2n n hn)).trans caEvolve2_FFFFT
    rw [List.length_drop, ts2LastList_length]; omega

/-- Step-2 recurrence: caEvolve(n+2) on ts2LastList(2*(n+2)+1) equals caEvolve n on ts2LastList(2*n+1)
    at position 0.

    Proof: Write n+2 = n+2 and apply caEvolve_add, then use caEvolve_agree n with
    caEvolve2_ts2Last_pos to show the two inner lists agree on all relevant positions. -/
lemma ts2_last_step2 (n : Nat) (hn : 2 ≤ n) :
    (caEvolve (n + 2) (ts2LastList (2 * (n + 2) + 1))).getD 0 false =
    (caEvolve n (ts2LastList (2 * n + 1))).getD 0 false := by
  simp only [show 2 * (n + 2) + 1 = 2 * n + 5 from by omega]
  rw [caEvolve_add n 2]
  apply caEvolve_agree n
  · have := caEvolve_length_le 2 (ts2LastList (2*n+5)) (by rw [ts2LastList_length]; omega)
    rw [ts2LastList_length] at this; omega
  · rw [ts2LastList_length]; omega
  · intro i hi
    exact caEvolve2_ts2Last_pos n hn i (by omega)

/-- For n ≥ 2, `caEvolve n (ts2LastList (2*n+1))` outputs false at position 0.

    Proof by strong induction:
    - Base cases n=2, n=3 by native_decide.
    - Inductive step (n ≥ 4): use ts2_last_step2 to reduce to n-2. -/
theorem ts2_last_always_false (n : Nat) (hn : 2 ≤ n) :
    (caEvolve n (ts2LastList (2 * n + 1))).getD 0 false = false := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · -- n ∈ {2, 3}: base cases
      rcases Nat.eq_or_lt_of_le hn with rfl | hn3
      · native_decide
      · have : n = 3 := by omega
        subst this; native_decide
    · -- n ≥ 4: reduce to n-2 via ts2_last_step2
      have hprev2 : 2 ≤ n - 2 := by omega
      have key := ts2_last_step2 (n - 2) hprev2
      simp only [show n - 2 + 2 = n from by omega] at key
      rw [key]
      exact ih (n - 2) (by omega) hprev2

-- Type-check all key lemmas
#check @caEvolve_add
#check @caEvolve_length_le
#check @caEvolve_agree
#check @caEvolve_allFalse
#check @caEvolve_drop_comm
#check @caEvolve_getD_shift
#check @rule30n_spike6_period16
#check @rule30n_spike20_period256
