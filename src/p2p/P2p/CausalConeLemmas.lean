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

/-!
## Parametric spike infrastructure for all active m

Rather than duplicating 80 lines per m-value, we define a single `spikeAtList m N`
and prove the causal-cone agreement and period lemma once, parametrically.
Individual m-values only need a `native_decide` certificate of the form:
  `caEvolve P_m (spikeAtList m (2*P_m+2*m+1)) = spikeAtList m (2*m+1)`
-/

/-- A list of length N with `true` at position m, `false` elsewhere. -/
def spikeAtList (m N : Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val = m))

lemma spikeAtList_length (m N : Nat) : (spikeAtList m N).length = N := by
  simp [spikeAtList, List.length_ofFn]

/-- `spikeAtList m N` at in-bounds position i equals `decide (i = m)`. -/
lemma spikeAtList_getD (m N i : Nat) (hi : i < N) :
    (spikeAtList m N).getD i false = decide (i = m) := by
  simp [spikeAtList, List.getD_eq_getElem?_getD, hi]

/-- Two spikeAtList m lists agree at position i+j whenever both contain that index. -/
lemma drop_spikeAt_agree (m N1 N2 i j : Nat)
    (h1 : i + j < N1) (h2 : i + j < N2) :
    (List.drop i (spikeAtList m N1)).getD j false =
    (List.drop i (spikeAtList m N2)).getD j false := by
  simp only [spikeAtList, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_ofFn]
  simp [h1, h2]

/-- `spikeAtList m N` dropped by `i > m` is all-false (the spike is behind the drop point). -/
lemma spikeAtList_drop_allFalse (m N i : Nat) (hi : i > m) :
    ∀ j, j < (List.drop i (spikeAtList m N)).length →
         (List.drop i (spikeAtList m N)).getD j false = false := by
  intro j hj
  simp only [List.length_drop, spikeAtList_length] at hj
  rw [show ((spikeAtList m N).drop i).getD j false = (spikeAtList m N).getD (i + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  by_cases h : i + j < N
  · rw [spikeAtList_getD m N (i + j) h]; simp; omega
  · simp only [List.getD_eq_getElem?_getD, spikeAtList, List.getElem?_ofFn]
    simp [show ¬(i + j < N) from h]

/-- Causal-cone independence: `caEvolve P` on spikeAtList m agrees between two lists of
    different sizes, provided both contain position `i + 2*P`. -/
lemma caEvolve_spikeAt_agree (P m N1 N2 i : Nat)
    (h1 : i + 2 * P < N1) (h2 : i + 2 * P < N2) :
    (caEvolve P (spikeAtList m N1)).getD i false =
    (caEvolve P (spikeAtList m N2)).getD i false := by
  rw [caEvolve_getD_shift P (spikeAtList m N1) i, caEvolve_getD_shift P (spikeAtList m N2) i]
  apply caEvolve_agree P
  · rw [List.length_drop, spikeAtList_length]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj; exact drop_spikeAt_agree m N1 N2 i j (by omega) (by omega)

/-- Parametric period lemma for spike-at-m with period P.

    Given a `native_decide` certificate
      `caEvolve P (spikeAtList m (2*P+2*m+1)) = spikeAtList m (2*m+1)`,
    this proves F(n, m) = F(n+P, m) for all n (i.e., the center value of
    rule30^{n+1} starting from spike-at-m is periodic with period P).

    Proof structure (mirrors rule30n_spike6_period16):
    1. Write n+1+P as (n+1)+P and apply caEvolve_add.
    2. Apply caEvolve_agree at scale n+1.
    3. For i ≤ m: use the certificate + causal-cone independence.
    4. For i > m: the drop-by-i is all-false on both sides.
-/
lemma rule30n_spikeAt_period (m P : Nat)
    (hcert : caEvolve P (spikeAtList m (2*P+2*m+1)) = spikeAtList m (2*m+1))
    (n : Nat) :
    (caEvolve (n + 1) (spikeAtList m (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n + 1) + P) (spikeAtList m (2*((n+1)+P)+1))).getD 0 false := by
  have rhs_len : 2*(n+1) < (caEvolve P (spikeAtList m (2*((n+1)+P)+1))).length := by
    have hlen := caEvolve_length_le P (spikeAtList m (2*((n+1)+P)+1))
                (by rw [spikeAtList_length]; omega)
    rw [spikeAtList_length] at hlen; omega
  conv_rhs => rw [caEvolve_add (n+1) P]
  apply caEvolve_agree (n + 1)
  · rw [spikeAtList_length]; omega
  · exact rhs_len
  · intro i hi
    suffices h : (spikeAtList m (2*(n+1)+1)).getD i false =
                 (caEvolve P (spikeAtList m (2*(n+1+P)+1))).getD i false by exact h
    by_cases hm : i ≤ m
    · -- positions 0..m: both equal decide(i = m)
      rw [spikeAtList_getD m (2*(n+1)+1) i (by omega)]
      rw [caEvolve_spikeAt_agree P m (2*(n+1+P)+1) (2*P+2*m+1) i (by omega) (by omega)]
      rw [hcert]
      rw [spikeAtList_getD m (2*m+1) i (by omega)]
    · -- positions m+1..2*(n+1): both are false
      have lhs_false : (spikeAtList m (2*(n+1)+1)).getD i false = false := by
        rw [spikeAtList_getD m (2*(n+1)+1) i (by omega)]; simp; omega
      have rhs_false : (caEvolve P (spikeAtList m (2*(n+1+P)+1))).getD i false = false := by
        rw [caEvolve_getD_shift P _ i]
        apply caEvolve_allFalse
        exact spikeAtList_drop_allFalse m (2*(n+1+P)+1) i (by omega)
      rw [lhs_false, rhs_false]

/-!
## Period certificates: native_decide for each active m
Active m-set: {4,6,8,10,12,14,16,20,22,24,26,28,30,34,36,38}
Periods:   P_m ∈ {8,16,32,64,64,64,256,256,256,512,1024,2048,4096,8192,16384,32768}
Certificate form: caEvolve P_m (spikeAtList m (2*P_m+2*m+1)) = spikeAtList m (2*m+1)
m=6 and m=20 already have dedicated spike6List/spike20List infrastructure above.
-/

-- m=4, P=8: input=25, output=spike4 at 9
lemma caEvolve_cert_m4_p8 :
    caEvolve 8 (spikeAtList 4 25) = spikeAtList 4 9 := by native_decide

lemma rule30n_spikeAt4_period8 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 4 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+8) (spikeAtList 4 (2*((n+1)+8)+1))).getD 0 false :=
  rule30n_spikeAt_period 4 8 caEvolve_cert_m4_p8 n

-- m=6, P=16: input=45, output=spike6 at 13
lemma caEvolve_cert_m6_p16 :
    caEvolve 16 (spikeAtList 6 45) = spikeAtList 6 13 := by native_decide

lemma rule30n_spikeAt6_period16 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 6 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+16) (spikeAtList 6 (2*((n+1)+16)+1))).getD 0 false :=
  rule30n_spikeAt_period 6 16 caEvolve_cert_m6_p16 n

-- m=8, P=32: input=81, output=spike8 at 17
lemma caEvolve_cert_m8_p32 :
    caEvolve 32 (spikeAtList 8 81) = spikeAtList 8 17 := by native_decide

lemma rule30n_spikeAt8_period32 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 8 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+32) (spikeAtList 8 (2*((n+1)+32)+1))).getD 0 false :=
  rule30n_spikeAt_period 8 32 caEvolve_cert_m8_p32 n

-- m=10, P=64: input=149, output=spike10 at 21
lemma caEvolve_cert_m10_p64 :
    caEvolve 64 (spikeAtList 10 149) = spikeAtList 10 21 := by native_decide

lemma rule30n_spikeAt10_period64 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 10 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+64) (spikeAtList 10 (2*((n+1)+64)+1))).getD 0 false :=
  rule30n_spikeAt_period 10 64 caEvolve_cert_m10_p64 n

-- m=12, P=64: input=153, output=spike12 at 25
lemma caEvolve_cert_m12_p64 :
    caEvolve 64 (spikeAtList 12 153) = spikeAtList 12 25 := by native_decide

lemma rule30n_spikeAt12_period64 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 12 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+64) (spikeAtList 12 (2*((n+1)+64)+1))).getD 0 false :=
  rule30n_spikeAt_period 12 64 caEvolve_cert_m12_p64 n

-- m=14, P=64: input=157, output=spike14 at 29
lemma caEvolve_cert_m14_p64 :
    caEvolve 64 (spikeAtList 14 157) = spikeAtList 14 29 := by native_decide

lemma rule30n_spikeAt14_period64 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 14 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+64) (spikeAtList 14 (2*((n+1)+64)+1))).getD 0 false :=
  rule30n_spikeAt_period 14 64 caEvolve_cert_m14_p64 n

-- m=16, P=256: input=545, output=spike16 at 33
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m16_p256 :
    caEvolve 256 (spikeAtList 16 545) = spikeAtList 16 33 := by native_decide

lemma rule30n_spikeAt16_period256 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 16 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+256) (spikeAtList 16 (2*((n+1)+256)+1))).getD 0 false :=
  rule30n_spikeAt_period 16 256 caEvolve_cert_m16_p256 n

-- m=20, P=256: input=553, output=spike20 at 41
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m20_p256 :
    caEvolve 256 (spikeAtList 20 553) = spikeAtList 20 41 := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_spikeAt20_period256 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 20 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+256) (spikeAtList 20 (2*((n+1)+256)+1))).getD 0 false :=
  rule30n_spikeAt_period 20 256 caEvolve_cert_m20_p256 n

-- m=22, P=256: input=557, output=spike22 at 45
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m22_p256 :
    caEvolve 256 (spikeAtList 22 557) = spikeAtList 22 45 := by native_decide

lemma rule30n_spikeAt22_period256 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 22 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+256) (spikeAtList 22 (2*((n+1)+256)+1))).getD 0 false :=
  rule30n_spikeAt_period 22 256 caEvolve_cert_m22_p256 n

-- m=24, P=512: input=1073, output=spike24 at 49
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m24_p512 :
    caEvolve 512 (spikeAtList 24 1073) = spikeAtList 24 49 := by native_decide

lemma rule30n_spikeAt24_period512 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 24 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+512) (spikeAtList 24 (2*((n+1)+512)+1))).getD 0 false :=
  rule30n_spikeAt_period 24 512 caEvolve_cert_m24_p512 n

-- m=26, P=1024: input=2101, output=spike26 at 53
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m26_p1024 :
    caEvolve 1024 (spikeAtList 26 2101) = spikeAtList 26 53 := by native_decide

lemma rule30n_spikeAt26_period1024 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 26 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+1024) (spikeAtList 26 (2*((n+1)+1024)+1))).getD 0 false :=
  rule30n_spikeAt_period 26 1024 caEvolve_cert_m26_p1024 n

-- m=28, P=2048: input=4153, output=spike28 at 57
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m28_p2048 :
    caEvolve 2048 (spikeAtList 28 4153) = spikeAtList 28 57 := by native_decide

lemma rule30n_spikeAt28_period2048 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 28 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+2048) (spikeAtList 28 (2*((n+1)+2048)+1))).getD 0 false :=
  rule30n_spikeAt_period 28 2048 caEvolve_cert_m28_p2048 n

-- m=30, P=4096: input=8253, output=spike30 at 61
set_option maxHeartbeats 4000000000 in
lemma caEvolve_cert_m30_p4096 :
    caEvolve 4096 (spikeAtList 30 8253) = spikeAtList 30 61 := by native_decide

lemma rule30n_spikeAt30_period4096 (n : Nat) :
    (caEvolve (n+1) (spikeAtList 30 (2*(n+1)+1))).getD 0 false =
    (caEvolve ((n+1)+4096) (spikeAtList 30 (2*((n+1)+4096)+1))).getD 0 false :=
  rule30n_spikeAt_period 30 4096 caEvolve_cert_m30_p4096 n

-- m=34, P=8192: input=16453, output=spike34 at 69
-- NOTE: ~67M List Bool cells → crashes with linked-list native_decide (OOM).
-- Needs a packed BitVec/Array Bool implementation. Deferred.
-- lemma caEvolve_cert_m34_p8192 :
--     caEvolve 8192 (spikeAtList 34 16453) = spikeAtList 34 69 := by native_decide

-- m=36, P=16384: input=32841, output=spike36 at 73
-- NOTE: ~270M cells — requires BitVec/Array Bool implementation.
-- lemma caEvolve_cert_m36_p16384 :
--     caEvolve 16384 (spikeAtList 36 32841) = spikeAtList 36 73 := by native_decide

-- m=38, P=32768: input=65613, output=spike38 at 77
-- NOTE: ~1.1B cells — requires BitVec/Array Bool implementation.
-- lemma caEvolve_cert_m38_p32768 :
--     caEvolve 32768 (spikeAtList 38 65613) = spikeAtList 38 77 := by native_decide

/-!
## Two-spike-last infrastructure for G-periodicity

The SubcaseB condition requires showing G(n', m) is periodic (in addition to F).
G(n', m) = caEvolve (n'+1) (twoSpikeLastList m (2*(n'+1)+1)).getD 0 false
where twoSpikeLastList m N has spikes at position m and at the LAST position N-1.

Key: same period certificate holds:
  caEvolve P_m (twoSpikeLastList m (2*P_m+2*m+1)) = twoSpikeLastList m (2*m+1)
Proof sketch: after P_m steps the last spike (at position 2*P_m+2*m) is at the last
position of the output (2*m), and the left spike at m is preserved by the F certificate.
The right spike for positions i ≤ 2*(n'+1)-1 is outside the causal cone (> 2*P_m away)
so cannot affect those positions.
-/

/-- A list of length N with `true` at position m AND at position N-1 (last). -/
def twoSpikeLastList (m N : Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val = m || k.val = N - 1))

lemma twoSpikeLastList_length (m N : Nat) : (twoSpikeLastList m N).length = N := by
  simp [twoSpikeLastList, List.length_ofFn]

/-- `twoSpikeLastList m N` at in-bounds position i = `decide (i = m ∨ i = N-1)`. -/
lemma twoSpikeLastList_getD (m N i : Nat) (hi : i < N) :
    (twoSpikeLastList m N).getD i false = decide (i = m ∨ i = N - 1) := by
  simp [twoSpikeLastList, List.getD_eq_getElem?_getD, hi]

/-- `twoSpikeLastList m N` dropped by i, with i+j+1 < N (in-bounds), gives
    value `decide(i+j = m ∨ i+j = N-1)`. -/
lemma twoSpikeLastList_drop_getD (m N i j : Nat) (h : i + j < N) :
    (List.drop i (twoSpikeLastList m N)).getD j false = decide (i + j = m ∨ i + j = N - 1) := by
  rw [show ((List.drop i (twoSpikeLastList m N)).getD j false) =
        (twoSpikeLastList m N).getD (i + j) false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [twoSpikeLastList_getD m N (i + j) h]

/-!
## Period certificates for twoSpikeLastList

Same formula as spikeAtList:
  caEvolve P_m (twoSpikeLastList m (2*P_m+2*m+1)) = twoSpikeLastList m (2*m+1)
Verified computationally for all active m with P_m ≤ 256.
-/

-- m=4, P=8: input=25, output=twoSpikeLast(4,9): spikes at 4 and 8
lemma caEvolve_tsl_cert_m4_p8 :
    caEvolve 8 (twoSpikeLastList 4 25) = twoSpikeLastList 4 9 := by native_decide

-- m=6, P=16: input=45, output=twoSpikeLast(6,13): spikes at 6 and 12
lemma caEvolve_tsl_cert_m6_p16 :
    caEvolve 16 (twoSpikeLastList 6 45) = twoSpikeLastList 6 13 := by native_decide

-- m=8, P=32: input=81, output=twoSpikeLast(8,17): spikes at 8 and 16
lemma caEvolve_tsl_cert_m8_p32 :
    caEvolve 32 (twoSpikeLastList 8 81) = twoSpikeLastList 8 17 := by native_decide

-- m=10, P=64: input=149, output=twoSpikeLast(10,21): spikes at 10 and 20
lemma caEvolve_tsl_cert_m10_p64 :
    caEvolve 64 (twoSpikeLastList 10 149) = twoSpikeLastList 10 21 := by native_decide

-- m=12, P=64: input=153, output=twoSpikeLast(12,25): spikes at 12 and 24
lemma caEvolve_tsl_cert_m12_p64 :
    caEvolve 64 (twoSpikeLastList 12 153) = twoSpikeLastList 12 25 := by native_decide

-- m=14, P=64: input=157, output=twoSpikeLast(14,29): spikes at 14 and 28
lemma caEvolve_tsl_cert_m14_p64 :
    caEvolve 64 (twoSpikeLastList 14 157) = twoSpikeLastList 14 29 := by native_decide

-- m=16, P=256: input=545, output=twoSpikeLast(16,33): spikes at 16 and 32
set_option maxHeartbeats 4000000000 in
lemma caEvolve_tsl_cert_m16_p256 :
    caEvolve 256 (twoSpikeLastList 16 545) = twoSpikeLastList 16 33 := by native_decide

-- m=20, P=256: input=553, output=twoSpikeLast(20,41): spikes at 20 and 40
set_option maxHeartbeats 4000000000 in
lemma caEvolve_tsl_cert_m20_p256 :
    caEvolve 256 (twoSpikeLastList 20 553) = twoSpikeLastList 20 41 := by native_decide

-- m=22, P=256: input=557, output=twoSpikeLast(22,45): spikes at 22 and 44
set_option maxHeartbeats 4000000000 in
lemma caEvolve_tsl_cert_m22_p256 :
    caEvolve 256 (twoSpikeLastList 22 557) = twoSpikeLastList 22 45 := by native_decide

/-!
## G-periodicity: rule30n_twoSpikeLast_period

The center value G(n', m) = caEvolve (n'+1) (twoSpikeLastList m (2*(n'+1)+1)) .getD 0 false
is periodic with the same period P_m as F(n', m).

Three key ingredients:
1. `caEvolve_twoSpike_eq_spikeAt`: for positions i where the right spike (at N-1) is strictly
   beyond i+2*P, caEvolve P of twoSpikeLastList agrees with caEvolve P of spikeAtList.
2. `twoSpikeLastList_drop_last_getD`: after dropping 2*(n+1) > m elements, position j of
   the dropped tape is decide(j = 2*P) — only the right spike at 2*P remains.
3. H=1: `caEvolve P (spikeAtList (2*P) (2*P+1)).getD 0 false = true`.
   Proof by induction: caStepList moves the last spike 2 positions left each step,
   reaching position 0 of a length-1 tape after P steps. (Certified below by native_decide
   for each specific P; general proof deferred.)
-/

/-- When the right spike (at N-1) lies strictly beyond position i+2*P,
    caEvolve P of twoSpikeLastList at i equals caEvolve P of spikeAtList at i. -/
lemma caEvolve_twoSpike_eq_spikeAt (P m N i : Nat)
    (h1 : i + 2 * P < N)
    (h2 : i + 2 * P + 1 < N) :  -- i.e., right spike N-1 > i+2*P
    (caEvolve P (twoSpikeLastList m N)).getD i false =
    (caEvolve P (spikeAtList m N)).getD i false := by
  rw [caEvolve_getD_shift P (twoSpikeLastList m N) i,
      caEvolve_getD_shift P (spikeAtList m N) i]
  apply caEvolve_agree P
  · rw [List.length_drop, twoSpikeLastList_length]; omega
  · rw [List.length_drop, spikeAtList_length]; omega
  · intro j hj
    have hij : i + j < N := by omega
    rw [twoSpikeLastList_drop_getD m N i j hij]
    rw [show ((spikeAtList m N).drop i).getD j false = (spikeAtList m N).getD (i + j) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
    rw [spikeAtList_getD m N (i + j) hij]
    -- Both sides are decide(i+j = m); need i+j ≠ N-1
    have hright : i + j ≠ N - 1 := by omega
    simp [hright]

/-- After dropping 2*(n+1) > m elements from the big two-spike tape, position j agrees
    with spikeAtList (2*P) (2*P+1) — only the right spike at 2*P remains. -/
lemma twoSpikeLastList_drop_last_getD (m P n : Nat) (hn : n ≥ m) (j : Nat) (hj : j ≤ 2 * P) :
    (List.drop (2 * (n + 1)) (twoSpikeLastList m (2 * ((n + 1) + P) + 1))).getD j false =
    decide (j = 2 * P) := by
  rw [twoSpikeLastList_drop_getD m (2 * ((n + 1) + P) + 1) (2 * (n + 1)) j (by omega)]
  rcases Decidable.em (j = 2 * P) with rfl | hne
  · -- j = 2*P: both sides evaluate to true
    have hlhs : 2*(n+1)+2*P = m ∨ 2*(n+1)+2*P = 2*((n+1)+P)+1-1 := Or.inr (by omega)
    rw [decide_eq_true_eq.mpr hlhs, decide_eq_true_eq.mpr (show 2*P = 2*P from rfl)]
  · -- j ≠ 2*P: both sides evaluate to false
    have hlhs : ¬(2*(n+1)+j = m ∨ 2*(n+1)+j = 2*((n+1)+P)+1-1) := by rintro (h|h) <;> omega
    rw [decide_eq_false_iff_not.mpr hlhs, decide_eq_false_iff_not.mpr hne]

/-!
## H=1 lemma: caEvolve_lastSpike_true

Proof sketch: by induction on P, caStepList maps spikeAtList(2*(k+1))(2*(k+1)+1) to
spikeAtList(2*k)(2*k+1). After P steps the spike reaches position 0 of a length-1 tape.
We certify specific instances by native_decide below.
-/

/-- At a non-last position (i ≠ N-1), twoSpikeLastList agrees with spikeAtList. -/
lemma twoSpikeLastList_eq_spikeAt_notLast (m N i : Nat) (hi : i < N) (hne : i ≠ N - 1) :
    (twoSpikeLastList m N).getD i false = (spikeAtList m N).getD i false := by
  rw [twoSpikeLastList_getD m N i hi, spikeAtList_getD m N i hi]
  simp [decide_eq_false_iff_not.mpr hne]

/-- G-periodicity: the two-spike-last center value is periodic with period P.

    Given:
    - hF_cert: caEvolve P (spikeAtList m (2*P+2*m+1)) = spikeAtList m (2*m+1)
    - hH: (caEvolve P (spikeAtList (2*P) (2*P+1))).getD 0 false = true  (H=1 cert)
    - hn: n ≥ m

    Proves: G(n, m) = G(n+P, m). -/
lemma rule30n_twoSpikeLast_period (m P : Nat)
    (hF_cert : caEvolve P (spikeAtList m (2 * P + 2 * m + 1)) = spikeAtList m (2 * m + 1))
    (hH : (caEvolve P (spikeAtList (2 * P) (2 * P + 1))).getD 0 false = true)
    (n : Nat) (hn : n ≥ m) :
    (caEvolve (n + 1) (twoSpikeLastList m (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + P) (twoSpikeLastList m (2 * ((n + 1) + P) + 1))).getD 0 false := by
  have rhs_len : 2 * (n + 1) < (caEvolve P (twoSpikeLastList m (2 * ((n + 1) + P) + 1))).length := by
    have hlen := caEvolve_length_le P (twoSpikeLastList m (2 * ((n + 1) + P) + 1))
                 (by rw [twoSpikeLastList_length]; omega)
    rw [twoSpikeLastList_length] at hlen; omega
  conv_rhs => rw [caEvolve_add (n + 1) P]
  apply caEvolve_agree (n + 1)
  · rw [twoSpikeLastList_length]; omega
  · exact rhs_len
  · intro i hi
    by_cases heq : i = 2 * (n + 1)
    · -- Case i = 2*(n+1): last spike of tape1 → true; RHS also true via H=1
      subst heq
      have lhs_true : (twoSpikeLastList m (2*(n+1)+1)).getD (2*(n+1)) false = true := by
        rw [twoSpikeLastList_getD m (2*(n+1)+1) (2*(n+1)) (by omega)]
        simp [decide_eq_true_iff.mpr (show 2*(n+1) = 2*(n+1)+1-1 from by omega)]
      have rhs_true : (caEvolve P (twoSpikeLastList m (2*((n+1)+P)+1))).getD (2*(n+1)) false = true := by
        rw [caEvolve_getD_shift P]
        calc (caEvolve P ((twoSpikeLastList m (2*((n+1)+P)+1)).drop (2*(n+1)))).getD 0 false
            = (caEvolve P (spikeAtList (2*P) (2*P+1))).getD 0 false := by
              apply caEvolve_agree P
              · rw [List.length_drop, twoSpikeLastList_length]; omega
              · rw [spikeAtList_length]; omega
              · intro j hj
                rw [twoSpikeLastList_drop_last_getD m P n hn j (by omega),
                    spikeAtList_getD (2*P) (2*P+1) j (by omega)]
          _ = true := hH
      rw [lhs_true, rhs_true]
    · -- Case i ≠ 2*(n+1), so i < 2*(n+1)
      have hlt : i < 2 * (n + 1) := by omega
      -- Right spike of tape2 (at 2*(n+1+P)) is outside causal cone of position i
      rw [caEvolve_twoSpike_eq_spikeAt P m (2 * ((n + 1) + P) + 1) i (by omega) (by omega)]
      -- Left side: i ≠ 2*(n+1) means i ≠ 2*(n+1)+1-1 (= last pos), so notLast applies
      rw [twoSpikeLastList_eq_spikeAt_notLast m (2*(n+1)+1) i (by omega) (by omega : i ≠ 2*(n+1)+1-1)]
      by_cases hle : i ≤ m
      · -- Sub-case i ≤ m: use F periodicity cert
        rw [spikeAtList_getD m (2*(n+1)+1) i (by omega),
            caEvolve_spikeAt_agree P m (2*((n+1)+P)+1) (2*P+2*m+1) i (by omega) (by omega),
            hF_cert, spikeAtList_getD m (2*m+1) i (by omega)]
      · -- Sub-case m < i < 2*(n+1): both sides false
        rw [spikeAtList_getD m (2*(n+1)+1) i (by omega)]
        have him : decide (i = m) = false := decide_eq_false_iff_not.mpr (by omega)
        rw [him, caEvolve_getD_shift P]
        exact (caEvolve_allFalse P _ (spikeAtList_drop_allFalse m (2*((n+1)+P)+1) i (by omega))).symm

/-- H=1 certs for each active period P. -/
lemma caEvolve_h1_p8 :
    (caEvolve 8 (spikeAtList 16 17)).getD 0 false = true := by native_decide
lemma caEvolve_h1_p16 :
    (caEvolve 16 (spikeAtList 32 33)).getD 0 false = true := by native_decide
lemma caEvolve_h1_p32 :
    (caEvolve 32 (spikeAtList 64 65)).getD 0 false = true := by native_decide
lemma caEvolve_h1_p64 :
    (caEvolve 64 (spikeAtList 128 129)).getD 0 false = true := by native_decide
set_option maxHeartbeats 4000000000 in
lemma caEvolve_h1_p256 :
    (caEvolve 256 (spikeAtList 512 513)).getD 0 false = true := by native_decide

/-- Specific G-period lemmas for each active m. -/

lemma rule30n_twoSpikeLast4_period8 (n : Nat) (hn : n ≥ 4) :
    (caEvolve (n + 1) (twoSpikeLastList 4 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 8) (twoSpikeLastList 4 (2 * ((n + 1) + 8) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 4 8 caEvolve_cert_m4_p8 caEvolve_h1_p8 n hn

lemma rule30n_twoSpikeLast6_period16 (n : Nat) (hn : n ≥ 6) :
    (caEvolve (n + 1) (twoSpikeLastList 6 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 16) (twoSpikeLastList 6 (2 * ((n + 1) + 16) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 6 16 caEvolve_cert_m6_p16 caEvolve_h1_p16 n hn

lemma rule30n_twoSpikeLast8_period32 (n : Nat) (hn : n ≥ 8) :
    (caEvolve (n + 1) (twoSpikeLastList 8 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 32) (twoSpikeLastList 8 (2 * ((n + 1) + 32) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 8 32 caEvolve_cert_m8_p32 caEvolve_h1_p32 n hn

lemma rule30n_twoSpikeLast10_period64 (n : Nat) (hn : n ≥ 10) :
    (caEvolve (n + 1) (twoSpikeLastList 10 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 64) (twoSpikeLastList 10 (2 * ((n + 1) + 64) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 10 64 caEvolve_cert_m10_p64 caEvolve_h1_p64 n hn

lemma rule30n_twoSpikeLast12_period64 (n : Nat) (hn : n ≥ 12) :
    (caEvolve (n + 1) (twoSpikeLastList 12 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 64) (twoSpikeLastList 12 (2 * ((n + 1) + 64) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 12 64 caEvolve_cert_m12_p64 caEvolve_h1_p64 n hn

lemma rule30n_twoSpikeLast14_period64 (n : Nat) (hn : n ≥ 14) :
    (caEvolve (n + 1) (twoSpikeLastList 14 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 64) (twoSpikeLastList 14 (2 * ((n + 1) + 64) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 14 64 caEvolve_cert_m14_p64 caEvolve_h1_p64 n hn

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast16_period256 (n : Nat) (hn : n ≥ 16) :
    (caEvolve (n + 1) (twoSpikeLastList 16 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 256) (twoSpikeLastList 16 (2 * ((n + 1) + 256) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 16 256 caEvolve_cert_m16_p256 caEvolve_h1_p256 n hn

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast20_period256 (n : Nat) (hn : n ≥ 20) :
    (caEvolve (n + 1) (twoSpikeLastList 20 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 256) (twoSpikeLastList 20 (2 * ((n + 1) + 256) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 20 256 caEvolve_cert_m20_p256 caEvolve_h1_p256 n hn

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast22_period256 (n : Nat) (hn : n ≥ 22) :
    (caEvolve (n + 1) (twoSpikeLastList 22 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 256) (twoSpikeLastList 22 (2 * ((n + 1) + 256) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 22 256 caEvolve_cert_m22_p256 caEvolve_h1_p256 n hn

set_option maxHeartbeats 4000000000 in
lemma caEvolve_h1_p512 :
    (caEvolve 512 (spikeAtList 1024 1025)).getD 0 false = true := by native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolve_h1_p1024 :
    (caEvolve 1024 (spikeAtList 2048 2049)).getD 0 false = true := by native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolve_h1_p2048 :
    (caEvolve 2048 (spikeAtList 4096 4097)).getD 0 false = true := by native_decide

set_option maxHeartbeats 4000000000 in
lemma caEvolve_h1_p4096 :
    (caEvolve 4096 (spikeAtList 8192 8193)).getD 0 false = true := by native_decide

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast24_period512 (n : Nat) (hn : n ≥ 24) :
    (caEvolve (n + 1) (twoSpikeLastList 24 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 512) (twoSpikeLastList 24 (2 * ((n + 1) + 512) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 24 512 caEvolve_cert_m24_p512 caEvolve_h1_p512 n hn

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast26_period1024 (n : Nat) (hn : n ≥ 26) :
    (caEvolve (n + 1) (twoSpikeLastList 26 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 1024) (twoSpikeLastList 26 (2 * ((n + 1) + 1024) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 26 1024 caEvolve_cert_m26_p1024 caEvolve_h1_p1024 n hn

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast28_period2048 (n : Nat) (hn : n ≥ 28) :
    (caEvolve (n + 1) (twoSpikeLastList 28 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 2048) (twoSpikeLastList 28 (2 * ((n + 1) + 2048) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 28 2048 caEvolve_cert_m28_p2048 caEvolve_h1_p2048 n hn

set_option maxHeartbeats 4000000000 in
lemma rule30n_twoSpikeLast30_period4096 (n : Nat) (hn : n ≥ 30) :
    (caEvolve (n + 1) (twoSpikeLastList 30 (2 * (n + 1) + 1))).getD 0 false =
    (caEvolve ((n + 1) + 4096) (twoSpikeLastList 30 (2 * ((n + 1) + 4096) + 1))).getD 0 false :=
  rule30n_twoSpikeLast_period 30 4096 caEvolve_cert_m30_p4096 caEvolve_h1_p4096 n hn

/-!
## Pending: m=34,36,38 (periods 8192, 16384, 32768)

Lean 4.29 native_decide crashes (SIGABRT exit 134) during native binary
CODE GENERATION for lists of size ≥ 16K elements, specifically at the
`decl_1_1` step for `caEvolve_cert_m34_p8192`. This is a Lean tooling
limitation, not a mathematical obstruction.

Verified in Python:
- m=34, P=8192: caEvolve 8192 (spikeAtList 34 16453) = spikeAtList 34 69 ✓
- m=36, P=16384: caEvolve 16384 (spikeAtList 36 32841) = spikeAtList 36 73 ✓ (expected)
- m=38, P=32768: caEvolve 32768 (spikeAtList 38 65613) = spikeAtList 38 77 ✓ (expected)
- H=1 certs: all True for P=8192,16384,32768 ✓

Workaround options:
1. Staged native_decide (4 stages of 2048 steps each) — reduces per-stage list size
2. Tail-recursive caStepList + proof of equivalence with accumulator
3. Lean 4.30+ (if the code generation limit is raised)

-- m=34, P=8192: (staged approach template, pending implementation)
-- def m34_s1 : List Bool := List.ofFn (fun k : Fin 12357 => decide (k.val = 1 || k.val = 3 || k.val = 5 || k.val = 34))
-- def m34_s2 : List Bool := List.ofFn (fun k : Fin 8261 => decide (k.val = 0 || k.val = 34))
-- def m34_s3 : List Bool := List.ofFn (fun k : Fin 4165 => decide (k.val = 0 || k.val = 1 || k.val = 3 || k.val = 5 || k.val = 34))
-- lemma caEvolve_cert_m34_p8192 : caEvolve 8192 (spikeAtList 34 16453) = spikeAtList 34 69 := ...
-- lemma caEvolve_h1_p8192 : (caEvolve 8192 (spikeAtList 16384 16385)).getD 0 false = true := ...
-- lemma rule30n_twoSpikeLast34_period8192 : ... := rule30n_twoSpikeLast_period 34 8192 ...
-- (analogously for m=36,38)
-/
