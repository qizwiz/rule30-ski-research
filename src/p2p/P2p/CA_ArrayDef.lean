/-
CA_ArrayDef.lean — Array Bool CA definitions (imported by CA_Array.lean)
============================================================================

This file ONLY contains definitions and equivalence lemmas.
It must be imported by CA_Array.lean so that caEvolveArr, spikeArr, etc.
are pre-compiled before native_decide calls in CA_Array.lean — enabling
the native evaluator to use compiled C code instead of the kernel reducer.

Split rationale: native_decide in Lean 4 uses pre-compiled (imported) code.
If caEvolveArr is defined in the same file as native_decide, the evaluator
falls back to the kernel reducer (~50× slower).
-/

import P2p.CausalConeLemmas

/-
================================================================================
SECTION 1: ARRAY BOOL DEFINITIONS
================================================================================
-/

/-- Array-based single CA step: rule30 applied to each triple, shrinks by 2 -/
def caStepArr (a : Array Bool) : Array Bool :=
  if h : 3 ≤ a.size then
    Array.ofFn (fun i : Fin (a.size - 2) =>
      rule30Local (a[i.val]'(by omega))
                  (a[i.val + 1]'(by omega))
                  (a[i.val + 2]'(by omega)))
  else #[]

/-- Array-based CA evolution for n steps -/
def caEvolveArr : Nat → Array Bool → Array Bool
  | 0,     a => a
  | t + 1, a => caEvolveArr t (caStepArr a)

/-- Array Bool spike: true only at position m in [0, N) -/
def spikeArr (m N : Nat) : Array Bool :=
  Array.ofFn (fun k : Fin N => decide (k.val = m))

/-- Array Bool two-spike-last: true at position m and at position N-1 -/
def twoSpikeLastArr (m N : Nat) : Array Bool :=
  Array.ofFn (fun k : Fin N => decide (k.val = m || k.val = N - 1))

/-- Array Bool two-spike at arbitrary positions p and q (not necessarily last) -/
def twoSpikeArr (p q N : Nat) : Array Bool :=
  Array.ofFn (fun k : Fin N => decide (k.val = p ∨ k.val = q))

/-
================================================================================
SECTION 2: HELPER LEMMAS FOR EQUIVALENCE
================================================================================
-/

/-- `caStepList` getD at in-bounds index i -/
lemma caStepList_getD_val (l : List Bool) (i : Nat) (hi : i + 2 < l.length) :
    (caStepList l).getD i false =
    rule30Local (l.getD i false) (l.getD (i + 1) false) (l.getD (i + 2) false) := by
  induction i generalizing l with
  | zero =>
    match l with
    | [] => simp at hi
    | [_] => simp at hi
    | [_, _] => simp at hi
    | p :: q :: r :: _ => simp [caStepList, List.getD]
  | succ n ih =>
    match l with
    | [] => simp at hi
    | [_] => simp at hi
    | [_, _] => simp at hi; omega
    | p :: q :: r :: rest =>
      simp only [caStepList, List.getD_cons_succ]
      apply ih
      have hlen : (p :: q :: r :: rest).length = (q :: r :: rest).length + 1 := rfl
      omega

/-- Array.getD equals List.getD on toList -/
lemma Array.getD_eq_toList_getD (a : Array Bool) (i : Nat) :
    a.getD i false = a.toList.getD i false := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- getD of List.ofFn: in-bounds gives function value, out-of-bounds gives default -/
private lemma List.getD_ofFn_eq {n : Nat} (f : Fin n → Bool) (i : Nat) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

set_option maxHeartbeats 800000 in
/-- caStepArr.toList = caStepList on the same data -/
theorem caStepArr_toList_eq (a : Array Bool) :
    (caStepArr a).toList = caStepList a.toList := by
  by_cases h : 3 ≤ a.size
  · have hal : a.toList.length = a.size := Array.length_toList
    have hstep : (caStepList a.toList).length = a.size - 2 := by
      have := caStep_length a.toList (by omega); omega
    simp only [caStepArr, h, dif_pos, Array.toList_ofFn]
    apply List.ext_getElem
    · simp only [List.length_ofFn]; omega
    · intro i hi1 hi2
      simp only [List.length_ofFn] at hi1
      conv_lhs => rw [List.getElem_eq_getD false, List.getD_ofFn_eq, dif_pos hi1]
      conv_rhs => rw [List.getElem_eq_getD false, caStepList_getD_val a.toList i (by omega)]
      simp only [Array.getElem_eq_getD false, Array.getD_eq_toList_getD]
  · push_neg at h
    simp only [caStepArr, show ¬(3 ≤ a.size) from by omega, dif_neg, not_false_eq_true,
               Array.toList_empty]
    have hl : a.toList.length < 3 := by
      have hal : a.toList.length = a.size := Array.length_toList; omega
    match a.toList, hl with
    | [], _ => simp [caStepList]
    | [_], _ => simp [caStepList]
    | [_, _], _ => simp [caStepList]
    | _ :: _ :: _ :: _, h => simp [List.length] at h; omega

/-- Main equivalence: caEvolveArr on toList = caEvolve on same list -/
theorem caEvolveArr_toList_eq (n : Nat) (a : Array Bool) :
    (caEvolveArr n a).toList = caEvolve n a.toList := by
  induction n generalizing a with
  | zero => simp [caEvolveArr, caEvolve]
  | succ n ih =>
    simp only [caEvolveArr, caEvolve]
    rw [ih, caStepArr_toList_eq]

/-- spikeArr.toList = spikeAtList -/
theorem spikeArr_toList_eq (m N : Nat) : (spikeArr m N).toList = spikeAtList m N := by
  simp [spikeArr, spikeAtList, Array.toList_ofFn]

/-- twoSpikeLastArr.toList = twoSpikeLastList -/
theorem twoSpikeLastArr_toList_eq (m N : Nat) :
    (twoSpikeLastArr m N).toList = twoSpikeLastList m N := by
  simp [twoSpikeLastArr, twoSpikeLastList, Array.toList_ofFn]

/-- twoSpikeArr.toList = twoSpikeList -/
theorem twoSpikeArr_toList_eq (p q N : Nat) :
    (twoSpikeArr p q N).toList = twoSpikeList p q N := by
  simp [twoSpikeArr, twoSpikeList, Array.toList_ofFn]
