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

/-
================================================================================
SECTION 3: INCREMENTAL CENTER-OUTPUT SEQUENCES
================================================================================

For residue proofs, instead of scanning ∀ j : Fin P with separate CA evolutions
(cost O(P × T²)), we precompute the center-output sequence incrementally
(cost O(T²)) using a single evolving tape.

Key idea:
  spikeAtCenterSeq m T_max : Array Bool
  result[t] = (caEvolveArr (t+1) (spikeArr m (2*(t+1)+1))).getD 0 false

Computed by evolving spikeArr m (2*T_max+1) step-by-step and recording tape[0]
at each step. Total cost: O(T_max²) instead of O(P × T²).

The `spikeAtCenterSeqSpec` definition (Array.ofFn) is used for proofs;
the `spikeAtCenterSeq` recursive definition is used for native_decide performance.
In native_decide, `spikeAtCenterSeq m T_max` is computed as a shared thunk —
the incremental loop runs once and the result is cached for all j lookups.
================================================================================
-/

/-- Recursive helper: evolves tape for `n` more steps, appending tape[0] to result. -/
private def spikeAtCenterSeqAux : Nat → Array Bool → Array Bool → Array Bool
  | 0,     _tape, result => result
  | n + 1, tape,  result =>
    let tape' := caStepArr tape
    spikeAtCenterSeqAux n tape' (result.push (tape'.getD 0 false))

/-- Incremental center-output sequence for spike_m evolution.
    result[t] = center output after t+1 steps from spike at m in tape 2*(t+1)+1.
    Computed in O(T_max²) by a single tape evolution (vs O(P × T²) for per-j scan). -/
def spikeAtCenterSeq (m T_max : Nat) : Array Bool :=
  spikeAtCenterSeqAux T_max (spikeArr m (2 * T_max + 1)) #[]

/-- Recursive helper: evolves twoSpikeLastArr tape for `n` more steps. -/
private def twoSpikeLastCenterSeqAux : Nat → Array Bool → Array Bool → Array Bool
  | 0,     _tape, result => result
  | n + 1, tape,  result =>
    let tape' := caStepArr tape
    twoSpikeLastCenterSeqAux n tape' (result.push (tape'.getD 0 false))

/-- Incremental center-output sequence for twoSpikeLast_m evolution.
    result[t] = center output after t+1 steps from twoSpikeLastArr m (2*(T_max)+1).
    NOTE: this approximates G_m(t) for t ≤ T_max, but the last spike is fixed at
    position 2*T_max (not 2*(t+1)) — use only for COMBINED residue checks where
    native_decide verifies the exact condition directly. -/
def twoSpikeLastCenterSeq (m T_max : Nat) : Array Bool :=
  twoSpikeLastCenterSeqAux T_max (twoSpikeLastArr m (2 * T_max + 1)) #[]

/-- caEvolveArr (n+1) equals caStepArr applied after caEvolveArr n.
    Proof by induction: matches the loop order in spikeAtCenterSeqAux. -/
private lemma caEvolveArr_succ_comm (n : Nat) (init : Array Bool) :
    caEvolveArr (n + 1) init = caStepArr (caEvolveArr n init) := by
  induction n generalizing init with
  | zero => simp [caEvolveArr]
  | succ k ih =>
    simp only [caEvolveArr]
    exact ih (caStepArr init)

/-- Loop invariant for spikeAtCenterSeqAux (strong form):
    tape = caEvolveArr acc init (exact array equality),
    result has size acc, result[t] = (caEvolveArr (t+1) init).getD 0 false for t < acc.
    Conclusion: after n more steps, same properties hold for acc+n. -/
private lemma spikeAtCenterSeqAux_inv (n acc : Nat) (init tape : Array Bool) (result : Array Bool)
    (hacc : result.size = acc)
    (htape : tape = caEvolveArr acc init)
    (hresult : ∀ t, t < acc → result.getD t false = (caEvolveArr (t + 1) init).getD 0 false) :
    (spikeAtCenterSeqAux n tape result).size = acc + n ∧
    ∀ t, t < acc + n →
      (spikeAtCenterSeqAux n tape result).getD t false =
      (caEvolveArr (t + 1) init).getD 0 false := by
  induction n generalizing acc tape result with
  | zero => exact ⟨hacc, hresult⟩
  | succ n ih =>
    simp only [spikeAtCenterSeqAux]
    set tape' := caStepArr tape with htape'_def
    -- tape' = caEvolveArr (acc+1) init  (exact array equality)
    have htape' : tape' = caEvolveArr (acc + 1) init := by
      rw [htape'_def, htape, caEvolveArr_succ_comm]
    -- New result size
    have hresult'_size : (result.push (tape'.getD 0 false)).size = acc + 1 := by
      simp [Array.size_push, hacc]
    -- Helper: push preserves old entries (t < result.size = acc)
    have push_old : ∀ t, t < acc →
        (result.push (tape'.getD 0 false)).getD t false = result.getD t false := fun t hlt => by
      have hlt' : t < result.size := hacc ▸ hlt
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hlt',
                 Array.getElem?_eq_getElem hlt', Option.getD_some]
    -- Helper: push gives new entry at position acc
    have push_new : (result.push (tape'.getD 0 false)).getD acc false = tape'.getD 0 false := by
      rw [show acc = result.size from hacc.symm]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]
    -- New result correctness
    have hresult' : ∀ t, t < acc + 1 →
        (result.push (tape'.getD 0 false)).getD t false = (caEvolveArr (t+1) init).getD 0 false := by
      intro t ht
      by_cases hlt : t < acc
      · rw [push_old t hlt]; exact hresult t hlt
      · have heq : t = acc := by omega
        subst heq
        rw [push_new, htape']
    obtain ⟨hsize, hval⟩ := ih (acc + 1) tape' (result.push (tape'.getD 0 false))
      hresult'_size htape' hresult'
    exact ⟨by omega, fun t ht => hval t (by omega)⟩

/-
================================================================================
SECTION 4: G CENTER-OUTPUT SEQUENCES (recurrence-based)
================================================================================

gCenterSeq m T_max precomputes G_m(t+1) for t < T_max using the recurrence
  G_0(t+1) = false (all time)
  G_{m+2}(t+1) = rule30Local(F_{m+2}(t), F_{m+1}(t), G_m(t))

where F_k(t) = spikeAtCenterSeq k T_max .getD t  (= F_k(t+1) by spikeAtCenterSeq_correct
but we reindex: G[t] = G_m(t+1), F[t] = F_m(t+1), so recurrence becomes
  G[t] = rule30Local(F_{m+2}[t-1], F_{m+1}[t-1], G_m[t-1])  for t ≥ 1
  G[0] = G_{m+2}(1) = true (verified for all m).
-/

/-- Precomputed G center-output sequence via recurrence.
    (gCenterSeq m T_max).getD t = G_m(t+1) for t < T_max.
    G_0(t+1) = false.
    G_{m+2}(t+1) = rule30Local(F_{m+2}(t), F_{m+1}(t), G_m(t)) for t ≥ 0. -/
def gCenterSeq : Nat → Nat → Array Bool
  | 0,     T_max => Array.replicate T_max false
  | 1,     T_max => Array.replicate T_max false  -- G_1 not used for even m (placeholder)
  | m + 2, T_max =>
    let seqFm  := spikeAtCenterSeq (m + 2) T_max
    let seqFm1 := spikeAtCenterSeq (m + 1) T_max
    let seqGm  := gCenterSeq m T_max
    Array.ofFn fun t : Fin T_max =>
      if t.val = 0 then true
      else rule30Local
        (seqFm.getD  (t.val - 1) false)
        (seqFm1.getD (t.val - 1) false)
        (seqGm.getD  (t.val - 1) false)

/-- gCenterSeq 0 is all-false. -/
private lemma gCenterSeq_zero (T_max t : Nat) (ht : t < T_max) :
    (gCenterSeq 0 T_max).getD t false = false := by
  simp [gCenterSeq, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, ht]

/-- gCenterSeq (m+2) at t=0 is true. -/
private lemma gCenterSeq_succ2_zero (m T_max : Nat) (hT : 0 < T_max) :
    (gCenterSeq (m + 2) T_max).getD 0 false = true := by
  simp [gCenterSeq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hT]

/-- gCenterSeq (m+2) at t+1 unfolds to the recurrence. -/
private lemma gCenterSeq_succ2_succ (m T_max t : Nat) (ht : t + 1 < T_max) :
    (gCenterSeq (m + 2) T_max).getD (t + 1) false =
    rule30Local
      ((spikeAtCenterSeq (m + 2) T_max).getD t false)
      ((spikeAtCenterSeq (m + 1) T_max).getD t false)
      ((gCenterSeq m T_max).getD t false) := by
  simp only [gCenterSeq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
             show t + 1 < T_max from ht]
  simp [show (t + 1) ≠ 0 from Nat.succ_ne_zero t]

/-- Correctness of spikeAtCenterSeq:
    element t equals F_m(t+1) = (caEvolveArr (t+1) (spikeArr m (2*(t+1)+1))).getD 0 false. -/
theorem spikeAtCenterSeq_correct (m T_max t : Nat) (ht : t < T_max) :
    (spikeAtCenterSeq m T_max).getD t false =
    (caEvolveArr (t + 1) (spikeArr m (2 * (t + 1) + 1))).getD 0 false := by
  simp only [spikeAtCenterSeq]
  obtain ⟨_, hval⟩ := spikeAtCenterSeqAux_inv T_max 0 (spikeArr m (2 * T_max + 1))
    (spikeArr m (2 * T_max + 1)) #[] (by simp) (by simp [caEvolveArr]) (by intro t ht; omega)
  rw [hval t (by omega)]
  -- Goal: (caEvolveArr (t+1) (spikeArr m (2*T_max+1))).getD 0 false =
  --       (caEvolveArr (t+1) (spikeArr m (2*(t+1)+1))).getD 0 false
  -- Convert both sides to caEvolve/List form, then apply caEvolve_spikeAt_agree
  simp only [Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq]
  exact caEvolve_spikeAt_agree (t + 1) m (2 * T_max + 1) (2 * (t + 1) + 1) 0
    (by omega) (by omega)

/-- Correctness of gCenterSeq for even m:
    element t equals G_m(t+1) = (caEvolveArr (t+1) (twoSpikeLastArr m (2*(t+1)+1))).getD 0.
    Proved by induction on m (stepping by 2), using twoSpikeLastList_center_recurrence. -/
theorem gCenterSeq_correct (m T_max t : Nat) (hm : m % 2 = 0) (ht : t < T_max) :
    (gCenterSeq m T_max).getD t false =
    (caEvolveArr (t + 1) (twoSpikeLastArr m (2 * (t + 1) + 1))).getD 0 false := by
  -- Prove the Array-level statement by reducing to List form
  -- Core lemma: for all k T t, t < T → (gCenterSeq (2*k) T).getD t = G_{2k}(t+1)
  suffices h : ∀ k T t, t < T →
      (gCenterSeq (2 * k) T).getD t false =
      (caEvolve (t + 1) (twoSpikeLastList (2 * k) (2 * (t + 1) + 1))).getD 0 false by
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    have := h k T_max t ht
    simp only [Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq]
    rw [Array.getD_eq_toList_getD] at this
    exact this
  intro k
  induction k with
  | zero =>
    intro T t ht'
    simp only [Nat.zero_mul, Nat.mul_zero]
    rw [gCenterSeq_zero T t ht']
    exact (twoSpikeLastList0_center_false t).symm
  | succ k ih =>
    intro T t ht'
    -- m = 2*(k+1) = 2*k+2
    show (gCenterSeq (2 * (k + 1)) T).getD t false =
         (caEvolve (t + 1) (twoSpikeLastList (2 * (k + 1)) (2 * (t + 1) + 1))).getD 0 false
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega]
    -- Use recurrence on G side
    rw [twoSpikeLastList_center_recurrence (2 * k) t]
    -- Two cases: t=0 or t=t'+1
    cases t with
    | zero =>
      -- t=0: gCenterSeq (2*k+2) T .getD 0 = true
      --      rule30Local(F_{2k+2}(0), F_{2k+1}(0), G_{2k}(0))
      -- G_{2k}(0) = caEvolve 0 (twoSpikeLastList (2*k) 1) .getD 0 = twoSpikeLastList (2*k) 1 .getD 0
      --           = decide(0 = 2*k ∨ 0 = 0) = true (since 0=0)
      -- F_{2k+2}(0) = spikeAtList (2*k+2) 1 .getD 0 = decide(0 = 2*k+2) = false (k≥0)
      -- F_{2k+1}(0) = spikeAtList (2*k+1) 1 .getD 0 = decide(0 = 2*k+1) = false
      -- rule30Local(false, false, true) = false XOR (false||true) = true
      -- gCenterSeq (2*k+2) T .getD 0 = true (by gCenterSeq_succ2_zero)
      rw [gCenterSeq_succ2_zero (2 * k) T ht']
      simp only [caEvolve, twoSpikeLastList_getD (2 * k) 1 0 (by omega),
                 spikeAtList_getD (2 * k + 2) 1 0 (by omega),
                 spikeAtList_getD (2 * k + 1) 1 0 (by omega)]
      simp [rule30Local, show ¬(0 = 2 * k + 2) from by omega,
            show ¬(0 = 2 * k + 1) from by omega,
            show (0 = 2 * k ∨ 0 = 1 - 1) from Or.inr (by omega)]
    | succ t' =>
      -- t = t'+1: use gCenterSeq_succ2_succ + spikeAtCenterSeq_correct + ih
      rw [gCenterSeq_succ2_succ (2 * k) T t' (by omega)]
      congr 1
      · -- F_{2k+2}(t'+1) connection
        rw [spikeAtCenterSeq_correct (2 * k + 2) T t' (by omega)]
        simp only [Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq]
      · -- F_{2k+1}(t'+1) connection
        rw [spikeAtCenterSeq_correct (2 * k + 1) T t' (by omega)]
        simp only [Array.getD_eq_toList_getD, caEvolveArr_toList_eq, spikeArr_toList_eq]
      · -- G_{2k}(t'+1) connection = inductive hypothesis
        exact ih T t' (by omega)

/-
================================================================================
SECTION 5: GENERIC RESIDUE CHECKER (for SubcaseB firing position classification)
================================================================================

checkResiduesBool m period validSet seqF seqG:
  Returns true iff for all j < period, if seqF[j+m]=false and seqG[j+m]=true,
  then j+m ∈ validSet.

Defined here (in an imported file) so that native_decide in the per-m residue files
uses pre-compiled native code, not the kernel reducer.
-/

/-- Generic Bool check for SubcaseB residue classification.
    Returns true iff for all j < period, SubcaseB firing at position j+m
    implies j+m ∈ validSet. -/
def checkResiduesBool (m period : Nat) (validSet : List Nat) (seqF seqG : Array Bool) : Bool :=
  (Array.range period).all fun j =>
    let fval := seqF.getD (j + m) false
    let gval := seqG.getD (j + m) false
    if fval == false && gval == true then
      validSet.any fun v => j + m == v
    else
      true

/-- Bridge: if checkResiduesBool returns true, then for all j < period,
    SubcaseB at position j+m implies j+m ∈ validSet. -/
lemma checkResiduesBool_spec (m period : Nat) (validSet : List Nat) (seqF seqG : Array Bool)
    (h : checkResiduesBool m period validSet seqF seqG = true) :
    ∀ j : Fin period,
    seqF.getD (j.val + m) false = false →
    seqG.getD (j.val + m) false = true →
    j.val + m ∈ validSet := by
  intro ⟨j, hj⟩ hF hG
  rw [checkResiduesBool, Array.all_eq_true_iff_forall_mem] at h
  have hmem : j ∈ Array.range period := Array.mem_range.mpr hj
  have hcheck := h j hmem
  simp only [hF, hG, beq_self_eq_true, Bool.and_self, ite_true,
             List.any_eq_true, beq_iff_eq] at hcheck
  obtain ⟨v, hv_mem, hv_eq⟩ := hcheck
  exact hv_eq ▸ hv_mem

/-
================================================================================
SECTION 6: G2m CENTER-OUTPUT SEQUENCE (spikes at positions 2 AND m)
================================================================================

G2mCenterSeq m T_max : precomputes G_{2,m}(t+1) for t = 0 .. T_max-1.
Here G_{2,m}(T) = (caEvolveArr T (twoSpikeArr 2 m (2*T+1))).getD 0 false,
i.e., the center output after T steps starting from a tape with spikes at
positions 2 and m.

Computed by a single incremental tape evolution (O(T_max²)) starting from
twoSpikeArr 2 m (2*T_max+1), recording tape[0] after each step.

IMPORTANT: result[t] = G_{2,m}(t+1), so G_{2,m}(T) is at index T-1.
================================================================================
-/

/-- Recursive helper: evolves tape for `n` more steps, appending tape[0] to result. -/
private def G2mCenterSeqAux : Nat → Array Bool → Array Bool → Array Bool
  | 0,     _tape, result => result
  | n + 1, tape,  result =>
    let tape' := caStepArr tape
    G2mCenterSeqAux n tape' (result.push (tape'.getD 0 false))

/-- Incremental center-output sequence for two-spike configuration (spikes at 2 and m).
    result[t] = G_{2,m}(t+1) = center after t+1 steps from twoSpikeArr 2 m (2*T_max+1).
    Computed in O(T_max²) by a single tape evolution.

    Note: Uses causal-cone independence — the exact tape size doesn't matter as long as
    both spikes (at 2 and m) are within the tape, i.e., T_max > m/2. -/
def G2mCenterSeq (m T_max : Nat) : Array Bool :=
  G2mCenterSeqAux T_max (twoSpikeArr 2 m (2 * T_max + 1)) #[]

/-- Loop invariant for G2mCenterSeqAux (strong form):
    tape = caEvolveArr acc init, result[t] = (caEvolveArr (t+1) init).getD 0 false for t < acc.
    Mirrors spikeAtCenterSeqAux_inv. -/
private lemma G2mCenterSeqAux_inv (n acc : Nat) (init tape : Array Bool) (result : Array Bool)
    (hacc : result.size = acc)
    (htape : tape = caEvolveArr acc init)
    (hresult : ∀ t, t < acc → result.getD t false = (caEvolveArr (t + 1) init).getD 0 false) :
    (G2mCenterSeqAux n tape result).size = acc + n ∧
    ∀ t, t < acc + n →
      (G2mCenterSeqAux n tape result).getD t false =
      (caEvolveArr (t + 1) init).getD 0 false := by
  induction n generalizing acc tape result with
  | zero => exact ⟨hacc, hresult⟩
  | succ n ih =>
    simp only [G2mCenterSeqAux]
    set tape' := caStepArr tape with htape'_def
    have htape' : tape' = caEvolveArr (acc + 1) init := by
      rw [htape'_def, htape, caEvolveArr_succ_comm]
    have hresult'_size : (result.push (tape'.getD 0 false)).size = acc + 1 := by
      simp [Array.size_push, hacc]
    have push_old : ∀ t, t < acc →
        (result.push (tape'.getD 0 false)).getD t false = result.getD t false := fun t hlt => by
      have hlt' : t < result.size := hacc ▸ hlt
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hlt',
                 Array.getElem?_eq_getElem hlt', Option.getD_some]
    have push_new : (result.push (tape'.getD 0 false)).getD acc false = tape'.getD 0 false := by
      rw [show acc = result.size from hacc.symm]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_size, Option.getD_some]
    have hresult' : ∀ t, t < acc + 1 →
        (result.push (tape'.getD 0 false)).getD t false = (caEvolveArr (t+1) init).getD 0 false := by
      intro t ht
      by_cases hlt : t < acc
      · rw [push_old t hlt]; exact hresult t hlt
      · have heq : t = acc := by omega
        subst heq
        rw [push_new, htape']
    obtain ⟨hsize, hval⟩ := ih (acc + 1) tape' (result.push (tape'.getD 0 false))
      hresult'_size htape' hresult'
    exact ⟨by omega, fun t ht => hval t (by omega)⟩

/-- Correctness of G2mCenterSeq:
    element t equals G_{2,m}(t+1) = (caEvolveArr (t+1) (twoSpikeArr 2 m (2*(t+1)+1))).getD 0 false.
    Mirrors spikeAtCenterSeq_correct. -/
theorem G2mCenterSeq_correct (m T_max t : Nat) (ht : t < T_max) :
    (G2mCenterSeq m T_max).getD t false =
    (caEvolveArr (t + 1) (twoSpikeArr 2 m (2 * (t + 1) + 1))).getD 0 false := by
  simp only [G2mCenterSeq]
  obtain ⟨_, hval⟩ := G2mCenterSeqAux_inv T_max 0 (twoSpikeArr 2 m (2 * T_max + 1))
    (twoSpikeArr 2 m (2 * T_max + 1)) #[] (by simp) (by simp [caEvolveArr]) (by intro t ht; omega)
  rw [hval t (by omega)]
  -- Goal: (caEvolveArr (t+1) (twoSpikeArr 2 m (2*T_max+1))).getD 0 false =
  --       (caEvolveArr (t+1) (twoSpikeArr 2 m (2*(t+1)+1))).getD 0 false
  -- Convert to List form and use caEvolve_agree (causal cone)
  simp only [Array.getD_eq_toList_getD, caEvolveArr_toList_eq, twoSpikeArr_toList_eq]
  apply caEvolve_agree (t + 1)
  · rw [twoSpikeList_length]; omega
  · rw [twoSpikeList_length]; omega
  · intro i hi
    -- twoSpikeList 2 m N1 and twoSpikeList 2 m N2 agree at position i (when i < both lengths)
    -- Both give decide(i=2 ∨ i=m) at all in-bounds positions
    have hN1 : i < 2 * T_max + 1 := by omega
    have hN2 : i < 2 * (t + 1) + 1 := by omega
    rw [twoSpikeList_getD 2 m (2 * T_max + 1) i hN1,
        twoSpikeList_getD 2 m (2 * (t + 1) + 1) i hN2]

/-
================================================================================
SECTION 7: UINT64 BIT-PACKED TAPE (fast path for large-T native_decide)
================================================================================

Direct translation of stream_G2m_all.c's step() function into Lean 4.
Uses Array UInt64 where bit (64*w + b) of the tape = cell at position 64*w+b.

Key operation: L XOR (cur OR R)  where L/C/R are left/center/right neighbors.
Left carry (lc): MSB of the previous word becomes LSB of L in the current word.
Right carry (rc): LSB of the next word becomes MSB of R in the current word.

This matches C exactly:
  L = (cur << 1) | lc;  lc = cur >> 63;
  R = (cur >> 1) | ((right & 1) ? (1<<63) : 0);
  out[w] = L ^ (cur | R);

No allocation per step (imperative loop with Array.set!), GC pressure ~ O(T/64).
Expected speedup: ~100x over caStepArr for large T (fewer allocations + SIMD-friendly).
================================================================================
-/

/-- Set bit at position `pos` in a UInt64 tape. -/
def setbitU64 (tape : Array UInt64) (pos : Nat) : Array UInt64 :=
  let w := pos / 64
  let b := (pos % 64).toUInt64
  if w < tape.size then
    tape.set! w ((tape[w]!) ||| ((1 : UInt64) <<< b))
  else
    tape

/-- Get bit at position `pos` from a UInt64 tape. Returns false if out of bounds. -/
def getbitU64 (tape : Array UInt64) (pos : Nat) : Bool :=
  if h : pos / 64 < tape.size then
    ((tape[pos / 64]'h) >>> (pos % 64).toUInt64) &&& 1 = 1
  else
    false

/-- Single Rule 30 step on UInt64-packed tape, matching C's step() exactly.
    Uses a mutable left-carry (lc) threaded through words left to right.
    Boundary: positions outside [0, 64*tape.size) treated as 0. -/
def caStepU64 (tape : Array UInt64) : Array UInt64 :=
  let n := tape.size
  Id.run do
    let mut out : Array UInt64 := Array.replicate n 0
    let mut lc : UInt64 := 0
    for w in [:n] do
      let cur  : UInt64 := tape.getD w 0
      let next : UInt64 := tape.getD (w + 1) 0
      let L : UInt64 := (cur <<< 1) ||| lc
      lc := cur >>> 63
      let R : UInt64 := (cur >>> 1) ||| (if (next &&& 1) = 1 then (1 : UInt64) <<< 63 else 0)
      out := out.set! w (L ^^^ (cur ||| R))
    return out

/-- Evolve a UInt64-packed tape for `t` steps using a loop. -/
def caEvolveU64 (steps : Nat) (tape : Array UInt64) : Array UInt64 :=
  Id.run do
    let mut t := tape
    for _ in [:steps] do
      t := caStepU64 t
    return t

/-- G_{2,m}(T): center of Rule 30 after T steps, matching C's stream_G2m_all.c.
    Initial tape has spikes at positions 2 and m.
    Fixed tape of size nWords = ceil((2*T+1)/64) words (large enough for T steps).
    At step T, center = bit T of the tape (C: get_bit(tape_two, T)).

    Performance: O(T² / 64) time, O(T/64) space — ~100x faster than caStepArr version. -/
def G2mFast (m T : Nat) : Bool :=
  let nWords := (2 * T + 1 + 63) / 64
  let init := setbitU64 (setbitU64 (Array.replicate nWords (0 : UInt64)) 2) m
  let evolved := caEvolveU64 T init
  getbitU64 evolved T

/-- G_{X,m}(T): center after T steps from spikes at X and m (generalized witness).
    G2mFast = GXmFast 2.
    Used to verify non-X=2 witnesses: X=4 for m=44, X=6 for m=48. -/
def GXmFast (X m T : Nat) : Bool :=
  let nWords := (2 * T + 1 + 63) / 64
  let init := setbitU64 (setbitU64 (Array.replicate nWords (0 : UInt64)) X) m
  let evolved := caEvolveU64 T init
  getbitU64 evolved T

/-- FXFast X T: center after T steps from single spike at X.
    FXFast 2 T = (T % 2 == 1) by Spike2Parity.lean. -/
def FXFast (X T : Nat) : Bool :=
  let nWords := (2 * T + 1 + 63) / 64
  let init := setbitU64 (Array.replicate nWords (0 : UInt64)) X
  let evolved := caEvolveU64 T init
  getbitU64 evolved T
