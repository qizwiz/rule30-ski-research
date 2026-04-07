/-
Spike2Parity.lean
=================
Structural proof that rule30n (n'+1) applied to the spike-at-position-2 configuration
equals decide (n' % 2 = 0) for ALL n'.

Proof strategy: 2-step cycle.
  [f,f,t,f,...,f] --caStep--> [t,t,t,f,...,f] --caStep--> [f,f,t,f,...,f]  (smaller tape)
So rule30n(n'+1)(spike2) = rule30n(n'-1)(spike2), with base cases n'=0 (true), n'=1 (false).
-/

import P2p.CA_Basics
import Mathlib.Tactic

/-
### Key lemma: caEvolve is additive in steps
-/

private theorem caEvolve_add (a b : Nat) (cells : List Bool) :
    caEvolve (a + b) cells = caEvolve a (caEvolve b cells) := by
  induction b generalizing cells with
  | zero => simp [caEvolve]
  | succ b ih =>
    rw [Nat.add_succ, caEvolve_succ, ih, ← caEvolve_succ]

/-
### Key lemma: getElem of caStepList
-/

private theorem caStepList_getElem (cells : List Bool) (i : Nat)
    (hi : i + 2 < cells.length) :
    (caStepList cells)[i]'(by rw [caStep_length]; omega) =
    rule30Local (cells[i]'(by omega)) (cells[i+1]'(by omega)) (cells[i+2]'(by omega)) := by
  induction i generalizing cells with
  | zero =>
    match cells with
    | p :: q :: r :: rest => simp [caStepList]
  | succ n ih =>
    match cells with
    | p :: q :: r :: rest =>
      have h_rest : n + 2 < (q :: r :: rest).length := by
        have hlen1 : (p :: q :: r :: rest).length = rest.length + 3 := by simp [List.length_cons]
        have hlen2 : (q :: r :: rest).length = rest.length + 2 := by simp [List.length_cons]
        omega
      simp only [caStepList, List.getElem_cons_succ]
      exact ih (q :: r :: rest) h_rest

/-
### The two-step cycle lemma
-/

/-- One caStep: spike-at-2 becomes three-ones.
    Input: [f,f,t,f,...,f] (length 2*(m+3)+1)
    Output: [t,t,t,f,...,f] (length 2*(m+2)+1) -/
private theorem caStep_spike2 (m : Nat) :
    caStepList (List.ofFn (fun k : Fin (2 * (m + 3) + 1) => decide (k.val = 2))) =
    List.ofFn (fun k : Fin (2 * (m + 2) + 1) => decide (k.val = 0 ∨ k.val = 1 ∨ k.val = 2)) := by
  apply List.ext_getElem
  · simp only [caStep_length, List.length_ofFn]; omega
  · intro i hi1 hi2
    simp only [List.length_ofFn, caStep_length, List.length_ofFn] at hi1 hi2
    rw [caStepList_getElem _ i (by simp only [List.length_ofFn]; omega)]
    simp only [List.getElem_ofFn]
    -- Now goal: rule30Local (decide (i=2)) (decide (i+1=2)) (decide (i+2=2))
    --           = decide (i=0 ∨ i=1 ∨ i=2)
    rcases Nat.lt_or_ge i 3 with hi3 | hi3
    · -- i = 0, 1, or 2
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [rule30Local]
    · have p1 : decide (i = 2) = false := by rw [Bool.decide_false_iff]; omega
      have p2 : decide (i + 1 = 2) = false := by rw [Bool.decide_false_iff]; omega
      have p3 : decide (i + 2 = 2) = false := by rw [Bool.decide_false_iff]; omega
      have p4 : decide (i = 0 ∨ i = 1 ∨ i = 2) = false := by
        rw [Bool.decide_false_iff]; omega
      simp [rule30Local, p1, p2, p3, p4] <;> omega

/-- One caStep: three-ones becomes spike-at-2.
    Input: [t,t,t,f,...,f] (length 2*(m+2)+1)
    Output: [f,f,t,f,...,f] (length 2*(m+1)+1) = spike2 list -/
private theorem caStep_three_ones (m : Nat) :
    caStepList (List.ofFn (fun k : Fin (2 * (m + 2) + 1) => decide (k.val = 0 ∨ k.val = 1 ∨ k.val = 2))) =
    List.ofFn (fun k : Fin (2 * (m + 1) + 1) => decide (k.val = 2)) := by
  apply List.ext_getElem
  · simp only [caStep_length, List.length_ofFn]; omega
  · intro i hi1 hi2
    simp only [List.length_ofFn, caStep_length, List.length_ofFn] at hi1 hi2
    rw [caStepList_getElem _ i (by simp only [List.length_ofFn]; omega)]
    simp only [List.getElem_ofFn]
    -- Now goal: rule30Local (decide (i=0∨i=1∨i=2)) (decide (i+1=0∨...)) (decide (i+2=0∨...))
    --           = decide (i=2)
    rcases Nat.lt_or_ge i 3 with hi3 | hi3
    · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [rule30Local]
    · have p1 : decide (i = 0 ∨ i = 1 ∨ i = 2) = false := by
        rw [Bool.decide_false_iff]; push_neg; omega
      have p2 : decide (i + 1 = 0 ∨ i + 1 = 1 ∨ i + 1 = 2) = false := by
        rw [Bool.decide_false_iff]; push_neg; omega
      have p3 : decide (i + 2 = 0 ∨ i + 2 = 1 ∨ i + 2 = 2) = false := by
        rw [Bool.decide_false_iff]; push_neg; omega
      have p4 : decide (i = 2) = false := by rw [Bool.decide_false_iff]; omega
      simp [rule30Local, p1, p2, p3, p4] <;> omega

/-- Two-step cycle: spike2 list of size 2*(m+3)+1 evolves in 2 steps to spike2 of size 2*(m+1)+1 -/
private theorem spike2_two_step (m : Nat) :
    caEvolve 2 (List.ofFn (fun k : Fin (2 * (m + 3) + 1) => decide (k.val = 2))) =
    List.ofFn (fun k : Fin (2 * (m + 1) + 1) => decide (k.val = 2)) := by
  -- caEvolve 2 cells = caStepList (caStepList cells) by definition
  change caStepList (caStepList (List.ofFn (fun k : Fin (2 * (m + 3) + 1) => decide (k.val = 2)))) =
    List.ofFn (fun k : Fin (2 * (m + 1) + 1) => decide (k.val = 2))
  rw [caStep_spike2 m, caStep_three_ones m]

/-
### Main theorem
-/

/-- The parity of rule30n applied to spike-at-2 equals (n' % 2 = 0). -/
theorem rule30n_spike2_parity (n' : Nat) :
    rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) => decide (k.val = 2)) =
    decide (n' % 2 = 0) := by
  induction n' using Nat.strongRecOn with
  | ind n' ih =>
    match n' with
    | 0 => native_decide
    | 1 => native_decide
    | (m + 2) =>
      -- Need: rule30n (m+3) (spike2 at size 2*(m+3)+1) = decide ((m+2)%2=0)
      show rule30n (m + 3) (fun k : Fin (2 * (m + 3) + 1) => decide (k.val = 2)) =
           decide ((m + 2) % 2 = 0)
      simp only [rule30n, configToList]
      -- caEvolve (m+3) = caEvolve (m+1) ∘ caEvolve 2
      rw [show m + 3 = (m + 1) + 2 from by omega]
      rw [caEvolve_add]
      rw [spike2_two_step m]
      -- Now have: (caEvolve (m+1) (ofFn spike2_(m+1))).getD 0 false
      -- = rule30n (m+1) spike2_(m+1) = decide(m%2=0) by IH
      have ih_m : rule30n (m + 1) (fun k : Fin (2 * (m + 1) + 1) => decide (k.val = 2)) =
                  decide (m % 2 = 0) := ih m (by omega)
      simp only [rule30n, configToList] at ih_m
      rw [ih_m]
      -- (m+2)%2 = m%2
      simp [show (m + 2) % 2 = m % 2 from by omega]
