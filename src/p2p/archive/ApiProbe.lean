import Mathlib.Data.List.Basic

def caStepList : List Bool → List Bool
  | p :: q :: r :: rest => (p ^^ (q || r)) :: caStepList (q :: r :: rest)
  | _ => []
def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStepList cells)
def spike6List (N : Nat) : List Bool :=
  List.ofFn (fun k : Fin N => decide (k.val = 6))
lemma spike6List_length (N : Nat) : (spike6List N).length = N := by
  simp [spike6List, List.length_ofFn]
theorem caEvolve_succ (n : Nat) (cells : List Bool) :
    caEvolve (n + 1) cells = caEvolve n (caStepList cells) := rfl
theorem caStep_length (cells : List Bool) (h : cells.length ≥ 2) :
    (caStepList cells).length + 2 = cells.length := by
  match cells with
  | [] => simp at h; | [_] => simp at h; | [_, _] => simp [caStepList]
  | _ :: q :: r :: rest =>
    simp only [caStepList, List.length_cons]
    have h' : (q :: r :: rest).length ≥ 2 := by simp
    have ih := caStep_length (q :: r :: rest) h'; simp only [List.length_cons] at ih; omega
lemma caEvolve_agree (k : Nat) (l1 l2 : List Bool)
    (hlen1 : 2 * k < l1.length) (hlen2 : 2 * k < l2.length)
    (hagree : ∀ i, i ≤ 2 * k → l1.getD i false = l2.getD i false) :
    (caEvolve k l1).getD 0 false = (caEvolve k l2).getD 0 false := by sorry
lemma caStepList_drop_comm (l : List Bool) (i : Nat) :
    caStepList (l.drop i) = (caStepList l).drop i := by
  induction i generalizing l with
  | zero => simp
  | succ i ih =>
    match l with
    | [] => simp [caStepList]; | [_] => simp [caStepList]
    | [a, b] => simp only [List.drop_succ_cons]; rw [ih [b]]; simp [caStepList]
    | p :: q :: r :: rest => simp only [List.drop_succ_cons, caStepList]; exact ih (q :: r :: rest)
lemma caEvolve_drop_comm (k : Nat) (l : List Bool) (i : Nat) :
    caEvolve k (l.drop i) = (caEvolve k l).drop i := by
  induction k generalizing l with
  | zero => simp [caEvolve]
  | succ k ih => simp only [caEvolve, ih, caStepList_drop_comm]
lemma caEvolve_getD_shift (k : Nat) (l : List Bool) (i : Nat) :
    (caEvolve k l).getD i false = (caEvolve k (l.drop i)).getD 0 false := by
  rw [caEvolve_drop_comm k l i]; simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

-- Key: general version of drop agree that works for any two lists both large enough
lemma drop_spike6_agree_general (N1 N2 : Nat) (i j : Nat)
    (h1 : i + j < N1) (h2 : i + j < N2) :
    (List.drop i (spike6List N1)).getD j false =
    (List.drop i (spike6List N2)).getD j false := by
  simp only [spike6List, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_ofFn]
  simp [h1, h2]

-- For the caEvolve 16 agree: compare any two N1, N2 that are both >= i + 32 + 1
lemma caEvolve16_spike6_agree (N1 N2 : Nat) (i : Nat)
    (h1 : i + 32 < N1) (h2 : i + 32 < N2) :
    (caEvolve 16 (spike6List N1)).getD i false =
    (caEvolve 16 (spike6List N2)).getD i false := by
  rw [caEvolve_getD_shift 16 (spike6List N1) i, caEvolve_getD_shift 16 (spike6List N2) i]
  apply caEvolve_agree 16
  · rw [List.length_drop, spike6List_length]; omega
  · rw [List.length_drop, spike6List_length]; omega
  · intro j hj; exact drop_spike6_agree_general N1 N2 i j (by omega) (by omega)

-- Now prove the period-16 fact using fixed ref spike6List 45
lemma caEvolve16_spike6_45 : caEvolve 16 (spike6List 45) = spike6List 13 := by native_decide

-- For i <= 12: caEvolve 16 (spike6List N) at i = spike6List 13 at i
-- provided N > i + 32, i.e. N >= i+33.
-- For our N = 2*(n+1+16)+1 = 2*n+35, and i <= 12: need i+33 <= 2*n+35, i.e. i <= 2*n+2 = 2*(n+1).
-- Since we have hi: i <= 2*(n+1), this is exactly the condition!
-- But we still need to compare with spike6List 45 (to get the concrete value).
-- 45 >= i+33 for i <= 12: 12+33 = 45. Exactly OK (strict: i <= 11 gives i+33 <= 44 < 45; i=12 gives i+33=45, need < 45, FAIL!)
-- For i = 12: 12 + 32 = 44 < 45. But h2: i + 32 < N2 = 45 requires 44 < 45 which is true!

-- Test: caEvolve16_spike6_agree 35 45 2 works when 2+32=34 < 35 and 34 < 45
example : (caEvolve 16 (spike6List 35)).getD 2 false =
          (caEvolve 16 (spike6List 45)).getD 2 false := by
  apply caEvolve16_spike6_agree
  · omega
  · omega
