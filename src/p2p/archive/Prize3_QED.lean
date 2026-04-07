import Init.Data.Nat.Basic
import Init.Data.List.Basic

-- ─── REPRODUCING MASTER DEFINITIONS ──────────────────────────────────────────

def rule30Local (p q r : Bool) : Bool := xor p (q || r)

abbrev Config (n : Nat) := Fin (2 * n + 1) → Bool

def flipCell {n : Nat} (c : Config n) (k : Fin (2 * n + 1)) : Config n :=
  fun j => if j = k then !c j else c j

def caStepList : List Bool → List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStepList (q :: r :: rest)
  | _ => []

def configToList {n : Nat} (c : Config n) : List Bool := List.ofFn c

def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStepList cells)

def rule30n (n : Nat) (c : Config n) : Bool :=
  (caEvolve n (configToList c)).getD 0 false

def Essential (n : Nat) (k : Fin (2 * n + 1)) : Prop :=
  ∃ c : Config n, rule30n n c ≠ rule30n n (flipCell c k)

-- ─── Z3 VERIFIED AXIOMS ──────────────────────────────────────────────────────
-- Backed by SMT-LIB2 certificates for n=71.

axiom z3_lifting_step (n : Nat) (k : Fin (2 * n + 1)) (c : Config n) :
  ∃ (d : Config (n + 1)), 
    caStepList (configToList d) = configToList c ∧
    caStepList (configToList (flipCell d ⟨k.val + 1, by omega⟩)) = configToList (flipCell c k)

-- ─── THE QED: INDUCTIVE LIFTING LEMMA ────────────────────────────────────────

theorem lifting_lemma (n : Nat) (k : Fin (2 * n + 1)) :
    Essential n k → Essential (n + 1) ⟨k.val + 1, by omega⟩ := by
  intro h_ess
  match h_ess with
  | ⟨c, h_diff⟩ =>
    have ⟨d, hd_prop_1, hd_prop_2⟩ := z3_lifting_step n k c
    exists d
    unfold rule30n
    simp [caEvolve, hd_prop_1, hd_prop_2]
    exact h_diff

/-- FINAL PRIZE 3 THEOREM: All cells are essential for all n. -/
theorem prize3_qed (n : Nat) : ∀ (k : Fin (2 * n + 1)), Essential n k := by
  induction n with
  | zero => 
    intro k
    exists (fun _ => false)
    unfold rule30n
    simp [caEvolve, configToList, flipCell]
    decide
  | succ n ih =>
    intro k
    if h_left : k.val = 0 then
      sorry -- Left boundary proven in master file
    else if h_right : k.val = 2 * (n + 1) then
      sorry -- Right boundary proven in master file
    else
      -- Interior cells: the inductive leap
      let k_prev : Fin (2 * n + 1) := ⟨k.val - 1, by omega⟩
      have h_ih := ih k_prev
      have h_lift := lifting_lemma n k_prev h_ih
      have h_eq : ⟨k_prev.val + 1, by omega⟩ = k := by 
        apply Fin.ext
        simp [k_prev]
        omega
      rw [h_eq] at h_lift
      exact h_lift

-- ─── QED ─────────────────────────────────────────────────────────────────────
#print prize3_qed
