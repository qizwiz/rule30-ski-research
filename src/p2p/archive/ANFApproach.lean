import P2p.Prize3_Bridge_Verified

/-- 
A variable x_i appears in the ANF of rule30n if there exists an input where
flipping x_i changes the output.

This is exactly the definition of essentiality!
-/
def AppearsInANF (n : Nat) (i : Fin (2 * n + 1)) : Prop :=
  ∃ (c : Config n), rule30n n c ≠ rule30n n (flipCell c i)

/-- 
All variables appear in the ANF of rule30n.
-/
def AllVariablesInANF (n : Nat) : Prop :=
  ∀ (i : Fin (2 * n + 1)), AppearsInANF n i

/-- 
All cells are essential for rule30n.
-/
def AllCellsEssential (n : Nat) : Prop :=
  ∀ (i : Fin (2 * n + 1)), Essential n i

/-- 
KEY LEMMA: A variable appears in ANF iff it's essential.

Proof: Unfold definitions - they're identical!
-/
theorem appears_in_anf_iff_essential (n : Nat) (i : Fin (2 * n + 1)) :
    AppearsInANF n i ↔ Essential n i :=
  Iff.rfl

/-- 
Corollary: All variables in ANF iff all cells essential.
-/
theorem all_variables_in_anf_iff_all_essential (n : Nat) :
    AllVariablesInANF n ↔ AllCellsEssential n :=
  Iff.rfl

/-- 
For n ≥ 221, the all-zeros configuration witnesses essentiality for ALL cells.

This was discovered empirically: for large n, flipping any single bit in the
all-zeros input changes the output.

TODO: Prove this by analyzing Rule 30's structure.
-/
theorem all_zeros_witnesses_all (n : Nat) (hn : n ≥ 221) :
    AllVariablesInANF n :=
  fun i => ⟨(fun _ => false), sorry⟩

/-- 
For small n (n ≤ 220), we verify all variables appear in ANF by computation.

The Python script rule30_anf_large.py already verified this computationally.

TODO: Implement computational verification in Lean using native_decide.
-/
theorem verify_small_n (n : Nat) (hn : n ≤ 220) :
    AllVariablesInANF n :=
  sorry

/-- 
MAIN THEOREM: All cells are essential for Rule 30, for all n ≥ 1.

Proof:
- For n ≤ 220: Computational verification (verify_small_n)
- For n ≥ 221: All-zeros is a universal witness (all_zeros_witnesses_all)
-/
theorem all_cells_essential_for_all_n (n : Nat) (hn : n ≥ 1) :
    AllCellsEssential n :=
  if h : n ≤ 220 then
    have h_anf : AllVariablesInANF n := verify_small_n n h
    have h_iff : AllVariablesInANF n ↔ AllCellsEssential n := all_variables_in_anf_iff_all_essential n
    h_iff.mp h_anf
  else
    have hn' : n ≥ 221 := by omega
    have h_anf : AllVariablesInANF n := all_zeros_witnesses_all n hn'
    have h_iff : AllVariablesInANF n ↔ AllCellsEssential n := all_variables_in_anf_iff_all_essential n
    h_iff.mp h_anf
