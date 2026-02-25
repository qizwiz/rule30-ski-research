-- THE INTER-BASIN THEOREM for SKI COMBINATORS
-- Machine-verified in Lean 4

import Init.Data.Nat.Basic

-- 1. The SKI Universe
inductive SKI : Type
  | S : SKI
  | K : SKI
  | I : SKI
  | Var : String → SKI
  | app : SKI → SKI → SKI
  deriving DecidableEq

-- 2. The Topological Basin (Parenthetical Skeleton)
inductive Basin : Type
  | star : Basin
  | app : Basin → Basin → Basin
  deriving DecidableEq

-- 3. The Mapping from Logic to Topology
def get_basin : SKI → Basin
  | SKI.app e1 e2 => Basin.app (get_basin e1) (get_basin e2)
  | _ => Basin.star

-- 4. The Structural Size of a Basin
def basin_size : Basin → Nat
  | Basin.star => 1
  | Basin.app b1 b2 => basin_size b1 + basin_size b2

-- 5. Helper: Size is always > 0
theorem size_pos (b : Basin) : 1 ≤ basin_size b := by
  induction b with
  | star => exact Nat.le_refl 1
  | app b1 b2 ih1 ih2 =>
    unfold basin_size
    have h1 : 1 ≤ basin_size b1 := ih1
    have h2 : basin_size b1 ≤ basin_size b1 + basin_size b2 := Nat.le_add_right _ _
    exact Nat.le_trans h1 h2

-- 6. Structural Lemmas (Proving that physical deformation cannot loop)
theorem no_cyclic_I (b : Basin) : Basin.app Basin.star b ≠ b := by
  intro h
  have h_sz : basin_size (Basin.app Basin.star b) = basin_size b := congrArg basin_size h
  have h_sz' : 1 + basin_size b = basin_size b := by
    simpa [basin_size] using h_sz
  have h' : basin_size b + 1 = basin_size b := by
    simpa [Nat.add_comm] using h_sz'
  have h'' : Nat.succ (basin_size b) = basin_size b := by
    simpa [Nat.succ_eq_add_one] using h'
  exact (Nat.succ_ne_self (basin_size b)) h''

theorem no_cyclic_K (b1 b2 : Basin) : Basin.app (Basin.app Basin.star b1) b2 ≠ b1 := by
  intro h
  have h_sz : basin_size (Basin.app (Basin.app Basin.star b1) b2) = basin_size b1 := congrArg basin_size h
  have h_sz' : (1 + basin_size b1) + basin_size b2 = basin_size b1 := by
    simpa [basin_size] using h_sz
  have h_lt : basin_size b1 < (1 + basin_size b1) + basin_size b2 := by
    have h1 : basin_size b1 < 1 + basin_size b1 := by
      simpa [Nat.add_comm] using (Nat.lt_succ_self (basin_size b1))
    have h2 : 1 + basin_size b1 ≤ (1 + basin_size b1) + basin_size b2 := Nat.le_add_right _ _
    exact Nat.lt_of_lt_of_le h1 h2
  have h_eq : basin_size b1 = (1 + basin_size b1) + basin_size b2 := h_sz'.symm
  have : basin_size b1 < basin_size b1 := by
    exact lt_of_lt_of_eq h_lt h_eq.symm
  exact (Nat.lt_irrefl _ ) this

theorem no_cyclic_S (bx b_y bz : Basin) : 
  Basin.app (Basin.app (Basin.app Basin.star bx) b_y) bz ≠ Basin.app (Basin.app bx bz) (Basin.app b_y bz) := by
  intro h
  injection h with _ h_right
  have h_sz : basin_size bz = basin_size (Basin.app b_y bz) := congrArg basin_size h_right
  have h_sz' : basin_size bz = basin_size b_y + basin_size bz := by
    simpa [basin_size] using h_sz
  have h_eq : basin_size bz = basin_size bz + basin_size b_y := by
    simpa [Nat.add_comm] using h_sz'
  have h_lt : basin_size bz < basin_size bz + basin_size b_y := by
    have hpos : 1 ≤ basin_size b_y := size_pos b_y
    have h1 : basin_size bz < basin_size bz + 1 := by
      simpa [Nat.add_comm] using (Nat.lt_succ_self (basin_size bz))
    have h2 : basin_size bz + 1 ≤ basin_size bz + basin_size b_y := by
      exact Nat.add_le_add_left hpos _
    exact Nat.lt_of_lt_of_le h1 h2
  have : basin_size bz < basin_size bz := by
    exact lt_of_lt_of_eq h_lt h_eq.symm
  exact (Nat.lt_irrefl _) this

-- 7. Define Single-Step Reduction
inductive Step : SKI → SKI → Prop
  | step_I (x : SKI) : 
      Step (SKI.app SKI.I x) x
  | step_K (x y : SKI) : 
      Step (SKI.app (SKI.app SKI.K x) y) x
  | step_S (x y z : SKI) : 
      Step (SKI.app (SKI.app (SKI.app SKI.S x) y) z) (SKI.app (SKI.app x z) (SKI.app y z))
  | step_app_left (e1 e1' e2 : SKI) (h : Step e1 e1') :
      Step (SKI.app e1 e2) (SKI.app e1' e2)

-- 8. THE INTER-BASIN THEOREM
theorem inter_basin_theorem (e e' : SKI) (h : Step e e') : 
  get_basin e ≠ get_basin e' := by
  induction h with
  | step_I x =>
    intro h_eq
    change Basin.app Basin.star (get_basin x) = get_basin x at h_eq
    exact no_cyclic_I (get_basin x) h_eq
  | step_K x y =>
    intro h_eq
    change Basin.app (Basin.app Basin.star (get_basin x)) (get_basin y) = get_basin x at h_eq
    exact no_cyclic_K (get_basin x) (get_basin y) h_eq
  | step_S x y z =>
    intro h_eq
    change Basin.app (Basin.app (Basin.app Basin.star (get_basin x)) (get_basin y)) (get_basin z) = 
           Basin.app (Basin.app (get_basin x) (get_basin z)) (Basin.app (get_basin y) (get_basin z)) at h_eq
    exact no_cyclic_S (get_basin x) (get_basin y) (get_basin z) h_eq
  | step_app_left e1 e1' e2 _ ih =>
    intro h_eq
    change Basin.app (get_basin e1) (get_basin e2) = Basin.app (get_basin e1') (get_basin e2) at h_eq
    injection h_eq with h_left _
    exact ih h_left
