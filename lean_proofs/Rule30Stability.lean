import Init.Data.Nat.Basic

-- 1. The SKI Universe
inductive SKI : Type
  | S : SKI
  | K : SKI
  | I : SKI
  | Var : String → SKI
  | app : SKI → SKI → SKI
  deriving DecidableEq, Repr

-- 2. Define standard combinator abbreviations to make the code readable
def A (e1 e2 : SKI) : SKI := SKI.app e1 e2
def T : SKI := SKI.K
def F : SKI := A SKI.K SKI.I

-- 3. The NOT combinator: S (S I (K F)) (K T)
def NOT_comb : SKI :=
  A (A SKI.S (A (A SKI.S SKI.I) (A SKI.K F))) (A SKI.K T)

-- 4. AND combinator: p q F -> S (S I (K q)) (K F)
def apply_and (p q : SKI) : SKI := A (A p q) F

-- 5. XOR combinator: p (NOT q) q
def apply_xor (p q : SKI) : SKI :=
  let not_q := A NOT_comb q
  A (A p not_q) q

-- 6. The Rule 30 local update function: p XOR (q OR r)
-- We know OR(q,r) = q q r
def apply_rule30 (p q r : SKI) : SKI :=
  let q_or_r := A (A q q) r
  let not_q_or_r := A NOT_comb q_or_r
  A (A p not_q_or_r) q_or_r

-- 7. Recursive generation of the Center Cell
-- Starts at gen 0: T if pos = 0 else F
def build_center_cell (gen : Nat) (pos : Int) : SKI :=
  match gen with
  | 0 => if pos = 0 then T else F
  | g + 1 => 
      let left := build_center_cell g (pos - 1)
      let center := build_center_cell g pos
      let right := build_center_cell g (pos + 1)
      apply_rule30 left center right

-- 8. The Topological Basin
inductive Basin : Type
  | star : Basin
  | app : Basin → Basin → Basin
  deriving DecidableEq, Repr

def get_basin : SKI → Basin
  | SKI.app e1 e2 => Basin.app (get_basin e1) (get_basin e2)
  | _ => Basin.star

-- 9. Extracting the "Outermost Shell" (Prefix Depth of 4)
-- This function truncates the basin at depth 4, turning any deeper structure into a single star.
-- This allows us to mathematically compare the macro-structure while ignoring the chaotic micro-structure.
def truncate_basin : Nat → Basin → Basin
  | 0, _ => Basin.star
  | _, Basin.star => Basin.star
  | d + 1, Basin.app b1 b2 => Basin.app (truncate_basin d b1) (truncate_basin d b2)

-- 10. The Target Theorem (The Prize Winner)
-- "The macro-structure of the Rule 30 computation completely stabilizes by Generation 3."
-- We want to prove that for any N >= 3, the outermost shell of the basin is identical to Gen 3.
-- theorem rule30_macro_stability (n : Nat) (h : n ≥ 3) : 
--   truncate_basin 4 (get_basin (build_center_cell n 0)) = 
--   truncate_basin 4 (get_basin (build_center_cell 3 0)) := by
--   sorry
