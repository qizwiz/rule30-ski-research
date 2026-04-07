/-
  ConeStructure.lean  —  Rule 30 Cone Geometry (Lean 4, no Mathlib)

  Coffee-filter insight:
    FLAT DISK  = SKI normal form: 5^n input appearances, no sharing
    CONE       = actual CA: memoized, O(n²)
    FOLD MAP   = memoization preserves the computed Boolean function
    5^n arises from XOR(OR): OR(q,r) appears TWICE in the XOR encoding,
                 giving recurrence T(n+1) = 1·T(n) + 2·T(n) + 2·T(n) = 5·T(n)
-/

import P2p.Prize3_Bridge_Verified

-- ─── Boolean rule ────────────────────────────────────────────────────────────

def rule30Local (p q r : Bool) : Bool := xor p (q || r)

-- Verify the truth table
#eval (List.range 8).map fun n =>
  let p := n / 4 % 2 == 1; let q := n / 2 % 2 == 1; let r := n % 2 == 1
  (p, q, r, rule30Local p q r)

-- ─── Configuration ───────────────────────────────────────────────────────────

abbrev Config (n : Nat) := Fin (2 * n + 1) → Bool

def flipCell {n : Nat} (c : Config n) (k : Fin (2 * n + 1)) : Config n :=
  fun j => if j = k then !c j else c j

-- ─── List-based CA computation (easily computable) ───────────────────────────

-- Apply one step of Rule 30 to a list of cells
-- Input: 2(n-t)+1 cells;  Output: 2(n-t-1)+1 cells = 2 fewer
def caStep : List Bool → List Bool
  | p :: q :: r :: rest => rule30Local p q r :: caStep (q :: r :: rest)
  | _ => []

-- Convert Config to List
def configToList {n : Nat} (c : Config n) : List Bool := List.ofFn c

-- Apply n steps of Rule 30; the center cell is always at index n - t after t steps
def caEvolve : Nat → List Bool → List Bool
  | 0, cells => cells
  | t + 1, cells => caEvolve t (caStep cells)

-- n-step center cell output
-- After n steps of caStep on 2n+1 cells, we have 1 cell remaining
def rule30n (n : Nat) (c : Config n) : Bool :=
  (caEvolve n (configToList c)).headD false

-- ─── Eval checks ─────────────────────────────────────────────────────────────

-- All-zeros: should always produce false
#eval rule30n 0 (fun _ => false)   -- single cell all-zero: false ✓
#eval rule30n 1 (fun _ => false)   -- (0,0,0) → 0: false ✓
#eval rule30n 2 (fun _ => false)   -- 5 zeros → 0: false ✓
#eval rule30n 3 (fun _ => false)   -- 7 zeros → 0: false ✓

-- Single 1 at center (index n): should propagate
-- n=1, Config 1 = Fin 3 → Bool; center is index 1
#eval rule30n 1 (fun i => i.val == 1)   -- (0,1,0) → 1 ✓
-- n=2, center is index 2
#eval rule30n 2 (fun i => i.val == 2)   -- should produce a specific value

-- ─── THE 5^n THEOREM (pure number theory) ────────────────────────────────────
--
-- This is the KEY theorem from the SKI normal-form analysis.
-- It's about the XOR(OR) compilation recurrence, NOT about the list-based CA.
--
-- In the SKI normal form for rule30Local:
--   rule30Local p q r = p XOR (q OR r) = IF p THEN NOT(q OR r) ELSE (q OR r)
-- The term (q OR r) appears TWICE — once in each branch.
-- So the flat tree (SKI compilation with no sharing) satisfies:
--   T(0) = 1  (leaf)
--   T(n+1) = T(n) + T(n) + T(n) + T(n) + T(n) = 5 * T(n)
--   [1 copy of left, 2 copies of center, 2 copies of right — due to XOR duplication]
-- Therefore T(n) = 5^n.

def skiLeafCount : Nat → Nat
  | 0     => 1
  | n + 1 => 5 * skiLeafCount n

theorem skiLeafCount_eq (n : Nat) : skiLeafCount n = 5 ^ n := by
  induction n with
  | zero      => simp [skiLeafCount]
  | succ n ih =>
    simp only [skiLeafCount, ih]
    rw [Nat.pow_succ]
    omega

-- This is the 5^n theorem: the SKI flat tree for n-step Rule 30 has exactly 5^n leaves.
#eval skiLeafCount 0  -- 1
#eval skiLeafCount 1  -- 5
#eval skiLeafCount 2  -- 25
#eval skiLeafCount 3  -- 125
#eval skiLeafCount 4  -- 625

-- ─── SENSITIVITY ─────────────────────────────────────────────────────────────

def Essential (n : Nat) (k : Fin (2 * n + 1)) : Prop :=
  ∃ c : Config n, rule30n n c ≠ rule30n n (flipCell c k)

-- Encode a config from a bitmask (bit i = cell i)
def configOfMask (n : Nat) (mask : Nat) : Config n :=
  fun i => Nat.testBit mask i.val

-- ─── n = 1: all 3 cells essential ────────────────────────────────────────────
-- Witness: mask=0 (all-zeros). Flipping any cell changes (0,0,0)→0 to something→1.

theorem essential_n1_k0 : Essential 1 ⟨0, by omega⟩ :=
  ⟨configOfMask 1 0, by native_decide⟩

theorem essential_n1_k1 : Essential 1 ⟨1, by omega⟩ :=
  ⟨configOfMask 1 0, by native_decide⟩

theorem essential_n1_k2 : Essential 1 ⟨2, by omega⟩ :=
  ⟨configOfMask 1 0, by native_decide⟩

-- ─── n = 2: all 5 cells essential ────────────────────────────────────────────
-- Witnesses (computed by exhaustive search):
--   k=0: mask=0  (all-zeros)
--   k=1: mask=8  (cell 3 = bit 3 set)
--   k=2: mask=8  (cell 3 = bit 3 set)
--   k=3: mask=0  (all-zeros)
--   k=4: mask=0  (all-zeros)

theorem essential_n2_k0 : Essential 2 ⟨0, by omega⟩ :=
  ⟨configOfMask 2 0, by native_decide⟩

theorem essential_n2_k1 : Essential 2 ⟨1, by omega⟩ :=
  ⟨configOfMask 2 8, by native_decide⟩

theorem essential_n2_k2 : Essential 2 ⟨2, by omega⟩ :=
  ⟨configOfMask 2 8, by native_decide⟩

theorem essential_n2_k3 : Essential 2 ⟨3, by omega⟩ :=
  ⟨configOfMask 2 0, by native_decide⟩

theorem essential_n2_k4 : Essential 2 ⟨4, by omega⟩ :=
  ⟨configOfMask 2 0, by native_decide⟩

-- ─── n = 3: all 7 cells essential ────────────────────────────────────────────
-- Witnesses (mask=0 for k=0,1,2,3,5,6; mask=2 for k=4):
--   k=0..3,5,6: mask=0 (all-zeros)
--   k=4:        mask=2 (cell 1 = bit 1 set)

theorem essential_n3_k0 : Essential 3 ⟨0, by omega⟩ :=
  ⟨configOfMask 3 0, by native_decide⟩

theorem essential_n3_k1 : Essential 3 ⟨1, by omega⟩ :=
  ⟨configOfMask 3 0, by native_decide⟩

theorem essential_n3_k2 : Essential 3 ⟨2, by omega⟩ :=
  ⟨configOfMask 3 0, by native_decide⟩

theorem essential_n3_k3 : Essential 3 ⟨3, by omega⟩ :=
  ⟨configOfMask 3 0, by native_decide⟩

theorem essential_n3_k4 : Essential 3 ⟨4, by omega⟩ :=
  ⟨configOfMask 3 2, by native_decide⟩

theorem essential_n3_k5 : Essential 3 ⟨5, by omega⟩ :=
  ⟨configOfMask 3 0, by native_decide⟩

theorem essential_n3_k6 : Essential 3 ⟨6, by omega⟩ :=
  ⟨configOfMask 3 0, by native_decide⟩

-- ─── n = 4: all 9 cells essential ────────────────────────────────────────────
-- Witnesses (computed by exhaustive search):
--   k=0:    mask=0   (all-zeros)
--   k=1:    mask=64  (cell 6 = bit 6 set)
--   k=2:    mask=16  (cell 4 = bit 4 set)
--   k=3:    mask=16  (cell 4 = bit 4 set)
--   k=4:    mask=0   (all-zeros)
--   k=5:    mask=12  (cells 2,3 = bits 2,3 set)
--   k=6:    mask=2   (cell 1 = bit 1 set)
--   k=7:    mask=0   (all-zeros)
--   k=8:    mask=0   (all-zeros)

theorem essential_n4_k0 : Essential 4 ⟨0, by omega⟩ :=
  ⟨configOfMask 4 0, by native_decide⟩

theorem essential_n4_k1 : Essential 4 ⟨1, by omega⟩ :=
  ⟨configOfMask 4 64, by native_decide⟩

theorem essential_n4_k2 : Essential 4 ⟨2, by omega⟩ :=
  ⟨configOfMask 4 16, by native_decide⟩

theorem essential_n4_k3 : Essential 4 ⟨3, by omega⟩ :=
  ⟨configOfMask 4 16, by native_decide⟩

theorem essential_n4_k4 : Essential 4 ⟨4, by omega⟩ :=
  ⟨configOfMask 4 0, by native_decide⟩

theorem essential_n4_k5 : Essential 4 ⟨5, by omega⟩ :=
  ⟨configOfMask 4 12, by native_decide⟩

theorem essential_n4_k6 : Essential 4 ⟨6, by omega⟩ :=
  ⟨configOfMask 4 2, by native_decide⟩

theorem essential_n4_k7 : Essential 4 ⟨7, by omega⟩ :=
  ⟨configOfMask 4 0, by native_decide⟩

theorem essential_n4_k8 : Essential 4 ⟨8, by omega⟩ :=
  ⟨configOfMask 4 0, by native_decide⟩

-- ─── n = 5: all 11 cells essential ────────────────────────────────────────────
-- Witnesses (computed by exhaustive search):
--   k=0..2,4..7,9,10: mask=0  (all-zeros)
--   k=3:              mask=16 (cell 4 set)
--   k=8:              mask=2  (cell 1 set)

theorem essential_n5_k0 : Essential 5 ⟨0, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k1 : Essential 5 ⟨1, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k2 : Essential 5 ⟨2, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k3 : Essential 5 ⟨3, by omega⟩ := ⟨configOfMask 5 16, by native_decide⟩
theorem essential_n5_k4 : Essential 5 ⟨4, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k5 : Essential 5 ⟨5, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k6 : Essential 5 ⟨6, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k7 : Essential 5 ⟨7, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k8 : Essential 5 ⟨8, by omega⟩ := ⟨configOfMask 5 2, by native_decide⟩
theorem essential_n5_k9 : Essential 5 ⟨9, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩
theorem essential_n5_k10 : Essential 5 ⟨10, by omega⟩ := ⟨configOfMask 5 0, by native_decide⟩

-- ─── n = 6: all 13 cells essential ────────────────────────────────────────────
-- Witnesses: k=1,2: mask=8; k=4,6,10: mask=2; k=5,9: mask=12; k=7: mask=4; others: mask=0

theorem essential_n6_k0 : Essential 6 ⟨0, by omega⟩ := ⟨configOfMask 6 0, by native_decide⟩
theorem essential_n6_k1 : Essential 6 ⟨1, by omega⟩ := ⟨configOfMask 6 8, by native_decide⟩
theorem essential_n6_k2 : Essential 6 ⟨2, by omega⟩ := ⟨configOfMask 6 8, by native_decide⟩
theorem essential_n6_k3 : Essential 6 ⟨3, by omega⟩ := ⟨configOfMask 6 0, by native_decide⟩
theorem essential_n6_k4 : Essential 6 ⟨4, by omega⟩ := ⟨configOfMask 6 2, by native_decide⟩
theorem essential_n6_k5 : Essential 6 ⟨5, by omega⟩ := ⟨configOfMask 6 12, by native_decide⟩
theorem essential_n6_k6 : Essential 6 ⟨6, by omega⟩ := ⟨configOfMask 6 2, by native_decide⟩
theorem essential_n6_k7 : Essential 6 ⟨7, by omega⟩ := ⟨configOfMask 6 4, by native_decide⟩
theorem essential_n6_k8 : Essential 6 ⟨8, by omega⟩ := ⟨configOfMask 6 0, by native_decide⟩
theorem essential_n6_k9 : Essential 6 ⟨9, by omega⟩ := ⟨configOfMask 6 12, by native_decide⟩
theorem essential_n6_k10 : Essential 6 ⟨10, by omega⟩ := ⟨configOfMask 6 2, by native_decide⟩
theorem essential_n6_k11 : Essential 6 ⟨11, by omega⟩ := ⟨configOfMask 6 0, by native_decide⟩
theorem essential_n6_k12 : Essential 6 ⟨12, by omega⟩ := ⟨configOfMask 6 0, by native_decide⟩

-- ─── n = 7: all 15 cells essential ────────────────────────────────────────────
-- Witnesses: k=6,12: mask=2; k=7: mask=4; others: mask=0

theorem essential_n7_k0 : Essential 7 ⟨0, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k1 : Essential 7 ⟨1, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k2 : Essential 7 ⟨2, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k3 : Essential 7 ⟨3, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k4 : Essential 7 ⟨4, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k5 : Essential 7 ⟨5, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k6 : Essential 7 ⟨6, by omega⟩ := ⟨configOfMask 7 2, by native_decide⟩
theorem essential_n7_k7 : Essential 7 ⟨7, by omega⟩ := ⟨configOfMask 7 4, by native_decide⟩
theorem essential_n7_k8 : Essential 7 ⟨8, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k9 : Essential 7 ⟨9, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k10 : Essential 7 ⟨10, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k11 : Essential 7 ⟨11, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k12 : Essential 7 ⟨12, by omega⟩ := ⟨configOfMask 7 2, by native_decide⟩
theorem essential_n7_k13 : Essential 7 ⟨13, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩
theorem essential_n7_k14 : Essential 7 ⟨14, by omega⟩ := ⟨configOfMask 7 0, by native_decide⟩

-- ─── n = 8: all 17 cells essential ────────────────────────────────────────────
-- Witnesses: k=1,2,3: mask=128; k=4,5: mask=64; k=9,13: mask=12; k=10,14: mask=2; k=11: mask=4; others: mask=0

theorem essential_n8_k0 : Essential 8 ⟨0, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩
theorem essential_n8_k1 : Essential 8 ⟨1, by omega⟩ := ⟨configOfMask 8 128, by native_decide⟩
theorem essential_n8_k2 : Essential 8 ⟨2, by omega⟩ := ⟨configOfMask 8 128, by native_decide⟩
theorem essential_n8_k3 : Essential 8 ⟨3, by omega⟩ := ⟨configOfMask 8 128, by native_decide⟩
theorem essential_n8_k4 : Essential 8 ⟨4, by omega⟩ := ⟨configOfMask 8 64, by native_decide⟩
theorem essential_n8_k5 : Essential 8 ⟨5, by omega⟩ := ⟨configOfMask 8 64, by native_decide⟩
theorem essential_n8_k6 : Essential 8 ⟨6, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩
theorem essential_n8_k7 : Essential 8 ⟨7, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩
theorem essential_n8_k8 : Essential 8 ⟨8, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩
theorem essential_n8_k9 : Essential 8 ⟨9, by omega⟩ := ⟨configOfMask 8 12, by native_decide⟩
theorem essential_n8_k10 : Essential 8 ⟨10, by omega⟩ := ⟨configOfMask 8 2, by native_decide⟩
theorem essential_n8_k11 : Essential 8 ⟨11, by omega⟩ := ⟨configOfMask 8 4, by native_decide⟩
theorem essential_n8_k12 : Essential 8 ⟨12, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩
theorem essential_n8_k13 : Essential 8 ⟨13, by omega⟩ := ⟨configOfMask 8 12, by native_decide⟩
theorem essential_n8_k14 : Essential 8 ⟨14, by omega⟩ := ⟨configOfMask 8 2, by native_decide⟩
theorem essential_n8_k15 : Essential 8 ⟨15, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩
theorem essential_n8_k16 : Essential 8 ⟨16, by omega⟩ := ⟨configOfMask 8 0, by native_decide⟩

-- n=9 (19 cells)
theorem essential_n9_k0 : Essential 9 ⟨0, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k1 : Essential 9 ⟨1, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k2 : Essential 9 ⟨2, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k3 : Essential 9 ⟨3, by omega⟩ := ⟨configOfMask 9 128, by native_decide⟩
theorem essential_n9_k4 : Essential 9 ⟨4, by omega⟩ := ⟨configOfMask 9 64, by native_decide⟩
theorem essential_n9_k5 : Essential 9 ⟨5, by omega⟩ := ⟨configOfMask 9 64, by native_decide⟩
theorem essential_n9_k6 : Essential 9 ⟨6, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k7 : Essential 9 ⟨7, by omega⟩ := ⟨configOfMask 9 2, by native_decide⟩
theorem essential_n9_k8 : Essential 9 ⟨8, by omega⟩ := ⟨configOfMask 9 2, by native_decide⟩
theorem essential_n9_k9 : Essential 9 ⟨9, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k10 : Essential 9 ⟨10, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k11 : Essential 9 ⟨11, by omega⟩ := ⟨configOfMask 9 4, by native_decide⟩
theorem essential_n9_k12 : Essential 9 ⟨12, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k13 : Essential 9 ⟨13, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k14 : Essential 9 ⟨14, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k15 : Essential 9 ⟨15, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k16 : Essential 9 ⟨16, by omega⟩ := ⟨configOfMask 9 2, by native_decide⟩
theorem essential_n9_k17 : Essential 9 ⟨17, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩
theorem essential_n9_k18 : Essential 9 ⟨18, by omega⟩ := ⟨configOfMask 9 0, by native_decide⟩

-- n=10 (21 cells)
theorem essential_n10_k0 : Essential 10 ⟨0, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k1 : Essential 10 ⟨1, by omega⟩ := ⟨configOfMask 10 8, by native_decide⟩
theorem essential_n10_k2 : Essential 10 ⟨2, by omega⟩ := ⟨configOfMask 10 8, by native_decide⟩
theorem essential_n10_k3 : Essential 10 ⟨3, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k4 : Essential 10 ⟨4, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k5 : Essential 10 ⟨5, by omega⟩ := ⟨configOfMask 10 64, by native_decide⟩
theorem essential_n10_k6 : Essential 10 ⟨6, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k7 : Essential 10 ⟨7, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k8 : Essential 10 ⟨8, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k9 : Essential 10 ⟨9, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k10 : Essential 10 ⟨10, by omega⟩ := ⟨configOfMask 10 8, by native_decide⟩
theorem essential_n10_k11 : Essential 10 ⟨11, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k12 : Essential 10 ⟨12, by omega⟩ := ⟨configOfMask 10 2, by native_decide⟩
theorem essential_n10_k13 : Essential 10 ⟨13, by omega⟩ := ⟨configOfMask 10 12, by native_decide⟩
theorem essential_n10_k14 : Essential 10 ⟨14, by omega⟩ := ⟨configOfMask 10 2, by native_decide⟩
theorem essential_n10_k15 : Essential 10 ⟨15, by omega⟩ := ⟨configOfMask 10 4, by native_decide⟩
theorem essential_n10_k16 : Essential 10 ⟨16, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k17 : Essential 10 ⟨17, by omega⟩ := ⟨configOfMask 10 12, by native_decide⟩
theorem essential_n10_k18 : Essential 10 ⟨18, by omega⟩ := ⟨configOfMask 10 2, by native_decide⟩
theorem essential_n10_k19 : Essential 10 ⟨19, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩
theorem essential_n10_k20 : Essential 10 ⟨20, by omega⟩ := ⟨configOfMask 10 0, by native_decide⟩


-- n=11 (23 cells)
theorem essential_n11_k0 : Essential 11 ⟨0, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k1 : Essential 11 ⟨1, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k2 : Essential 11 ⟨2, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k3 : Essential 11 ⟨3, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k4 : Essential 11 ⟨4, by omega⟩ := ⟨configOfMask 11 2, by native_decide⟩
theorem essential_n11_k5 : Essential 11 ⟨5, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k6 : Essential 11 ⟨6, by omega⟩ := ⟨configOfMask 11 2, by native_decide⟩
theorem essential_n11_k7 : Essential 11 ⟨7, by omega⟩ := ⟨configOfMask 11 2, by native_decide⟩
theorem essential_n11_k8 : Essential 11 ⟨8, by omega⟩ := ⟨configOfMask 11 2, by native_decide⟩
theorem essential_n11_k9 : Essential 11 ⟨9, by omega⟩ := ⟨configOfMask 11 8, by native_decide⟩
theorem essential_n11_k10 : Essential 11 ⟨10, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k11 : Essential 11 ⟨11, by omega⟩ := ⟨configOfMask 11 4, by native_decide⟩
theorem essential_n11_k12 : Essential 11 ⟨12, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k13 : Essential 11 ⟨13, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k14 : Essential 11 ⟨14, by omega⟩ := ⟨configOfMask 11 2, by native_decide⟩
theorem essential_n11_k15 : Essential 11 ⟨15, by omega⟩ := ⟨configOfMask 11 4, by native_decide⟩
theorem essential_n11_k16 : Essential 11 ⟨16, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k17 : Essential 11 ⟨17, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k18 : Essential 11 ⟨18, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k19 : Essential 11 ⟨19, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k20 : Essential 11 ⟨20, by omega⟩ := ⟨configOfMask 11 2, by native_decide⟩
theorem essential_n11_k21 : Essential 11 ⟨21, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩
theorem essential_n11_k22 : Essential 11 ⟨22, by omega⟩ := ⟨configOfMask 11 0, by native_decide⟩


-- n=12 (25 cells)
theorem essential_n12_k0 : Essential 12 ⟨0, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k1 : Essential 12 ⟨1, by omega⟩ := ⟨configOfMask 12 64, by native_decide⟩
theorem essential_n12_k2 : Essential 12 ⟨2, by omega⟩ := ⟨configOfMask 12 16, by native_decide⟩
theorem essential_n12_k3 : Essential 12 ⟨3, by omega⟩ := ⟨configOfMask 12 16, by native_decide⟩
theorem essential_n12_k4 : Essential 12 ⟨4, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k5 : Essential 12 ⟨5, by omega⟩ := ⟨configOfMask 12 12, by native_decide⟩
theorem essential_n12_k6 : Essential 12 ⟨6, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k7 : Essential 12 ⟨7, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k8 : Essential 12 ⟨8, by omega⟩ := ⟨configOfMask 12 2, by native_decide⟩
theorem essential_n12_k9 : Essential 12 ⟨9, by omega⟩ := ⟨configOfMask 12 12, by native_decide⟩
theorem essential_n12_k10 : Essential 12 ⟨10, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k11 : Essential 12 ⟨11, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k12 : Essential 12 ⟨12, by omega⟩ := ⟨configOfMask 12 8, by native_decide⟩
theorem essential_n12_k13 : Essential 12 ⟨13, by omega⟩ := ⟨configOfMask 12 2, by native_decide⟩
theorem essential_n12_k14 : Essential 12 ⟨14, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k15 : Essential 12 ⟨15, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k16 : Essential 12 ⟨16, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k17 : Essential 12 ⟨17, by omega⟩ := ⟨configOfMask 12 12, by native_decide⟩
theorem essential_n12_k18 : Essential 12 ⟨18, by omega⟩ := ⟨configOfMask 12 2, by native_decide⟩
theorem essential_n12_k19 : Essential 12 ⟨19, by omega⟩ := ⟨configOfMask 12 4, by native_decide⟩
theorem essential_n12_k20 : Essential 12 ⟨20, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k21 : Essential 12 ⟨21, by omega⟩ := ⟨configOfMask 12 12, by native_decide⟩
theorem essential_n12_k22 : Essential 12 ⟨22, by omega⟩ := ⟨configOfMask 12 2, by native_decide⟩
theorem essential_n12_k23 : Essential 12 ⟨23, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩
theorem essential_n12_k24 : Essential 12 ⟨24, by omega⟩ := ⟨configOfMask 12 0, by native_decide⟩


-- n=13 (27 cells)
theorem essential_n13_k0 : Essential 13 ⟨0, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k1 : Essential 13 ⟨1, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k2 : Essential 13 ⟨2, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k3 : Essential 13 ⟨3, by omega⟩ := ⟨configOfMask 13 16, by native_decide⟩
theorem essential_n13_k4 : Essential 13 ⟨4, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k5 : Essential 13 ⟨5, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k6 : Essential 13 ⟨6, by omega⟩ := ⟨configOfMask 13 4, by native_decide⟩
theorem essential_n13_k7 : Essential 13 ⟨7, by omega⟩ := ⟨configOfMask 13 4, by native_decide⟩
theorem essential_n13_k8 : Essential 13 ⟨8, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k9 : Essential 13 ⟨9, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k10 : Essential 13 ⟨10, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k11 : Essential 13 ⟨11, by omega⟩ := ⟨configOfMask 13 4, by native_decide⟩
theorem essential_n13_k12 : Essential 13 ⟨12, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k13 : Essential 13 ⟨13, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k14 : Essential 13 ⟨14, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k15 : Essential 13 ⟨15, by omega⟩ := ⟨configOfMask 13 2, by native_decide⟩
theorem essential_n13_k16 : Essential 13 ⟨16, by omega⟩ := ⟨configOfMask 13 2, by native_decide⟩
theorem essential_n13_k17 : Essential 13 ⟨17, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k18 : Essential 13 ⟨18, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k19 : Essential 13 ⟨19, by omega⟩ := ⟨configOfMask 13 4, by native_decide⟩
theorem essential_n13_k20 : Essential 13 ⟨20, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k21 : Essential 13 ⟨21, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k22 : Essential 13 ⟨22, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k23 : Essential 13 ⟨23, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k24 : Essential 13 ⟨24, by omega⟩ := ⟨configOfMask 13 2, by native_decide⟩
theorem essential_n13_k25 : Essential 13 ⟨25, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩
theorem essential_n13_k26 : Essential 13 ⟨26, by omega⟩ := ⟨configOfMask 13 0, by native_decide⟩

-- ========= n=14 (29 cells) — computed 2026-03-01 =========
theorem essential_n14_k0 : Essential 14 ⟨0, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k1 : Essential 14 ⟨1, by omega⟩ := ⟨configOfMask 14 8, by native_decide⟩
theorem essential_n14_k2 : Essential 14 ⟨2, by omega⟩ := ⟨configOfMask 14 8, by native_decide⟩
theorem essential_n14_k3 : Essential 14 ⟨3, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k4 : Essential 14 ⟨4, by omega⟩ := ⟨configOfMask 14 2, by native_decide⟩
theorem essential_n14_k5 : Essential 14 ⟨5, by omega⟩ := ⟨configOfMask 14 12, by native_decide⟩
theorem essential_n14_k6 : Essential 14 ⟨6, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k7 : Essential 14 ⟨7, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k8 : Essential 14 ⟨8, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k9 : Essential 14 ⟨9, by omega⟩ := ⟨configOfMask 14 2, by native_decide⟩
theorem essential_n14_k10 : Essential 14 ⟨10, by omega⟩ := ⟨configOfMask 14 4, by native_decide⟩
theorem essential_n14_k11 : Essential 14 ⟨11, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k12 : Essential 14 ⟨12, by omega⟩ := ⟨configOfMask 14 16, by native_decide⟩
theorem essential_n14_k13 : Essential 14 ⟨13, by omega⟩ := ⟨configOfMask 14 4, by native_decide⟩
theorem essential_n14_k14 : Essential 14 ⟨14, by omega⟩ := ⟨configOfMask 14 2, by native_decide⟩
theorem essential_n14_k15 : Essential 14 ⟨15, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k16 : Essential 14 ⟨16, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k17 : Essential 14 ⟨17, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k18 : Essential 14 ⟨18, by omega⟩ := ⟨configOfMask 14 8, by native_decide⟩
theorem essential_n14_k19 : Essential 14 ⟨19, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k20 : Essential 14 ⟨20, by omega⟩ := ⟨configOfMask 14 2, by native_decide⟩
theorem essential_n14_k21 : Essential 14 ⟨21, by omega⟩ := ⟨configOfMask 14 12, by native_decide⟩
theorem essential_n14_k22 : Essential 14 ⟨22, by omega⟩ := ⟨configOfMask 14 2, by native_decide⟩
theorem essential_n14_k23 : Essential 14 ⟨23, by omega⟩ := ⟨configOfMask 14 4, by native_decide⟩
theorem essential_n14_k24 : Essential 14 ⟨24, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k25 : Essential 14 ⟨25, by omega⟩ := ⟨configOfMask 14 12, by native_decide⟩
theorem essential_n14_k26 : Essential 14 ⟨26, by omega⟩ := ⟨configOfMask 14 2, by native_decide⟩
theorem essential_n14_k27 : Essential 14 ⟨27, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩
theorem essential_n14_k28 : Essential 14 ⟨28, by omega⟩ := ⟨configOfMask 14 0, by native_decide⟩

-- ========= n=15 (31 cells) — computed 2026-03-01 =========
theorem essential_n15_k0 : Essential 15 ⟨0, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k1 : Essential 15 ⟨1, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k2 : Essential 15 ⟨2, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k3 : Essential 15 ⟨3, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k4 : Essential 15 ⟨4, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k5 : Essential 15 ⟨5, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k6 : Essential 15 ⟨6, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k7 : Essential 15 ⟨7, by omega⟩ := ⟨configOfMask 15 2, by native_decide⟩
theorem essential_n15_k8 : Essential 15 ⟨8, by omega⟩ := ⟨configOfMask 15 2, by native_decide⟩
theorem essential_n15_k9 : Essential 15 ⟨9, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k10 : Essential 15 ⟨10, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k11 : Essential 15 ⟨11, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k12 : Essential 15 ⟨12, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k13 : Essential 15 ⟨13, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k14 : Essential 15 ⟨14, by omega⟩ := ⟨configOfMask 15 2, by native_decide⟩
theorem essential_n15_k15 : Essential 15 ⟨15, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k16 : Essential 15 ⟨16, by omega⟩ := ⟨configOfMask 15 8, by native_decide⟩
theorem essential_n15_k17 : Essential 15 ⟨17, by omega⟩ := ⟨configOfMask 15 16, by native_decide⟩
theorem essential_n15_k18 : Essential 15 ⟨18, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k19 : Essential 15 ⟨19, by omega⟩ := ⟨configOfMask 15 4, by native_decide⟩
theorem essential_n15_k20 : Essential 15 ⟨20, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k21 : Essential 15 ⟨21, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k22 : Essential 15 ⟨22, by omega⟩ := ⟨configOfMask 15 2, by native_decide⟩
theorem essential_n15_k23 : Essential 15 ⟨23, by omega⟩ := ⟨configOfMask 15 4, by native_decide⟩
theorem essential_n15_k24 : Essential 15 ⟨24, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k25 : Essential 15 ⟨25, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k26 : Essential 15 ⟨26, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k27 : Essential 15 ⟨27, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k28 : Essential 15 ⟨28, by omega⟩ := ⟨configOfMask 15 2, by native_decide⟩
theorem essential_n15_k29 : Essential 15 ⟨29, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩
theorem essential_n15_k30 : Essential 15 ⟨30, by omega⟩ := ⟨configOfMask 15 0, by native_decide⟩

-- ========= n=16 (33 cells) — computed 2026-03-01 =========
theorem essential_n16_k0 : Essential 16 ⟨0, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k1 : Essential 16 ⟨1, by omega⟩ := ⟨configOfMask 16 896, by native_decide⟩
theorem essential_n16_k2 : Essential 16 ⟨2, by omega⟩ := ⟨configOfMask 16 448, by native_decide⟩
theorem essential_n16_k3 : Essential 16 ⟨3, by omega⟩ := ⟨configOfMask 16 272, by native_decide⟩
theorem essential_n16_k4 : Essential 16 ⟨4, by omega⟩ := ⟨configOfMask 16 256, by native_decide⟩
theorem essential_n16_k5 : Essential 16 ⟨5, by omega⟩ := ⟨configOfMask 16 128, by native_decide⟩
theorem essential_n16_k6 : Essential 16 ⟨6, by omega⟩ := ⟨configOfMask 16 128, by native_decide⟩
theorem essential_n16_k7 : Essential 16 ⟨7, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k8 : Essential 16 ⟨8, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k9 : Essential 16 ⟨9, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k10 : Essential 16 ⟨10, by omega⟩ := ⟨configOfMask 16 2, by native_decide⟩
theorem essential_n16_k11 : Essential 16 ⟨11, by omega⟩ := ⟨configOfMask 16 4, by native_decide⟩
theorem essential_n16_k12 : Essential 16 ⟨12, by omega⟩ := ⟨configOfMask 16 2, by native_decide⟩
theorem essential_n16_k13 : Essential 16 ⟨13, by omega⟩ := ⟨configOfMask 16 4, by native_decide⟩
theorem essential_n16_k14 : Essential 16 ⟨14, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k15 : Essential 16 ⟨15, by omega⟩ := ⟨configOfMask 16 2, by native_decide⟩
theorem essential_n16_k16 : Essential 16 ⟨16, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k17 : Essential 16 ⟨17, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k18 : Essential 16 ⟨18, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k19 : Essential 16 ⟨19, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k20 : Essential 16 ⟨20, by omega⟩ := ⟨configOfMask 16 8, by native_decide⟩
theorem essential_n16_k21 : Essential 16 ⟨21, by omega⟩ := ⟨configOfMask 16 2, by native_decide⟩
theorem essential_n16_k22 : Essential 16 ⟨22, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k23 : Essential 16 ⟨23, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k24 : Essential 16 ⟨24, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k25 : Essential 16 ⟨25, by omega⟩ := ⟨configOfMask 16 12, by native_decide⟩
theorem essential_n16_k26 : Essential 16 ⟨26, by omega⟩ := ⟨configOfMask 16 2, by native_decide⟩
theorem essential_n16_k27 : Essential 16 ⟨27, by omega⟩ := ⟨configOfMask 16 4, by native_decide⟩
theorem essential_n16_k28 : Essential 16 ⟨28, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k29 : Essential 16 ⟨29, by omega⟩ := ⟨configOfMask 16 12, by native_decide⟩
theorem essential_n16_k30 : Essential 16 ⟨30, by omega⟩ := ⟨configOfMask 16 2, by native_decide⟩
theorem essential_n16_k31 : Essential 16 ⟨31, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩
theorem essential_n16_k32 : Essential 16 ⟨32, by omega⟩ := ⟨configOfMask 16 0, by native_decide⟩

-- n=17 (35 cells)
theorem essential_n17_k0 : Essential 17 ⟨0, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k1 : Essential 17 ⟨1, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k2 : Essential 17 ⟨2, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k3 : Essential 17 ⟨3, by omega⟩ := ⟨configOfMask 17 272, by native_decide⟩
theorem essential_n17_k4 : Essential 17 ⟨4, by omega⟩ := ⟨configOfMask 17 256, by native_decide⟩
theorem essential_n17_k5 : Essential 17 ⟨5, by omega⟩ := ⟨configOfMask 17 128, by native_decide⟩
theorem essential_n17_k6 : Essential 17 ⟨6, by omega⟩ := ⟨configOfMask 17 128, by native_decide⟩
theorem essential_n17_k7 : Essential 17 ⟨7, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k8 : Essential 17 ⟨8, by omega⟩ := ⟨configOfMask 17 4, by native_decide⟩
theorem essential_n17_k9 : Essential 17 ⟨9, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k10 : Essential 17 ⟨10, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k11 : Essential 17 ⟨11, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k12 : Essential 17 ⟨12, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k13 : Essential 17 ⟨13, by omega⟩ := ⟨configOfMask 17 4, by native_decide⟩
theorem essential_n17_k14 : Essential 17 ⟨14, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k15 : Essential 17 ⟨15, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k16 : Essential 17 ⟨16, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k17 : Essential 17 ⟨17, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k18 : Essential 17 ⟨18, by omega⟩ := ⟨configOfMask 17 8, by native_decide⟩
theorem essential_n17_k19 : Essential 17 ⟨19, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k20 : Essential 17 ⟨20, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k21 : Essential 17 ⟨21, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k22 : Essential 17 ⟨22, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k23 : Essential 17 ⟨23, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k24 : Essential 17 ⟨24, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k25 : Essential 17 ⟨25, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k26 : Essential 17 ⟨26, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k27 : Essential 17 ⟨27, by omega⟩ := ⟨configOfMask 17 4, by native_decide⟩
theorem essential_n17_k28 : Essential 17 ⟨28, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k29 : Essential 17 ⟨29, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k30 : Essential 17 ⟨30, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k31 : Essential 17 ⟨31, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k32 : Essential 17 ⟨32, by omega⟩ := ⟨configOfMask 17 2, by native_decide⟩
theorem essential_n17_k33 : Essential 17 ⟨33, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩
theorem essential_n17_k34 : Essential 17 ⟨34, by omega⟩ := ⟨configOfMask 17 0, by native_decide⟩

-- n=18 (37 cells)
theorem essential_n18_k0 : Essential 18 ⟨0, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k1 : Essential 18 ⟨1, by omega⟩ := ⟨configOfMask 18 8, by native_decide⟩
theorem essential_n18_k2 : Essential 18 ⟨2, by omega⟩ := ⟨configOfMask 18 8, by native_decide⟩
theorem essential_n18_k3 : Essential 18 ⟨3, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k4 : Essential 18 ⟨4, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k5 : Essential 18 ⟨5, by omega⟩ := ⟨configOfMask 18 128, by native_decide⟩
theorem essential_n18_k6 : Essential 18 ⟨6, by omega⟩ := ⟨configOfMask 18 128, by native_decide⟩
theorem essential_n18_k7 : Essential 18 ⟨7, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k8 : Essential 18 ⟨8, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k9 : Essential 18 ⟨9, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k10 : Essential 18 ⟨10, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k11 : Essential 18 ⟨11, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k12 : Essential 18 ⟨12, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k13 : Essential 18 ⟨13, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k14 : Essential 18 ⟨14, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k15 : Essential 18 ⟨15, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k16 : Essential 18 ⟨16, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k17 : Essential 18 ⟨17, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k18 : Essential 18 ⟨18, by omega⟩ := ⟨configOfMask 18 8, by native_decide⟩
theorem essential_n18_k19 : Essential 18 ⟨19, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k20 : Essential 18 ⟨20, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k21 : Essential 18 ⟨21, by omega⟩ := ⟨configOfMask 18 4, by native_decide⟩
theorem essential_n18_k22 : Essential 18 ⟨22, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k23 : Essential 18 ⟨23, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k24 : Essential 18 ⟨24, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k25 : Essential 18 ⟨25, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k26 : Essential 18 ⟨26, by omega⟩ := ⟨configOfMask 18 8, by native_decide⟩
theorem essential_n18_k27 : Essential 18 ⟨27, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k28 : Essential 18 ⟨28, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k29 : Essential 18 ⟨29, by omega⟩ := ⟨configOfMask 18 12, by native_decide⟩
theorem essential_n18_k30 : Essential 18 ⟨30, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k31 : Essential 18 ⟨31, by omega⟩ := ⟨configOfMask 18 4, by native_decide⟩
theorem essential_n18_k32 : Essential 18 ⟨32, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k33 : Essential 18 ⟨33, by omega⟩ := ⟨configOfMask 18 12, by native_decide⟩
theorem essential_n18_k34 : Essential 18 ⟨34, by omega⟩ := ⟨configOfMask 18 2, by native_decide⟩
theorem essential_n18_k35 : Essential 18 ⟨35, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩
theorem essential_n18_k36 : Essential 18 ⟨36, by omega⟩ := ⟨configOfMask 18 0, by native_decide⟩


-- n=19 (39 cells)
theorem essential_n19_k0 : Essential 19 ⟨0, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k1 : Essential 19 ⟨1, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k2 : Essential 19 ⟨2, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k3 : Essential 19 ⟨3, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k4 : Essential 19 ⟨4, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k5 : Essential 19 ⟨5, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k6 : Essential 19 ⟨6, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k7 : Essential 19 ⟨7, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k8 : Essential 19 ⟨8, by omega⟩ := ⟨configOfMask 19 4, by native_decide⟩
theorem essential_n19_k9 : Essential 19 ⟨9, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k10 : Essential 19 ⟨10, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k11 : Essential 19 ⟨11, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k12 : Essential 19 ⟨12, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k13 : Essential 19 ⟨13, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k14 : Essential 19 ⟨14, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k15 : Essential 19 ⟨15, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k16 : Essential 19 ⟨16, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k17 : Essential 19 ⟨17, by omega⟩ := ⟨configOfMask 19 4, by native_decide⟩
theorem essential_n19_k18 : Essential 19 ⟨18, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k19 : Essential 19 ⟨19, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k20 : Essential 19 ⟨20, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k21 : Essential 19 ⟨21, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k22 : Essential 19 ⟨22, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k23 : Essential 19 ⟨23, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k24 : Essential 19 ⟨24, by omega⟩ := ⟨configOfMask 19 8, by native_decide⟩
theorem essential_n19_k25 : Essential 19 ⟨25, by omega⟩ := ⟨configOfMask 19 16, by native_decide⟩
theorem essential_n19_k26 : Essential 19 ⟨26, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k27 : Essential 19 ⟨27, by omega⟩ := ⟨configOfMask 19 4, by native_decide⟩
theorem essential_n19_k28 : Essential 19 ⟨28, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k29 : Essential 19 ⟨29, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k30 : Essential 19 ⟨30, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k31 : Essential 19 ⟨31, by omega⟩ := ⟨configOfMask 19 4, by native_decide⟩
theorem essential_n19_k32 : Essential 19 ⟨32, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k33 : Essential 19 ⟨33, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k34 : Essential 19 ⟨34, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k35 : Essential 19 ⟨35, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k36 : Essential 19 ⟨36, by omega⟩ := ⟨configOfMask 19 2, by native_decide⟩
theorem essential_n19_k37 : Essential 19 ⟨37, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩
theorem essential_n19_k38 : Essential 19 ⟨38, by omega⟩ := ⟨configOfMask 19 0, by native_decide⟩


-- n=20 (41 cells)
theorem essential_n20_k0 : Essential 20 ⟨0, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k1 : Essential 20 ⟨1, by omega⟩ := ⟨configOfMask 20 64, by native_decide⟩
theorem essential_n20_k2 : Essential 20 ⟨2, by omega⟩ := ⟨configOfMask 20 16, by native_decide⟩
theorem essential_n20_k3 : Essential 20 ⟨3, by omega⟩ := ⟨configOfMask 20 16, by native_decide⟩
theorem essential_n20_k4 : Essential 20 ⟨4, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k5 : Essential 20 ⟨5, by omega⟩ := ⟨configOfMask 20 12, by native_decide⟩
theorem essential_n20_k6 : Essential 20 ⟨6, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k7 : Essential 20 ⟨7, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k8 : Essential 20 ⟨8, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k9 : Essential 20 ⟨9, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k10 : Essential 20 ⟨10, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k11 : Essential 20 ⟨11, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k12 : Essential 20 ⟨12, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k13 : Essential 20 ⟨13, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k14 : Essential 20 ⟨14, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k15 : Essential 20 ⟨15, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k16 : Essential 20 ⟨16, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k17 : Essential 20 ⟨17, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k18 : Essential 20 ⟨18, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k19 : Essential 20 ⟨19, by omega⟩ := ⟨configOfMask 20 4, by native_decide⟩
theorem essential_n20_k20 : Essential 20 ⟨20, by omega⟩ := ⟨configOfMask 20 4, by native_decide⟩
theorem essential_n20_k21 : Essential 20 ⟨21, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k22 : Essential 20 ⟨22, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k23 : Essential 20 ⟨23, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k24 : Essential 20 ⟨24, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k25 : Essential 20 ⟨25, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k26 : Essential 20 ⟨26, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k27 : Essential 20 ⟨27, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k28 : Essential 20 ⟨28, by omega⟩ := ⟨configOfMask 20 8, by native_decide⟩
theorem essential_n20_k29 : Essential 20 ⟨29, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k30 : Essential 20 ⟨30, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k31 : Essential 20 ⟨31, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k32 : Essential 20 ⟨32, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k33 : Essential 20 ⟨33, by omega⟩ := ⟨configOfMask 20 12, by native_decide⟩
theorem essential_n20_k34 : Essential 20 ⟨34, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k35 : Essential 20 ⟨35, by omega⟩ := ⟨configOfMask 20 4, by native_decide⟩
theorem essential_n20_k36 : Essential 20 ⟨36, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k37 : Essential 20 ⟨37, by omega⟩ := ⟨configOfMask 20 12, by native_decide⟩
theorem essential_n20_k38 : Essential 20 ⟨38, by omega⟩ := ⟨configOfMask 20 2, by native_decide⟩
theorem essential_n20_k39 : Essential 20 ⟨39, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩
theorem essential_n20_k40 : Essential 20 ⟨40, by omega⟩ := ⟨configOfMask 20 0, by native_decide⟩


-- n=21 (43 cells)
theorem essential_n21_k0 : Essential 21 ⟨0, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k1 : Essential 21 ⟨1, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k2 : Essential 21 ⟨2, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k3 : Essential 21 ⟨3, by omega⟩ := ⟨configOfMask 21 16, by native_decide⟩
theorem essential_n21_k4 : Essential 21 ⟨4, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k5 : Essential 21 ⟨5, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k6 : Essential 21 ⟨6, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k7 : Essential 21 ⟨7, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k8 : Essential 21 ⟨8, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k9 : Essential 21 ⟨9, by omega⟩ := ⟨configOfMask 21 8, by native_decide⟩
theorem essential_n21_k10 : Essential 21 ⟨10, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k11 : Essential 21 ⟨11, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k12 : Essential 21 ⟨12, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k13 : Essential 21 ⟨13, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k14 : Essential 21 ⟨14, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k15 : Essential 21 ⟨15, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k16 : Essential 21 ⟨16, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k17 : Essential 21 ⟨17, by omega⟩ := ⟨configOfMask 21 4, by native_decide⟩
theorem essential_n21_k18 : Essential 21 ⟨18, by omega⟩ := ⟨configOfMask 21 4, by native_decide⟩
theorem essential_n21_k19 : Essential 21 ⟨19, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k20 : Essential 21 ⟨20, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k21 : Essential 21 ⟨21, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k22 : Essential 21 ⟨22, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k23 : Essential 21 ⟨23, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k24 : Essential 21 ⟨24, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k25 : Essential 21 ⟨25, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k26 : Essential 21 ⟨26, by omega⟩ := ⟨configOfMask 21 16, by native_decide⟩
theorem essential_n21_k27 : Essential 21 ⟨27, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k28 : Essential 21 ⟨28, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k29 : Essential 21 ⟨29, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k30 : Essential 21 ⟨30, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k31 : Essential 21 ⟨31, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k32 : Essential 21 ⟨32, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k33 : Essential 21 ⟨33, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k34 : Essential 21 ⟨34, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k35 : Essential 21 ⟨35, by omega⟩ := ⟨configOfMask 21 4, by native_decide⟩
theorem essential_n21_k36 : Essential 21 ⟨36, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k37 : Essential 21 ⟨37, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k38 : Essential 21 ⟨38, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k39 : Essential 21 ⟨39, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k40 : Essential 21 ⟨40, by omega⟩ := ⟨configOfMask 21 2, by native_decide⟩
theorem essential_n21_k41 : Essential 21 ⟨41, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩
theorem essential_n21_k42 : Essential 21 ⟨42, by omega⟩ := ⟨configOfMask 21 0, by native_decide⟩


-- n=22 (45 cells)
theorem essential_n22_k0 : Essential 22 ⟨0, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k1 : Essential 22 ⟨1, by omega⟩ := ⟨configOfMask 22 8, by native_decide⟩
theorem essential_n22_k2 : Essential 22 ⟨2, by omega⟩ := ⟨configOfMask 22 8, by native_decide⟩
theorem essential_n22_k3 : Essential 22 ⟨3, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k4 : Essential 22 ⟨4, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k5 : Essential 22 ⟨5, by omega⟩ := ⟨configOfMask 22 12, by native_decide⟩
theorem essential_n22_k6 : Essential 22 ⟨6, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k7 : Essential 22 ⟨7, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k8 : Essential 22 ⟨8, by omega⟩ := ⟨configOfMask 22 4, by native_decide⟩
theorem essential_n22_k9 : Essential 22 ⟨9, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k10 : Essential 22 ⟨10, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k11 : Essential 22 ⟨11, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k12 : Essential 22 ⟨12, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k13 : Essential 22 ⟨13, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k14 : Essential 22 ⟨14, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k15 : Essential 22 ⟨15, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k16 : Essential 22 ⟨16, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k17 : Essential 22 ⟨17, by omega⟩ := ⟨configOfMask 22 4, by native_decide⟩
theorem essential_n22_k18 : Essential 22 ⟨18, by omega⟩ := ⟨configOfMask 22 4, by native_decide⟩
theorem essential_n22_k19 : Essential 22 ⟨19, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k20 : Essential 22 ⟨20, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k21 : Essential 22 ⟨21, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k22 : Essential 22 ⟨22, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k23 : Essential 22 ⟨23, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k24 : Essential 22 ⟨24, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k25 : Essential 22 ⟨25, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k26 : Essential 22 ⟨26, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k27 : Essential 22 ⟨27, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k28 : Essential 22 ⟨28, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k29 : Essential 22 ⟨29, by omega⟩ := ⟨configOfMask 22 4, by native_decide⟩
theorem essential_n22_k30 : Essential 22 ⟨30, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k31 : Essential 22 ⟨31, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k32 : Essential 22 ⟨32, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k33 : Essential 22 ⟨33, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k34 : Essential 22 ⟨34, by omega⟩ := ⟨configOfMask 22 8, by native_decide⟩
theorem essential_n22_k35 : Essential 22 ⟨35, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k36 : Essential 22 ⟨36, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k37 : Essential 22 ⟨37, by omega⟩ := ⟨configOfMask 22 12, by native_decide⟩
theorem essential_n22_k38 : Essential 22 ⟨38, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k39 : Essential 22 ⟨39, by omega⟩ := ⟨configOfMask 22 4, by native_decide⟩
theorem essential_n22_k40 : Essential 22 ⟨40, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k41 : Essential 22 ⟨41, by omega⟩ := ⟨configOfMask 22 12, by native_decide⟩
theorem essential_n22_k42 : Essential 22 ⟨42, by omega⟩ := ⟨configOfMask 22 2, by native_decide⟩
theorem essential_n22_k43 : Essential 22 ⟨43, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩
theorem essential_n22_k44 : Essential 22 ⟨44, by omega⟩ := ⟨configOfMask 22 0, by native_decide⟩


-- n=23 (47 cells)
theorem essential_n23_k0 : Essential 23 ⟨0, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k1 : Essential 23 ⟨1, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k2 : Essential 23 ⟨2, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k3 : Essential 23 ⟨3, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k4 : Essential 23 ⟨4, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k5 : Essential 23 ⟨5, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k6 : Essential 23 ⟨6, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k7 : Essential 23 ⟨7, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k8 : Essential 23 ⟨8, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k9 : Essential 23 ⟨9, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k10 : Essential 23 ⟨10, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k11 : Essential 23 ⟨11, by omega⟩ := ⟨configOfMask 23 4, by native_decide⟩
theorem essential_n23_k12 : Essential 23 ⟨12, by omega⟩ := ⟨configOfMask 23 4, by native_decide⟩
theorem essential_n23_k13 : Essential 23 ⟨13, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k14 : Essential 23 ⟨14, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k15 : Essential 23 ⟨15, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k16 : Essential 23 ⟨16, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k17 : Essential 23 ⟨17, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k18 : Essential 23 ⟨18, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k19 : Essential 23 ⟨19, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k20 : Essential 23 ⟨20, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k21 : Essential 23 ⟨21, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k22 : Essential 23 ⟨22, by omega⟩ := ⟨configOfMask 23 4, by native_decide⟩
theorem essential_n23_k23 : Essential 23 ⟨23, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k24 : Essential 23 ⟨24, by omega⟩ := ⟨configOfMask 23 4, by native_decide⟩
theorem essential_n23_k25 : Essential 23 ⟨25, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k26 : Essential 23 ⟨26, by omega⟩ := ⟨configOfMask 23 12, by native_decide⟩
theorem essential_n23_k27 : Essential 23 ⟨27, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k28 : Essential 23 ⟨28, by omega⟩ := ⟨configOfMask 23 16, by native_decide⟩
theorem essential_n23_k29 : Essential 23 ⟨29, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k30 : Essential 23 ⟨30, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k31 : Essential 23 ⟨31, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k32 : Essential 23 ⟨32, by omega⟩ := ⟨configOfMask 23 8, by native_decide⟩
theorem essential_n23_k33 : Essential 23 ⟨33, by omega⟩ := ⟨configOfMask 23 16, by native_decide⟩
theorem essential_n23_k34 : Essential 23 ⟨34, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k35 : Essential 23 ⟨35, by omega⟩ := ⟨configOfMask 23 4, by native_decide⟩
theorem essential_n23_k36 : Essential 23 ⟨36, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k37 : Essential 23 ⟨37, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k38 : Essential 23 ⟨38, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k39 : Essential 23 ⟨39, by omega⟩ := ⟨configOfMask 23 4, by native_decide⟩
theorem essential_n23_k40 : Essential 23 ⟨40, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k41 : Essential 23 ⟨41, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k42 : Essential 23 ⟨42, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k43 : Essential 23 ⟨43, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k44 : Essential 23 ⟨44, by omega⟩ := ⟨configOfMask 23 2, by native_decide⟩
theorem essential_n23_k45 : Essential 23 ⟨45, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩
theorem essential_n23_k46 : Essential 23 ⟨46, by omega⟩ := ⟨configOfMask 23 0, by native_decide⟩


-- n=24 (49 cells)
theorem essential_n24_k0 : Essential 24 ⟨0, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k1 : Essential 24 ⟨1, by omega⟩ := ⟨configOfMask 24 128, by native_decide⟩
theorem essential_n24_k2 : Essential 24 ⟨2, by omega⟩ := ⟨configOfMask 24 128, by native_decide⟩
theorem essential_n24_k3 : Essential 24 ⟨3, by omega⟩ := ⟨configOfMask 24 128, by native_decide⟩
theorem essential_n24_k4 : Essential 24 ⟨4, by omega⟩ := ⟨configOfMask 24 64, by native_decide⟩
theorem essential_n24_k5 : Essential 24 ⟨5, by omega⟩ := ⟨configOfMask 24 64, by native_decide⟩
theorem essential_n24_k6 : Essential 24 ⟨6, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k7 : Essential 24 ⟨7, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k8 : Essential 24 ⟨8, by omega⟩ := ⟨configOfMask 24 4, by native_decide⟩
theorem essential_n24_k9 : Essential 24 ⟨9, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k10 : Essential 24 ⟨10, by omega⟩ := ⟨configOfMask 24 8, by native_decide⟩
theorem essential_n24_k11 : Essential 24 ⟨11, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k12 : Essential 24 ⟨12, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k13 : Essential 24 ⟨13, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k14 : Essential 24 ⟨14, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k15 : Essential 24 ⟨15, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k16 : Essential 24 ⟨16, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k17 : Essential 24 ⟨17, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k18 : Essential 24 ⟨18, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k19 : Essential 24 ⟨19, by omega⟩ := ⟨configOfMask 24 8, by native_decide⟩
theorem essential_n24_k20 : Essential 24 ⟨20, by omega⟩ := ⟨configOfMask 24 8, by native_decide⟩
theorem essential_n24_k21 : Essential 24 ⟨21, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k22 : Essential 24 ⟨22, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k23 : Essential 24 ⟨23, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k24 : Essential 24 ⟨24, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k25 : Essential 24 ⟨25, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k26 : Essential 24 ⟨26, by omega⟩ := ⟨configOfMask 24 18, by native_decide⟩
theorem essential_n24_k27 : Essential 24 ⟨27, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k28 : Essential 24 ⟨28, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k29 : Essential 24 ⟨29, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k30 : Essential 24 ⟨30, by omega⟩ := ⟨configOfMask 24 4, by native_decide⟩
theorem essential_n24_k31 : Essential 24 ⟨31, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k32 : Essential 24 ⟨32, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k33 : Essential 24 ⟨33, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k34 : Essential 24 ⟨34, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k35 : Essential 24 ⟨35, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k36 : Essential 24 ⟨36, by omega⟩ := ⟨configOfMask 24 8, by native_decide⟩
theorem essential_n24_k37 : Essential 24 ⟨37, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k38 : Essential 24 ⟨38, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k39 : Essential 24 ⟨39, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k40 : Essential 24 ⟨40, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k41 : Essential 24 ⟨41, by omega⟩ := ⟨configOfMask 24 12, by native_decide⟩
theorem essential_n24_k42 : Essential 24 ⟨42, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k43 : Essential 24 ⟨43, by omega⟩ := ⟨configOfMask 24 4, by native_decide⟩
theorem essential_n24_k44 : Essential 24 ⟨44, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k45 : Essential 24 ⟨45, by omega⟩ := ⟨configOfMask 24 12, by native_decide⟩
theorem essential_n24_k46 : Essential 24 ⟨46, by omega⟩ := ⟨configOfMask 24 2, by native_decide⟩
theorem essential_n24_k47 : Essential 24 ⟨47, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩
theorem essential_n24_k48 : Essential 24 ⟨48, by omega⟩ := ⟨configOfMask 24 0, by native_decide⟩


-- n=25 (51 cells)
theorem essential_n25_k0 : Essential 25 ⟨0, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k1 : Essential 25 ⟨1, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k2 : Essential 25 ⟨2, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k3 : Essential 25 ⟨3, by omega⟩ := ⟨configOfMask 25 128, by native_decide⟩
theorem essential_n25_k4 : Essential 25 ⟨4, by omega⟩ := ⟨configOfMask 25 64, by native_decide⟩
theorem essential_n25_k5 : Essential 25 ⟨5, by omega⟩ := ⟨configOfMask 25 64, by native_decide⟩
theorem essential_n25_k6 : Essential 25 ⟨6, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k7 : Essential 25 ⟨7, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k8 : Essential 25 ⟨8, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k9 : Essential 25 ⟨9, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k10 : Essential 25 ⟨10, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k11 : Essential 25 ⟨11, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k12 : Essential 25 ⟨12, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k13 : Essential 25 ⟨13, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k14 : Essential 25 ⟨14, by omega⟩ := ⟨configOfMask 25 4, by native_decide⟩
theorem essential_n25_k15 : Essential 25 ⟨15, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k16 : Essential 25 ⟨16, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k17 : Essential 25 ⟨17, by omega⟩ := ⟨configOfMask 25 4, by native_decide⟩
theorem essential_n25_k18 : Essential 25 ⟨18, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k19 : Essential 25 ⟨19, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k20 : Essential 25 ⟨20, by omega⟩ := ⟨configOfMask 25 10, by native_decide⟩
theorem essential_n25_k21 : Essential 25 ⟨21, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k22 : Essential 25 ⟨22, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k23 : Essential 25 ⟨23, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k24 : Essential 25 ⟨24, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k25 : Essential 25 ⟨25, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k26 : Essential 25 ⟨26, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k27 : Essential 25 ⟨27, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k28 : Essential 25 ⟨28, by omega⟩ := ⟨configOfMask 25 8, by native_decide⟩
theorem essential_n25_k29 : Essential 25 ⟨29, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k30 : Essential 25 ⟨30, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k31 : Essential 25 ⟨31, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k32 : Essential 25 ⟨32, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k33 : Essential 25 ⟨33, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k34 : Essential 25 ⟨34, by omega⟩ := ⟨configOfMask 25 16, by native_decide⟩
theorem essential_n25_k35 : Essential 25 ⟨35, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k36 : Essential 25 ⟨36, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k37 : Essential 25 ⟨37, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k38 : Essential 25 ⟨38, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k39 : Essential 25 ⟨39, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k40 : Essential 25 ⟨40, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k41 : Essential 25 ⟨41, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k42 : Essential 25 ⟨42, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k43 : Essential 25 ⟨43, by omega⟩ := ⟨configOfMask 25 4, by native_decide⟩
theorem essential_n25_k44 : Essential 25 ⟨44, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k45 : Essential 25 ⟨45, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k46 : Essential 25 ⟨46, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k47 : Essential 25 ⟨47, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k48 : Essential 25 ⟨48, by omega⟩ := ⟨configOfMask 25 2, by native_decide⟩
theorem essential_n25_k49 : Essential 25 ⟨49, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩
theorem essential_n25_k50 : Essential 25 ⟨50, by omega⟩ := ⟨configOfMask 25 0, by native_decide⟩

-- n=26 (53 cells)
theorem essential_n26_k0 : Essential 26 ⟨0, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k1 : Essential 26 ⟨1, by omega⟩ := ⟨configOfMask 26 8, by native_decide⟩
theorem essential_n26_k2 : Essential 26 ⟨2, by omega⟩ := ⟨configOfMask 26 8, by native_decide⟩
theorem essential_n26_k3 : Essential 26 ⟨3, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k4 : Essential 26 ⟨4, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k5 : Essential 26 ⟨5, by omega⟩ := ⟨configOfMask 26 64, by native_decide⟩
theorem essential_n26_k6 : Essential 26 ⟨6, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k7 : Essential 26 ⟨7, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k8 : Essential 26 ⟨8, by omega⟩ := ⟨configOfMask 26 4, by native_decide⟩
theorem essential_n26_k9 : Essential 26 ⟨9, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k10 : Essential 26 ⟨10, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k11 : Essential 26 ⟨11, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k12 : Essential 26 ⟨12, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k13 : Essential 26 ⟨13, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k14 : Essential 26 ⟨14, by omega⟩ := ⟨configOfMask 26 4, by native_decide⟩
theorem essential_n26_k15 : Essential 26 ⟨15, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k16 : Essential 26 ⟨16, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k17 : Essential 26 ⟨17, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k18 : Essential 26 ⟨18, by omega⟩ := ⟨configOfMask 26 10, by native_decide⟩
theorem essential_n26_k19 : Essential 26 ⟨19, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k20 : Essential 26 ⟨20, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k21 : Essential 26 ⟨21, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k22 : Essential 26 ⟨22, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k23 : Essential 26 ⟨23, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k24 : Essential 26 ⟨24, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k25 : Essential 26 ⟨25, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k26 : Essential 26 ⟨26, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k27 : Essential 26 ⟨27, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k28 : Essential 26 ⟨28, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k29 : Essential 26 ⟨29, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k30 : Essential 26 ⟨30, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k31 : Essential 26 ⟨31, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k32 : Essential 26 ⟨32, by omega⟩ := ⟨configOfMask 26 12, by native_decide⟩
theorem essential_n26_k33 : Essential 26 ⟨33, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k34 : Essential 26 ⟨34, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k35 : Essential 26 ⟨35, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k36 : Essential 26 ⟨36, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k37 : Essential 26 ⟨37, by omega⟩ := ⟨configOfMask 26 4, by native_decide⟩
theorem essential_n26_k38 : Essential 26 ⟨38, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k39 : Essential 26 ⟨39, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k40 : Essential 26 ⟨40, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k41 : Essential 26 ⟨41, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k42 : Essential 26 ⟨42, by omega⟩ := ⟨configOfMask 26 8, by native_decide⟩
theorem essential_n26_k43 : Essential 26 ⟨43, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k44 : Essential 26 ⟨44, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k45 : Essential 26 ⟨45, by omega⟩ := ⟨configOfMask 26 12, by native_decide⟩
theorem essential_n26_k46 : Essential 26 ⟨46, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k47 : Essential 26 ⟨47, by omega⟩ := ⟨configOfMask 26 4, by native_decide⟩
theorem essential_n26_k48 : Essential 26 ⟨48, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k49 : Essential 26 ⟨49, by omega⟩ := ⟨configOfMask 26 12, by native_decide⟩
theorem essential_n26_k50 : Essential 26 ⟨50, by omega⟩ := ⟨configOfMask 26 2, by native_decide⟩
theorem essential_n26_k51 : Essential 26 ⟨51, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩
theorem essential_n26_k52 : Essential 26 ⟨52, by omega⟩ := ⟨configOfMask 26 0, by native_decide⟩


-- n=27 (55 cells)
theorem essential_n27_k0 : Essential 27 ⟨0, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k1 : Essential 27 ⟨1, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k2 : Essential 27 ⟨2, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k3 : Essential 27 ⟨3, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k4 : Essential 27 ⟨4, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k5 : Essential 27 ⟨5, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k6 : Essential 27 ⟨6, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k7 : Essential 27 ⟨7, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k8 : Essential 27 ⟨8, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k9 : Essential 27 ⟨9, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k10 : Essential 27 ⟨10, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k11 : Essential 27 ⟨11, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k12 : Essential 27 ⟨12, by omega⟩ := ⟨configOfMask 27 10, by native_decide⟩
theorem essential_n27_k13 : Essential 27 ⟨13, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k14 : Essential 27 ⟨14, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k15 : Essential 27 ⟨15, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k16 : Essential 27 ⟨16, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k17 : Essential 27 ⟨17, by omega⟩ := ⟨configOfMask 27 4, by native_decide⟩
theorem essential_n27_k18 : Essential 27 ⟨18, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k19 : Essential 27 ⟨19, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k20 : Essential 27 ⟨20, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k21 : Essential 27 ⟨21, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k22 : Essential 27 ⟨22, by omega⟩ := ⟨configOfMask 27 10, by native_decide⟩
theorem essential_n27_k23 : Essential 27 ⟨23, by omega⟩ := ⟨configOfMask 27 10, by native_decide⟩
theorem essential_n27_k24 : Essential 27 ⟨24, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k25 : Essential 27 ⟨25, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k26 : Essential 27 ⟨26, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k27 : Essential 27 ⟨27, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k28 : Essential 27 ⟨28, by omega⟩ := ⟨configOfMask 27 8, by native_decide⟩
theorem essential_n27_k29 : Essential 27 ⟨29, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k30 : Essential 27 ⟨30, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k31 : Essential 27 ⟨31, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k32 : Essential 27 ⟨32, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k33 : Essential 27 ⟨33, by omega⟩ := ⟨configOfMask 27 4, by native_decide⟩
theorem essential_n27_k34 : Essential 27 ⟨34, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k35 : Essential 27 ⟨35, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k36 : Essential 27 ⟨36, by omega⟩ := ⟨configOfMask 27 16, by native_decide⟩
theorem essential_n27_k37 : Essential 27 ⟨37, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k38 : Essential 27 ⟨38, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k39 : Essential 27 ⟨39, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k40 : Essential 27 ⟨40, by omega⟩ := ⟨configOfMask 27 8, by native_decide⟩
theorem essential_n27_k41 : Essential 27 ⟨41, by omega⟩ := ⟨configOfMask 27 16, by native_decide⟩
theorem essential_n27_k42 : Essential 27 ⟨42, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k43 : Essential 27 ⟨43, by omega⟩ := ⟨configOfMask 27 4, by native_decide⟩
theorem essential_n27_k44 : Essential 27 ⟨44, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k45 : Essential 27 ⟨45, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k46 : Essential 27 ⟨46, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k47 : Essential 27 ⟨47, by omega⟩ := ⟨configOfMask 27 4, by native_decide⟩
theorem essential_n27_k48 : Essential 27 ⟨48, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k49 : Essential 27 ⟨49, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k50 : Essential 27 ⟨50, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k51 : Essential 27 ⟨51, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k52 : Essential 27 ⟨52, by omega⟩ := ⟨configOfMask 27 2, by native_decide⟩
theorem essential_n27_k53 : Essential 27 ⟨53, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩
theorem essential_n27_k54 : Essential 27 ⟨54, by omega⟩ := ⟨configOfMask 27 0, by native_decide⟩


-- n=28 (57 cells)
theorem essential_n28_k0 : Essential 28 ⟨0, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k1 : Essential 28 ⟨1, by omega⟩ := ⟨configOfMask 28 64, by native_decide⟩
theorem essential_n28_k2 : Essential 28 ⟨2, by omega⟩ := ⟨configOfMask 28 16, by native_decide⟩
theorem essential_n28_k3 : Essential 28 ⟨3, by omega⟩ := ⟨configOfMask 28 16, by native_decide⟩
theorem essential_n28_k4 : Essential 28 ⟨4, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k5 : Essential 28 ⟨5, by omega⟩ := ⟨configOfMask 28 12, by native_decide⟩
theorem essential_n28_k6 : Essential 28 ⟨6, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k7 : Essential 28 ⟨7, by omega⟩ := ⟨configOfMask 28 8, by native_decide⟩
theorem essential_n28_k8 : Essential 28 ⟨8, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k9 : Essential 28 ⟨9, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k10 : Essential 28 ⟨10, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k11 : Essential 28 ⟨11, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k12 : Essential 28 ⟨12, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k13 : Essential 28 ⟨13, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k14 : Essential 28 ⟨14, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k15 : Essential 28 ⟨15, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k16 : Essential 28 ⟨16, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k17 : Essential 28 ⟨17, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k18 : Essential 28 ⟨18, by omega⟩ := ⟨configOfMask 28 10, by native_decide⟩
theorem essential_n28_k19 : Essential 28 ⟨19, by omega⟩ := ⟨configOfMask 28 4, by native_decide⟩
theorem essential_n28_k20 : Essential 28 ⟨20, by omega⟩ := ⟨configOfMask 28 4, by native_decide⟩
theorem essential_n28_k21 : Essential 28 ⟨21, by omega⟩ := ⟨configOfMask 28 4, by native_decide⟩
theorem essential_n28_k22 : Essential 28 ⟨22, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k23 : Essential 28 ⟨23, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k24 : Essential 28 ⟨24, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k25 : Essential 28 ⟨25, by omega⟩ := ⟨configOfMask 28 8, by native_decide⟩
theorem essential_n28_k26 : Essential 28 ⟨26, by omega⟩ := ⟨configOfMask 28 4, by native_decide⟩
theorem essential_n28_k27 : Essential 28 ⟨27, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k28 : Essential 28 ⟨28, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k29 : Essential 28 ⟨29, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k30 : Essential 28 ⟨30, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k31 : Essential 28 ⟨31, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k32 : Essential 28 ⟨32, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k33 : Essential 28 ⟨33, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k34 : Essential 28 ⟨34, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k35 : Essential 28 ⟨35, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k36 : Essential 28 ⟨36, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k37 : Essential 28 ⟨37, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k38 : Essential 28 ⟨38, by omega⟩ := ⟨configOfMask 28 4, by native_decide⟩
theorem essential_n28_k39 : Essential 28 ⟨39, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k40 : Essential 28 ⟨40, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k41 : Essential 28 ⟨41, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k42 : Essential 28 ⟨42, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k43 : Essential 28 ⟨43, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k44 : Essential 28 ⟨44, by omega⟩ := ⟨configOfMask 28 8, by native_decide⟩
theorem essential_n28_k45 : Essential 28 ⟨45, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k46 : Essential 28 ⟨46, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k47 : Essential 28 ⟨47, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k48 : Essential 28 ⟨48, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k49 : Essential 28 ⟨49, by omega⟩ := ⟨configOfMask 28 12, by native_decide⟩
theorem essential_n28_k50 : Essential 28 ⟨50, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k51 : Essential 28 ⟨51, by omega⟩ := ⟨configOfMask 28 4, by native_decide⟩
theorem essential_n28_k52 : Essential 28 ⟨52, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k53 : Essential 28 ⟨53, by omega⟩ := ⟨configOfMask 28 12, by native_decide⟩
theorem essential_n28_k54 : Essential 28 ⟨54, by omega⟩ := ⟨configOfMask 28 2, by native_decide⟩
theorem essential_n28_k55 : Essential 28 ⟨55, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩
theorem essential_n28_k56 : Essential 28 ⟨56, by omega⟩ := ⟨configOfMask 28 0, by native_decide⟩


-- n=29 (59 cells)
theorem essential_n29_k0 : Essential 29 ⟨0, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k1 : Essential 29 ⟨1, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k2 : Essential 29 ⟨2, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k3 : Essential 29 ⟨3, by omega⟩ := ⟨configOfMask 29 16, by native_decide⟩
theorem essential_n29_k4 : Essential 29 ⟨4, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k5 : Essential 29 ⟨5, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k6 : Essential 29 ⟨6, by omega⟩ := ⟨configOfMask 29 4, by native_decide⟩
theorem essential_n29_k7 : Essential 29 ⟨7, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k8 : Essential 29 ⟨8, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k9 : Essential 29 ⟨9, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k10 : Essential 29 ⟨10, by omega⟩ := ⟨configOfMask 29 10, by native_decide⟩
theorem essential_n29_k11 : Essential 29 ⟨11, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k12 : Essential 29 ⟨12, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k13 : Essential 29 ⟨13, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k14 : Essential 29 ⟨14, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k15 : Essential 29 ⟨15, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k16 : Essential 29 ⟨16, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k17 : Essential 29 ⟨17, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k18 : Essential 29 ⟨18, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k19 : Essential 29 ⟨19, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k20 : Essential 29 ⟨20, by omega⟩ := ⟨configOfMask 29 4, by native_decide⟩
theorem essential_n29_k21 : Essential 29 ⟨21, by omega⟩ := ⟨configOfMask 29 4, by native_decide⟩
theorem essential_n29_k22 : Essential 29 ⟨22, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k23 : Essential 29 ⟨23, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k24 : Essential 29 ⟨24, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k25 : Essential 29 ⟨25, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k26 : Essential 29 ⟨26, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k27 : Essential 29 ⟨27, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k28 : Essential 29 ⟨28, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k29 : Essential 29 ⟨29, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k30 : Essential 29 ⟨30, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k31 : Essential 29 ⟨31, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k32 : Essential 29 ⟨32, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k33 : Essential 29 ⟨33, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k34 : Essential 29 ⟨34, by omega⟩ := ⟨configOfMask 29 4, by native_decide⟩
theorem essential_n29_k35 : Essential 29 ⟨35, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k36 : Essential 29 ⟨36, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k37 : Essential 29 ⟨37, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k38 : Essential 29 ⟨38, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k39 : Essential 29 ⟨39, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k40 : Essential 29 ⟨40, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k41 : Essential 29 ⟨41, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k42 : Essential 29 ⟨42, by omega⟩ := ⟨configOfMask 29 16, by native_decide⟩
theorem essential_n29_k43 : Essential 29 ⟨43, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k44 : Essential 29 ⟨44, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k45 : Essential 29 ⟨45, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k46 : Essential 29 ⟨46, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k47 : Essential 29 ⟨47, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k48 : Essential 29 ⟨48, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k49 : Essential 29 ⟨49, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k50 : Essential 29 ⟨50, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k51 : Essential 29 ⟨51, by omega⟩ := ⟨configOfMask 29 4, by native_decide⟩
theorem essential_n29_k52 : Essential 29 ⟨52, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k53 : Essential 29 ⟨53, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k54 : Essential 29 ⟨54, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k55 : Essential 29 ⟨55, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k56 : Essential 29 ⟨56, by omega⟩ := ⟨configOfMask 29 2, by native_decide⟩
theorem essential_n29_k57 : Essential 29 ⟨57, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩
theorem essential_n29_k58 : Essential 29 ⟨58, by omega⟩ := ⟨configOfMask 29 0, by native_decide⟩


-- n=30 (61 cells)
theorem essential_n30_k0 : Essential 30 ⟨0, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k1 : Essential 30 ⟨1, by omega⟩ := ⟨configOfMask 30 8, by native_decide⟩
theorem essential_n30_k2 : Essential 30 ⟨2, by omega⟩ := ⟨configOfMask 30 8, by native_decide⟩
theorem essential_n30_k3 : Essential 30 ⟨3, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k4 : Essential 30 ⟨4, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k5 : Essential 30 ⟨5, by omega⟩ := ⟨configOfMask 30 12, by native_decide⟩
theorem essential_n30_k6 : Essential 30 ⟨6, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k7 : Essential 30 ⟨7, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k8 : Essential 30 ⟨8, by omega⟩ := ⟨configOfMask 30 12, by native_decide⟩
theorem essential_n30_k9 : Essential 30 ⟨9, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k10 : Essential 30 ⟨10, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k11 : Essential 30 ⟨11, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k12 : Essential 30 ⟨12, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k13 : Essential 30 ⟨13, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k14 : Essential 30 ⟨14, by omega⟩ := ⟨configOfMask 30 4, by native_decide⟩
theorem essential_n30_k15 : Essential 30 ⟨15, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k16 : Essential 30 ⟨16, by omega⟩ := ⟨configOfMask 30 18, by native_decide⟩
theorem essential_n30_k17 : Essential 30 ⟨17, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k18 : Essential 30 ⟨18, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k19 : Essential 30 ⟨19, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k20 : Essential 30 ⟨20, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k21 : Essential 30 ⟨21, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k22 : Essential 30 ⟨22, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k23 : Essential 30 ⟨23, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k24 : Essential 30 ⟨24, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k25 : Essential 30 ⟨25, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k26 : Essential 30 ⟨26, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k27 : Essential 30 ⟨27, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k28 : Essential 30 ⟨28, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k29 : Essential 30 ⟨29, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k30 : Essential 30 ⟨30, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k31 : Essential 30 ⟨31, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k32 : Essential 30 ⟨32, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k33 : Essential 30 ⟨33, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k34 : Essential 30 ⟨34, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k35 : Essential 30 ⟨35, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k36 : Essential 30 ⟨36, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k37 : Essential 30 ⟨37, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k38 : Essential 30 ⟨38, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k39 : Essential 30 ⟨39, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k40 : Essential 30 ⟨40, by omega⟩ := ⟨configOfMask 30 12, by native_decide⟩
theorem essential_n30_k41 : Essential 30 ⟨41, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k42 : Essential 30 ⟨42, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k43 : Essential 30 ⟨43, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k44 : Essential 30 ⟨44, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k45 : Essential 30 ⟨45, by omega⟩ := ⟨configOfMask 30 4, by native_decide⟩
theorem essential_n30_k46 : Essential 30 ⟨46, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k47 : Essential 30 ⟨47, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k48 : Essential 30 ⟨48, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k49 : Essential 30 ⟨49, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k50 : Essential 30 ⟨50, by omega⟩ := ⟨configOfMask 30 8, by native_decide⟩
theorem essential_n30_k51 : Essential 30 ⟨51, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k52 : Essential 30 ⟨52, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k53 : Essential 30 ⟨53, by omega⟩ := ⟨configOfMask 30 12, by native_decide⟩
theorem essential_n30_k54 : Essential 30 ⟨54, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k55 : Essential 30 ⟨55, by omega⟩ := ⟨configOfMask 30 4, by native_decide⟩
theorem essential_n30_k56 : Essential 30 ⟨56, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k57 : Essential 30 ⟨57, by omega⟩ := ⟨configOfMask 30 12, by native_decide⟩
theorem essential_n30_k58 : Essential 30 ⟨58, by omega⟩ := ⟨configOfMask 30 2, by native_decide⟩
theorem essential_n30_k59 : Essential 30 ⟨59, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩
theorem essential_n30_k60 : Essential 30 ⟨60, by omega⟩ := ⟨configOfMask 30 0, by native_decide⟩

-- n=31 (63 cells)
theorem essential_n31_k0 : Essential 31 ⟨0, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k1 : Essential 31 ⟨1, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k2 : Essential 31 ⟨2, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k3 : Essential 31 ⟨3, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k4 : Essential 31 ⟨4, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k5 : Essential 31 ⟨5, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k6 : Essential 31 ⟨6, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k7 : Essential 31 ⟨7, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k8 : Essential 31 ⟨8, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k9 : Essential 31 ⟨9, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k10 : Essential 31 ⟨10, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k11 : Essential 31 ⟨11, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k12 : Essential 31 ⟨12, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k13 : Essential 31 ⟨13, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k14 : Essential 31 ⟨14, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k15 : Essential 31 ⟨15, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k16 : Essential 31 ⟨16, by omega⟩ := ⟨configOfMask 31 8, by native_decide⟩
theorem essential_n31_k17 : Essential 31 ⟨17, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k18 : Essential 31 ⟨18, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k19 : Essential 31 ⟨19, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k20 : Essential 31 ⟨20, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k21 : Essential 31 ⟨21, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k22 : Essential 31 ⟨22, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k23 : Essential 31 ⟨23, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k24 : Essential 31 ⟨24, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k25 : Essential 31 ⟨25, by omega⟩ := ⟨configOfMask 31 8, by native_decide⟩
theorem essential_n31_k26 : Essential 31 ⟨26, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k27 : Essential 31 ⟨27, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k28 : Essential 31 ⟨28, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k29 : Essential 31 ⟨29, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k30 : Essential 31 ⟨30, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k31 : Essential 31 ⟨31, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k32 : Essential 31 ⟨32, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k33 : Essential 31 ⟨33, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k34 : Essential 31 ⟨34, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k35 : Essential 31 ⟨35, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k36 : Essential 31 ⟨36, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k37 : Essential 31 ⟨37, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k38 : Essential 31 ⟨38, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k39 : Essential 31 ⟨39, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k40 : Essential 31 ⟨40, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k41 : Essential 31 ⟨41, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k42 : Essential 31 ⟨42, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k43 : Essential 31 ⟨43, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k44 : Essential 31 ⟨44, by omega⟩ := ⟨configOfMask 31 16, by native_decide⟩
theorem essential_n31_k45 : Essential 31 ⟨45, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k46 : Essential 31 ⟨46, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k47 : Essential 31 ⟨47, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k48 : Essential 31 ⟨48, by omega⟩ := ⟨configOfMask 31 8, by native_decide⟩
theorem essential_n31_k49 : Essential 31 ⟨49, by omega⟩ := ⟨configOfMask 31 16, by native_decide⟩
theorem essential_n31_k50 : Essential 31 ⟨50, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k51 : Essential 31 ⟨51, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k52 : Essential 31 ⟨52, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k53 : Essential 31 ⟨53, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k54 : Essential 31 ⟨54, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k55 : Essential 31 ⟨55, by omega⟩ := ⟨configOfMask 31 4, by native_decide⟩
theorem essential_n31_k56 : Essential 31 ⟨56, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k57 : Essential 31 ⟨57, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k58 : Essential 31 ⟨58, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k59 : Essential 31 ⟨59, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k60 : Essential 31 ⟨60, by omega⟩ := ⟨configOfMask 31 2, by native_decide⟩
theorem essential_n31_k61 : Essential 31 ⟨61, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩
theorem essential_n31_k62 : Essential 31 ⟨62, by omega⟩ := ⟨configOfMask 31 0, by native_decide⟩


-- n=32 (65 cells)
theorem essential_n32_k0 : Essential 32 ⟨0, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k1 : Essential 32 ⟨1, by omega⟩ := ⟨configOfMask 32 3584, by native_decide⟩
theorem essential_n32_k2 : Essential 32 ⟨2, by omega⟩ := ⟨configOfMask 32 1792, by native_decide⟩
theorem essential_n32_k3 : Essential 32 ⟨3, by omega⟩ := ⟨configOfMask 32 1024, by native_decide⟩
theorem essential_n32_k4 : Essential 32 ⟨4, by omega⟩ := ⟨configOfMask 32 512, by native_decide⟩
theorem essential_n32_k5 : Essential 32 ⟨5, by omega⟩ := ⟨configOfMask 32 896, by native_decide⟩
theorem essential_n32_k6 : Essential 32 ⟨6, by omega⟩ := ⟨configOfMask 32 896, by native_decide⟩
theorem essential_n32_k7 : Essential 32 ⟨7, by omega⟩ := ⟨configOfMask 32 512, by native_decide⟩
theorem essential_n32_k8 : Essential 32 ⟨8, by omega⟩ := ⟨configOfMask 32 512, by native_decide⟩
theorem essential_n32_k9 : Essential 32 ⟨9, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k10 : Essential 32 ⟨10, by omega⟩ := ⟨configOfMask 32 8, by native_decide⟩
theorem essential_n32_k11 : Essential 32 ⟨11, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k12 : Essential 32 ⟨12, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k13 : Essential 32 ⟨13, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k14 : Essential 32 ⟨14, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k15 : Essential 32 ⟨15, by omega⟩ := ⟨configOfMask 32 8, by native_decide⟩
theorem essential_n32_k16 : Essential 32 ⟨16, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k17 : Essential 32 ⟨17, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k18 : Essential 32 ⟨18, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k19 : Essential 32 ⟨19, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k20 : Essential 32 ⟨20, by omega⟩ := ⟨configOfMask 32 10, by native_decide⟩
theorem essential_n32_k21 : Essential 32 ⟨21, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k22 : Essential 32 ⟨22, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k23 : Essential 32 ⟨23, by omega⟩ := ⟨configOfMask 32 4, by native_decide⟩
theorem essential_n32_k24 : Essential 32 ⟨24, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k25 : Essential 32 ⟨25, by omega⟩ := ⟨configOfMask 32 8, by native_decide⟩
theorem essential_n32_k26 : Essential 32 ⟨26, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k27 : Essential 32 ⟨27, by omega⟩ := ⟨configOfMask 32 8, by native_decide⟩
theorem essential_n32_k28 : Essential 32 ⟨28, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k29 : Essential 32 ⟨29, by omega⟩ := ⟨configOfMask 32 4, by native_decide⟩
theorem essential_n32_k30 : Essential 32 ⟨30, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k31 : Essential 32 ⟨31, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k32 : Essential 32 ⟨32, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k33 : Essential 32 ⟨33, by omega⟩ := ⟨configOfMask 32 4, by native_decide⟩
theorem essential_n32_k34 : Essential 32 ⟨34, by omega⟩ := ⟨configOfMask 32 4, by native_decide⟩
theorem essential_n32_k35 : Essential 32 ⟨35, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k36 : Essential 32 ⟨36, by omega⟩ := ⟨configOfMask 32 8, by native_decide⟩
theorem essential_n32_k37 : Essential 32 ⟨37, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k38 : Essential 32 ⟨38, by omega⟩ := ⟨configOfMask 32 32, by native_decide⟩
theorem essential_n32_k39 : Essential 32 ⟨39, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k40 : Essential 32 ⟨40, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k41 : Essential 32 ⟨41, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k42 : Essential 32 ⟨42, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k43 : Essential 32 ⟨43, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k44 : Essential 32 ⟨44, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k45 : Essential 32 ⟨45, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k46 : Essential 32 ⟨46, by omega⟩ := ⟨configOfMask 32 4, by native_decide⟩
theorem essential_n32_k47 : Essential 32 ⟨47, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k48 : Essential 32 ⟨48, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k49 : Essential 32 ⟨49, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k50 : Essential 32 ⟨50, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k51 : Essential 32 ⟨51, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k52 : Essential 32 ⟨52, by omega⟩ := ⟨configOfMask 32 8, by native_decide⟩
theorem essential_n32_k53 : Essential 32 ⟨53, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k54 : Essential 32 ⟨54, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k55 : Essential 32 ⟨55, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k56 : Essential 32 ⟨56, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k57 : Essential 32 ⟨57, by omega⟩ := ⟨configOfMask 32 12, by native_decide⟩
theorem essential_n32_k58 : Essential 32 ⟨58, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k59 : Essential 32 ⟨59, by omega⟩ := ⟨configOfMask 32 4, by native_decide⟩
theorem essential_n32_k60 : Essential 32 ⟨60, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k61 : Essential 32 ⟨61, by omega⟩ := ⟨configOfMask 32 12, by native_decide⟩
theorem essential_n32_k62 : Essential 32 ⟨62, by omega⟩ := ⟨configOfMask 32 2, by native_decide⟩
theorem essential_n32_k63 : Essential 32 ⟨63, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩
theorem essential_n32_k64 : Essential 32 ⟨64, by omega⟩ := ⟨configOfMask 32 0, by native_decide⟩


-- n=33 (67 cells)
theorem essential_n33_k0 : Essential 33 ⟨0, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k1 : Essential 33 ⟨1, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k2 : Essential 33 ⟨2, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k3 : Essential 33 ⟨3, by omega⟩ := ⟨configOfMask 33 1024, by native_decide⟩
theorem essential_n33_k4 : Essential 33 ⟨4, by omega⟩ := ⟨configOfMask 33 512, by native_decide⟩
theorem essential_n33_k5 : Essential 33 ⟨5, by omega⟩ := ⟨configOfMask 33 896, by native_decide⟩
theorem essential_n33_k6 : Essential 33 ⟨6, by omega⟩ := ⟨configOfMask 33 896, by native_decide⟩
theorem essential_n33_k7 : Essential 33 ⟨7, by omega⟩ := ⟨configOfMask 33 512, by native_decide⟩
theorem essential_n33_k8 : Essential 33 ⟨8, by omega⟩ := ⟨configOfMask 33 512, by native_decide⟩
theorem essential_n33_k9 : Essential 33 ⟨9, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k10 : Essential 33 ⟨10, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k11 : Essential 33 ⟨11, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k12 : Essential 33 ⟨12, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k13 : Essential 33 ⟨13, by omega⟩ := ⟨configOfMask 33 4, by native_decide⟩
theorem essential_n33_k14 : Essential 33 ⟨14, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k15 : Essential 33 ⟨15, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k16 : Essential 33 ⟨16, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k17 : Essential 33 ⟨17, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k18 : Essential 33 ⟨18, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k19 : Essential 33 ⟨19, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k20 : Essential 33 ⟨20, by omega⟩ := ⟨configOfMask 33 8, by native_decide⟩
theorem essential_n33_k21 : Essential 33 ⟨21, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k22 : Essential 33 ⟨22, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k23 : Essential 33 ⟨23, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k24 : Essential 33 ⟨24, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k25 : Essential 33 ⟨25, by omega⟩ := ⟨configOfMask 33 8, by native_decide⟩
theorem essential_n33_k26 : Essential 33 ⟨26, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k27 : Essential 33 ⟨27, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k28 : Essential 33 ⟨28, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k29 : Essential 33 ⟨29, by omega⟩ := ⟨configOfMask 33 4, by native_decide⟩
theorem essential_n33_k30 : Essential 33 ⟨30, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k31 : Essential 33 ⟨31, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k32 : Essential 33 ⟨32, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k33 : Essential 33 ⟨33, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k34 : Essential 33 ⟨34, by omega⟩ := ⟨configOfMask 33 4, by native_decide⟩
theorem essential_n33_k35 : Essential 33 ⟨35, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k36 : Essential 33 ⟨36, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k37 : Essential 33 ⟨37, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k38 : Essential 33 ⟨38, by omega⟩ := ⟨configOfMask 33 36, by native_decide⟩
theorem essential_n33_k39 : Essential 33 ⟨39, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k40 : Essential 33 ⟨40, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k41 : Essential 33 ⟨41, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k42 : Essential 33 ⟨42, by omega⟩ := ⟨configOfMask 33 4, by native_decide⟩
theorem essential_n33_k43 : Essential 33 ⟨43, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k44 : Essential 33 ⟨44, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k45 : Essential 33 ⟨45, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k46 : Essential 33 ⟨46, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k47 : Essential 33 ⟨47, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k48 : Essential 33 ⟨48, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k49 : Essential 33 ⟨49, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k50 : Essential 33 ⟨50, by omega⟩ := ⟨configOfMask 33 16, by native_decide⟩
theorem essential_n33_k51 : Essential 33 ⟨51, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k52 : Essential 33 ⟨52, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k53 : Essential 33 ⟨53, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k54 : Essential 33 ⟨54, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k55 : Essential 33 ⟨55, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k56 : Essential 33 ⟨56, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k57 : Essential 33 ⟨57, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k58 : Essential 33 ⟨58, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k59 : Essential 33 ⟨59, by omega⟩ := ⟨configOfMask 33 4, by native_decide⟩
theorem essential_n33_k60 : Essential 33 ⟨60, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k61 : Essential 33 ⟨61, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k62 : Essential 33 ⟨62, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k63 : Essential 33 ⟨63, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k64 : Essential 33 ⟨64, by omega⟩ := ⟨configOfMask 33 2, by native_decide⟩
theorem essential_n33_k65 : Essential 33 ⟨65, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩
theorem essential_n33_k66 : Essential 33 ⟨66, by omega⟩ := ⟨configOfMask 33 0, by native_decide⟩


-- n=34 (69 cells)
theorem essential_n34_k0 : Essential 34 ⟨0, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k1 : Essential 34 ⟨1, by omega⟩ := ⟨configOfMask 34 8, by native_decide⟩
theorem essential_n34_k2 : Essential 34 ⟨2, by omega⟩ := ⟨configOfMask 34 8, by native_decide⟩
theorem essential_n34_k3 : Essential 34 ⟨3, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k4 : Essential 34 ⟨4, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k5 : Essential 34 ⟨5, by omega⟩ := ⟨configOfMask 34 896, by native_decide⟩
theorem essential_n34_k6 : Essential 34 ⟨6, by omega⟩ := ⟨configOfMask 34 896, by native_decide⟩
theorem essential_n34_k7 : Essential 34 ⟨7, by omega⟩ := ⟨configOfMask 34 512, by native_decide⟩
theorem essential_n34_k8 : Essential 34 ⟨8, by omega⟩ := ⟨configOfMask 34 512, by native_decide⟩
theorem essential_n34_k9 : Essential 34 ⟨9, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k10 : Essential 34 ⟨10, by omega⟩ := ⟨configOfMask 34 16, by native_decide⟩
theorem essential_n34_k11 : Essential 34 ⟨11, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k12 : Essential 34 ⟨12, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k13 : Essential 34 ⟨13, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k14 : Essential 34 ⟨14, by omega⟩ := ⟨configOfMask 34 12, by native_decide⟩
theorem essential_n34_k15 : Essential 34 ⟨15, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k16 : Essential 34 ⟨16, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k17 : Essential 34 ⟨17, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k18 : Essential 34 ⟨18, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k19 : Essential 34 ⟨19, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k20 : Essential 34 ⟨20, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k21 : Essential 34 ⟨21, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k22 : Essential 34 ⟨22, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k23 : Essential 34 ⟨23, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k24 : Essential 34 ⟨24, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k25 : Essential 34 ⟨25, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k26 : Essential 34 ⟨26, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k27 : Essential 34 ⟨27, by omega⟩ := ⟨configOfMask 34 10, by native_decide⟩
theorem essential_n34_k28 : Essential 34 ⟨28, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k29 : Essential 34 ⟨29, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k30 : Essential 34 ⟨30, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k31 : Essential 34 ⟨31, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k32 : Essential 34 ⟨32, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k33 : Essential 34 ⟨33, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k34 : Essential 34 ⟨34, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k35 : Essential 34 ⟨35, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k36 : Essential 34 ⟨36, by omega⟩ := ⟨configOfMask 34 8, by native_decide⟩
theorem essential_n34_k37 : Essential 34 ⟨37, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k38 : Essential 34 ⟨38, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k39 : Essential 34 ⟨39, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k40 : Essential 34 ⟨40, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k41 : Essential 34 ⟨41, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k42 : Essential 34 ⟨42, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k43 : Essential 34 ⟨43, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k44 : Essential 34 ⟨44, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k45 : Essential 34 ⟨45, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k46 : Essential 34 ⟨46, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k47 : Essential 34 ⟨47, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k48 : Essential 34 ⟨48, by omega⟩ := ⟨configOfMask 34 12, by native_decide⟩
theorem essential_n34_k49 : Essential 34 ⟨49, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k50 : Essential 34 ⟨50, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k51 : Essential 34 ⟨51, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k52 : Essential 34 ⟨52, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k53 : Essential 34 ⟨53, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k54 : Essential 34 ⟨54, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k55 : Essential 34 ⟨55, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k56 : Essential 34 ⟨56, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k57 : Essential 34 ⟨57, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k58 : Essential 34 ⟨58, by omega⟩ := ⟨configOfMask 34 8, by native_decide⟩
theorem essential_n34_k59 : Essential 34 ⟨59, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k60 : Essential 34 ⟨60, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k61 : Essential 34 ⟨61, by omega⟩ := ⟨configOfMask 34 12, by native_decide⟩
theorem essential_n34_k62 : Essential 34 ⟨62, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k63 : Essential 34 ⟨63, by omega⟩ := ⟨configOfMask 34 4, by native_decide⟩
theorem essential_n34_k64 : Essential 34 ⟨64, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k65 : Essential 34 ⟨65, by omega⟩ := ⟨configOfMask 34 12, by native_decide⟩
theorem essential_n34_k66 : Essential 34 ⟨66, by omega⟩ := ⟨configOfMask 34 2, by native_decide⟩
theorem essential_n34_k67 : Essential 34 ⟨67, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩
theorem essential_n34_k68 : Essential 34 ⟨68, by omega⟩ := ⟨configOfMask 34 0, by native_decide⟩


-- n=35 (71 cells)
theorem essential_n35_k0 : Essential 35 ⟨0, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k1 : Essential 35 ⟨1, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k2 : Essential 35 ⟨2, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k3 : Essential 35 ⟨3, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k4 : Essential 35 ⟨4, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k5 : Essential 35 ⟨5, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k6 : Essential 35 ⟨6, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k7 : Essential 35 ⟨7, by omega⟩ := ⟨configOfMask 35 512, by native_decide⟩
theorem essential_n35_k8 : Essential 35 ⟨8, by omega⟩ := ⟨configOfMask 35 512, by native_decide⟩
theorem essential_n35_k9 : Essential 35 ⟨9, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k10 : Essential 35 ⟨10, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k11 : Essential 35 ⟨11, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k12 : Essential 35 ⟨12, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k13 : Essential 35 ⟨13, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k14 : Essential 35 ⟨14, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k15 : Essential 35 ⟨15, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k16 : Essential 35 ⟨16, by omega⟩ := ⟨configOfMask 35 4, by native_decide⟩
theorem essential_n35_k17 : Essential 35 ⟨17, by omega⟩ := ⟨configOfMask 35 4, by native_decide⟩
theorem essential_n35_k18 : Essential 35 ⟨18, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k19 : Essential 35 ⟨19, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k20 : Essential 35 ⟨20, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k21 : Essential 35 ⟨21, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k22 : Essential 35 ⟨22, by omega⟩ := ⟨configOfMask 35 10, by native_decide⟩
theorem essential_n35_k23 : Essential 35 ⟨23, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k24 : Essential 35 ⟨24, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k25 : Essential 35 ⟨25, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k26 : Essential 35 ⟨26, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k27 : Essential 35 ⟨27, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k28 : Essential 35 ⟨28, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k29 : Essential 35 ⟨29, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k30 : Essential 35 ⟨30, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k31 : Essential 35 ⟨31, by omega⟩ := ⟨configOfMask 35 10, by native_decide⟩
theorem essential_n35_k32 : Essential 35 ⟨32, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k33 : Essential 35 ⟨33, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k34 : Essential 35 ⟨34, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k35 : Essential 35 ⟨35, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k36 : Essential 35 ⟨36, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k37 : Essential 35 ⟨37, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k38 : Essential 35 ⟨38, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k39 : Essential 35 ⟨39, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k40 : Essential 35 ⟨40, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k41 : Essential 35 ⟨41, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k42 : Essential 35 ⟨42, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k43 : Essential 35 ⟨43, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k44 : Essential 35 ⟨44, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k45 : Essential 35 ⟨45, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k46 : Essential 35 ⟨46, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k47 : Essential 35 ⟨47, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k48 : Essential 35 ⟨48, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k49 : Essential 35 ⟨49, by omega⟩ := ⟨configOfMask 35 4, by native_decide⟩
theorem essential_n35_k50 : Essential 35 ⟨50, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k51 : Essential 35 ⟨51, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k52 : Essential 35 ⟨52, by omega⟩ := ⟨configOfMask 35 16, by native_decide⟩
theorem essential_n35_k53 : Essential 35 ⟨53, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k54 : Essential 35 ⟨54, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k55 : Essential 35 ⟨55, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k56 : Essential 35 ⟨56, by omega⟩ := ⟨configOfMask 35 8, by native_decide⟩
theorem essential_n35_k57 : Essential 35 ⟨57, by omega⟩ := ⟨configOfMask 35 16, by native_decide⟩
theorem essential_n35_k58 : Essential 35 ⟨58, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k59 : Essential 35 ⟨59, by omega⟩ := ⟨configOfMask 35 4, by native_decide⟩
theorem essential_n35_k60 : Essential 35 ⟨60, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k61 : Essential 35 ⟨61, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k62 : Essential 35 ⟨62, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k63 : Essential 35 ⟨63, by omega⟩ := ⟨configOfMask 35 4, by native_decide⟩
theorem essential_n35_k64 : Essential 35 ⟨64, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k65 : Essential 35 ⟨65, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k66 : Essential 35 ⟨66, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k67 : Essential 35 ⟨67, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k68 : Essential 35 ⟨68, by omega⟩ := ⟨configOfMask 35 2, by native_decide⟩
theorem essential_n35_k69 : Essential 35 ⟨69, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩
theorem essential_n35_k70 : Essential 35 ⟨70, by omega⟩ := ⟨configOfMask 35 0, by native_decide⟩


-- n=36 (73 cells)
theorem essential_n36_k0 : Essential 36 ⟨0, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k1 : Essential 36 ⟨1, by omega⟩ := ⟨configOfMask 36 64, by native_decide⟩
theorem essential_n36_k2 : Essential 36 ⟨2, by omega⟩ := ⟨configOfMask 36 16, by native_decide⟩
theorem essential_n36_k3 : Essential 36 ⟨3, by omega⟩ := ⟨configOfMask 36 16, by native_decide⟩
theorem essential_n36_k4 : Essential 36 ⟨4, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k5 : Essential 36 ⟨5, by omega⟩ := ⟨configOfMask 36 12, by native_decide⟩
theorem essential_n36_k6 : Essential 36 ⟨6, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k7 : Essential 36 ⟨7, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k8 : Essential 36 ⟨8, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k9 : Essential 36 ⟨9, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k10 : Essential 36 ⟨10, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k11 : Essential 36 ⟨11, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k12 : Essential 36 ⟨12, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k13 : Essential 36 ⟨13, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k14 : Essential 36 ⟨14, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k15 : Essential 36 ⟨15, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k16 : Essential 36 ⟨16, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k17 : Essential 36 ⟨17, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k18 : Essential 36 ⟨18, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k19 : Essential 36 ⟨19, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k20 : Essential 36 ⟨20, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k21 : Essential 36 ⟨21, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k22 : Essential 36 ⟨22, by omega⟩ := ⟨configOfMask 36 18, by native_decide⟩
theorem essential_n36_k23 : Essential 36 ⟨23, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k24 : Essential 36 ⟨24, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k25 : Essential 36 ⟨25, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k26 : Essential 36 ⟨26, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k27 : Essential 36 ⟨27, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k28 : Essential 36 ⟨28, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k29 : Essential 36 ⟨29, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k30 : Essential 36 ⟨30, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k31 : Essential 36 ⟨31, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k32 : Essential 36 ⟨32, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k33 : Essential 36 ⟨33, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k34 : Essential 36 ⟨34, by omega⟩ := ⟨configOfMask 36 16, by native_decide⟩
theorem essential_n36_k35 : Essential 36 ⟨35, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k36 : Essential 36 ⟨36, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k37 : Essential 36 ⟨37, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k38 : Essential 36 ⟨38, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k39 : Essential 36 ⟨39, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k40 : Essential 36 ⟨40, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k41 : Essential 36 ⟨41, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k42 : Essential 36 ⟨42, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k43 : Essential 36 ⟨43, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k44 : Essential 36 ⟨44, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k45 : Essential 36 ⟨45, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k46 : Essential 36 ⟨46, by omega⟩ := ⟨configOfMask 36 34, by native_decide⟩
theorem essential_n36_k47 : Essential 36 ⟨47, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k48 : Essential 36 ⟨48, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k49 : Essential 36 ⟨49, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k50 : Essential 36 ⟨50, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k51 : Essential 36 ⟨51, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k52 : Essential 36 ⟨52, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k53 : Essential 36 ⟨53, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k54 : Essential 36 ⟨54, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k55 : Essential 36 ⟨55, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k56 : Essential 36 ⟨56, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k57 : Essential 36 ⟨57, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k58 : Essential 36 ⟨58, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k59 : Essential 36 ⟨59, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k60 : Essential 36 ⟨60, by omega⟩ := ⟨configOfMask 36 8, by native_decide⟩
theorem essential_n36_k61 : Essential 36 ⟨61, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k62 : Essential 36 ⟨62, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k63 : Essential 36 ⟨63, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k64 : Essential 36 ⟨64, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k65 : Essential 36 ⟨65, by omega⟩ := ⟨configOfMask 36 12, by native_decide⟩
theorem essential_n36_k66 : Essential 36 ⟨66, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k67 : Essential 36 ⟨67, by omega⟩ := ⟨configOfMask 36 4, by native_decide⟩
theorem essential_n36_k68 : Essential 36 ⟨68, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k69 : Essential 36 ⟨69, by omega⟩ := ⟨configOfMask 36 12, by native_decide⟩
theorem essential_n36_k70 : Essential 36 ⟨70, by omega⟩ := ⟨configOfMask 36 2, by native_decide⟩
theorem essential_n36_k71 : Essential 36 ⟨71, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩
theorem essential_n36_k72 : Essential 36 ⟨72, by omega⟩ := ⟨configOfMask 36 0, by native_decide⟩


-- n=37 (75 cells)
theorem essential_n37_k0 : Essential 37 ⟨0, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k1 : Essential 37 ⟨1, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k2 : Essential 37 ⟨2, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k3 : Essential 37 ⟨3, by omega⟩ := ⟨configOfMask 37 16, by native_decide⟩
theorem essential_n37_k4 : Essential 37 ⟨4, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k5 : Essential 37 ⟨5, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k6 : Essential 37 ⟨6, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k7 : Essential 37 ⟨7, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k8 : Essential 37 ⟨8, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k9 : Essential 37 ⟨9, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k10 : Essential 37 ⟨10, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k11 : Essential 37 ⟨11, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k12 : Essential 37 ⟨12, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k13 : Essential 37 ⟨13, by omega⟩ := ⟨configOfMask 37 8, by native_decide⟩
theorem essential_n37_k14 : Essential 37 ⟨14, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k15 : Essential 37 ⟨15, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k16 : Essential 37 ⟨16, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k17 : Essential 37 ⟨17, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k18 : Essential 37 ⟨18, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k19 : Essential 37 ⟨19, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k20 : Essential 37 ⟨20, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k21 : Essential 37 ⟨21, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k22 : Essential 37 ⟨22, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k23 : Essential 37 ⟨23, by omega⟩ := ⟨configOfMask 37 4, by native_decide⟩
theorem essential_n37_k24 : Essential 37 ⟨24, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k25 : Essential 37 ⟨25, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k26 : Essential 37 ⟨26, by omega⟩ := ⟨configOfMask 37 4, by native_decide⟩
theorem essential_n37_k27 : Essential 37 ⟨27, by omega⟩ := ⟨configOfMask 37 10, by native_decide⟩
theorem essential_n37_k28 : Essential 37 ⟨28, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k29 : Essential 37 ⟨29, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k30 : Essential 37 ⟨30, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k31 : Essential 37 ⟨31, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k32 : Essential 37 ⟨32, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k33 : Essential 37 ⟨33, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k34 : Essential 37 ⟨34, by omega⟩ := ⟨configOfMask 37 8, by native_decide⟩
theorem essential_n37_k35 : Essential 37 ⟨35, by omega⟩ := ⟨configOfMask 37 8, by native_decide⟩
theorem essential_n37_k36 : Essential 37 ⟨36, by omega⟩ := ⟨configOfMask 37 8, by native_decide⟩
theorem essential_n37_k37 : Essential 37 ⟨37, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k38 : Essential 37 ⟨38, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k39 : Essential 37 ⟨39, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k40 : Essential 37 ⟨40, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k41 : Essential 37 ⟨41, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k42 : Essential 37 ⟨42, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k43 : Essential 37 ⟨43, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k44 : Essential 37 ⟨44, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k45 : Essential 37 ⟨45, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k46 : Essential 37 ⟨46, by omega⟩ := ⟨configOfMask 37 36, by native_decide⟩
theorem essential_n37_k47 : Essential 37 ⟨47, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k48 : Essential 37 ⟨48, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k49 : Essential 37 ⟨49, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k50 : Essential 37 ⟨50, by omega⟩ := ⟨configOfMask 37 4, by native_decide⟩
theorem essential_n37_k51 : Essential 37 ⟨51, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k52 : Essential 37 ⟨52, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k53 : Essential 37 ⟨53, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k54 : Essential 37 ⟨54, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k55 : Essential 37 ⟨55, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k56 : Essential 37 ⟨56, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k57 : Essential 37 ⟨57, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k58 : Essential 37 ⟨58, by omega⟩ := ⟨configOfMask 37 16, by native_decide⟩
theorem essential_n37_k59 : Essential 37 ⟨59, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k60 : Essential 37 ⟨60, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k61 : Essential 37 ⟨61, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k62 : Essential 37 ⟨62, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k63 : Essential 37 ⟨63, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k64 : Essential 37 ⟨64, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k65 : Essential 37 ⟨65, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k66 : Essential 37 ⟨66, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k67 : Essential 37 ⟨67, by omega⟩ := ⟨configOfMask 37 4, by native_decide⟩
theorem essential_n37_k68 : Essential 37 ⟨68, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k69 : Essential 37 ⟨69, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k70 : Essential 37 ⟨70, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k71 : Essential 37 ⟨71, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k72 : Essential 37 ⟨72, by omega⟩ := ⟨configOfMask 37 2, by native_decide⟩
theorem essential_n37_k73 : Essential 37 ⟨73, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩
theorem essential_n37_k74 : Essential 37 ⟨74, by omega⟩ := ⟨configOfMask 37 0, by native_decide⟩


-- n=38 (77 cells)
theorem essential_n38_k0 : Essential 38 ⟨0, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k1 : Essential 38 ⟨1, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k2 : Essential 38 ⟨2, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k3 : Essential 38 ⟨3, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k4 : Essential 38 ⟨4, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k5 : Essential 38 ⟨5, by omega⟩ := ⟨configOfMask 38 12, by native_decide⟩
theorem essential_n38_k6 : Essential 38 ⟨6, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k7 : Essential 38 ⟨7, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k8 : Essential 38 ⟨8, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k9 : Essential 38 ⟨9, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k10 : Essential 38 ⟨10, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k11 : Essential 38 ⟨11, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k12 : Essential 38 ⟨12, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k13 : Essential 38 ⟨13, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k14 : Essential 38 ⟨14, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k15 : Essential 38 ⟨15, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k16 : Essential 38 ⟨16, by omega⟩ := ⟨configOfMask 38 16, by native_decide⟩
theorem essential_n38_k17 : Essential 38 ⟨17, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k18 : Essential 38 ⟨18, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k19 : Essential 38 ⟨19, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k20 : Essential 38 ⟨20, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k21 : Essential 38 ⟨21, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k22 : Essential 38 ⟨22, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k23 : Essential 38 ⟨23, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k24 : Essential 38 ⟨24, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k25 : Essential 38 ⟨25, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k26 : Essential 38 ⟨26, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k27 : Essential 38 ⟨27, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k28 : Essential 38 ⟨28, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k29 : Essential 38 ⟨29, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k30 : Essential 38 ⟨30, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k31 : Essential 38 ⟨31, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k32 : Essential 38 ⟨32, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k33 : Essential 38 ⟨33, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k34 : Essential 38 ⟨34, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k35 : Essential 38 ⟨35, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k36 : Essential 38 ⟨36, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k37 : Essential 38 ⟨37, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k38 : Essential 38 ⟨38, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k39 : Essential 38 ⟨39, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k40 : Essential 38 ⟨40, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k41 : Essential 38 ⟨41, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k42 : Essential 38 ⟨42, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k43 : Essential 38 ⟨43, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k44 : Essential 38 ⟨44, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k45 : Essential 38 ⟨45, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k46 : Essential 38 ⟨46, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k47 : Essential 38 ⟨47, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k48 : Essential 38 ⟨48, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k49 : Essential 38 ⟨49, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k50 : Essential 38 ⟨50, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k51 : Essential 38 ⟨51, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k52 : Essential 38 ⟨52, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k53 : Essential 38 ⟨53, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k54 : Essential 38 ⟨54, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k55 : Essential 38 ⟨55, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k56 : Essential 38 ⟨56, by omega⟩ := ⟨configOfMask 38 12, by native_decide⟩
theorem essential_n38_k57 : Essential 38 ⟨57, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k58 : Essential 38 ⟨58, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k59 : Essential 38 ⟨59, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k60 : Essential 38 ⟨60, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k61 : Essential 38 ⟨61, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k62 : Essential 38 ⟨62, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k63 : Essential 38 ⟨63, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k64 : Essential 38 ⟨64, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k65 : Essential 38 ⟨65, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k66 : Essential 38 ⟨66, by omega⟩ := ⟨configOfMask 38 8, by native_decide⟩
theorem essential_n38_k67 : Essential 38 ⟨67, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k68 : Essential 38 ⟨68, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k69 : Essential 38 ⟨69, by omega⟩ := ⟨configOfMask 38 12, by native_decide⟩
theorem essential_n38_k70 : Essential 38 ⟨70, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k71 : Essential 38 ⟨71, by omega⟩ := ⟨configOfMask 38 4, by native_decide⟩
theorem essential_n38_k72 : Essential 38 ⟨72, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k73 : Essential 38 ⟨73, by omega⟩ := ⟨configOfMask 38 12, by native_decide⟩
theorem essential_n38_k74 : Essential 38 ⟨74, by omega⟩ := ⟨configOfMask 38 2, by native_decide⟩
theorem essential_n38_k75 : Essential 38 ⟨75, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩
theorem essential_n38_k76 : Essential 38 ⟨76, by omega⟩ := ⟨configOfMask 38 0, by native_decide⟩


-- n=39 (79 cells)
theorem essential_n39_k0 : Essential 39 ⟨0, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k1 : Essential 39 ⟨1, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k2 : Essential 39 ⟨2, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k3 : Essential 39 ⟨3, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k4 : Essential 39 ⟨4, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k5 : Essential 39 ⟨5, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k6 : Essential 39 ⟨6, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k7 : Essential 39 ⟨7, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k8 : Essential 39 ⟨8, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k9 : Essential 39 ⟨9, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k10 : Essential 39 ⟨10, by omega⟩ := ⟨configOfMask 39 8, by native_decide⟩
theorem essential_n39_k11 : Essential 39 ⟨11, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k12 : Essential 39 ⟨12, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k13 : Essential 39 ⟨13, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k14 : Essential 39 ⟨14, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k15 : Essential 39 ⟨15, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k16 : Essential 39 ⟨16, by omega⟩ := ⟨configOfMask 39 8, by native_decide⟩
theorem essential_n39_k17 : Essential 39 ⟨17, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k18 : Essential 39 ⟨18, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k19 : Essential 39 ⟨19, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k20 : Essential 39 ⟨20, by omega⟩ := ⟨configOfMask 39 12, by native_decide⟩
theorem essential_n39_k21 : Essential 39 ⟨21, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k22 : Essential 39 ⟨22, by omega⟩ := ⟨configOfMask 39 16, by native_decide⟩
theorem essential_n39_k23 : Essential 39 ⟨23, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k24 : Essential 39 ⟨24, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k25 : Essential 39 ⟨25, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k26 : Essential 39 ⟨26, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k27 : Essential 39 ⟨27, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k28 : Essential 39 ⟨28, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k29 : Essential 39 ⟨29, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k30 : Essential 39 ⟨30, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k31 : Essential 39 ⟨31, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k32 : Essential 39 ⟨32, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k33 : Essential 39 ⟨33, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k34 : Essential 39 ⟨34, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k35 : Essential 39 ⟨35, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k36 : Essential 39 ⟨36, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k37 : Essential 39 ⟨37, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k38 : Essential 39 ⟨38, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k39 : Essential 39 ⟨39, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k40 : Essential 39 ⟨40, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k41 : Essential 39 ⟨41, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k42 : Essential 39 ⟨42, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k43 : Essential 39 ⟨43, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k44 : Essential 39 ⟨44, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k45 : Essential 39 ⟨45, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k46 : Essential 39 ⟨46, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k47 : Essential 39 ⟨47, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k48 : Essential 39 ⟨48, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k49 : Essential 39 ⟨49, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k50 : Essential 39 ⟨50, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k51 : Essential 39 ⟨51, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k52 : Essential 39 ⟨52, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k53 : Essential 39 ⟨53, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k54 : Essential 39 ⟨54, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k55 : Essential 39 ⟨55, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k56 : Essential 39 ⟨56, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k57 : Essential 39 ⟨57, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k58 : Essential 39 ⟨58, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k59 : Essential 39 ⟨59, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k60 : Essential 39 ⟨60, by omega⟩ := ⟨configOfMask 39 16, by native_decide⟩
theorem essential_n39_k61 : Essential 39 ⟨61, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k62 : Essential 39 ⟨62, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k63 : Essential 39 ⟨63, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k64 : Essential 39 ⟨64, by omega⟩ := ⟨configOfMask 39 8, by native_decide⟩
theorem essential_n39_k65 : Essential 39 ⟨65, by omega⟩ := ⟨configOfMask 39 16, by native_decide⟩
theorem essential_n39_k66 : Essential 39 ⟨66, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k67 : Essential 39 ⟨67, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k68 : Essential 39 ⟨68, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k69 : Essential 39 ⟨69, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k70 : Essential 39 ⟨70, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k71 : Essential 39 ⟨71, by omega⟩ := ⟨configOfMask 39 4, by native_decide⟩
theorem essential_n39_k72 : Essential 39 ⟨72, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k73 : Essential 39 ⟨73, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k74 : Essential 39 ⟨74, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k75 : Essential 39 ⟨75, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k76 : Essential 39 ⟨76, by omega⟩ := ⟨configOfMask 39 2, by native_decide⟩
theorem essential_n39_k77 : Essential 39 ⟨77, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩
theorem essential_n39_k78 : Essential 39 ⟨78, by omega⟩ := ⟨configOfMask 39 0, by native_decide⟩


-- n=40 (81 cells)
theorem essential_n40_k0 : Essential 40 ⟨0, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k1 : Essential 40 ⟨1, by omega⟩ := ⟨configOfMask 40 128, by native_decide⟩
theorem essential_n40_k2 : Essential 40 ⟨2, by omega⟩ := ⟨configOfMask 40 128, by native_decide⟩
theorem essential_n40_k3 : Essential 40 ⟨3, by omega⟩ := ⟨configOfMask 40 128, by native_decide⟩
theorem essential_n40_k4 : Essential 40 ⟨4, by omega⟩ := ⟨configOfMask 40 64, by native_decide⟩
theorem essential_n40_k5 : Essential 40 ⟨5, by omega⟩ := ⟨configOfMask 40 64, by native_decide⟩
theorem essential_n40_k6 : Essential 40 ⟨6, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k7 : Essential 40 ⟨7, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k8 : Essential 40 ⟨8, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k9 : Essential 40 ⟨9, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k10 : Essential 40 ⟨10, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k11 : Essential 40 ⟨11, by omega⟩ := ⟨configOfMask 40 4, by native_decide⟩
theorem essential_n40_k12 : Essential 40 ⟨12, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k13 : Essential 40 ⟨13, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k14 : Essential 40 ⟨14, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k15 : Essential 40 ⟨15, by omega⟩ := ⟨configOfMask 40 8, by native_decide⟩
theorem essential_n40_k16 : Essential 40 ⟨16, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k17 : Essential 40 ⟨17, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k18 : Essential 40 ⟨18, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k19 : Essential 40 ⟨19, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k20 : Essential 40 ⟨20, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k21 : Essential 40 ⟨21, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k22 : Essential 40 ⟨22, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k23 : Essential 40 ⟨23, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k24 : Essential 40 ⟨24, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k25 : Essential 40 ⟨25, by omega⟩ := ⟨configOfMask 40 8, by native_decide⟩
theorem essential_n40_k26 : Essential 40 ⟨26, by omega⟩ := ⟨configOfMask 40 10, by native_decide⟩
theorem essential_n40_k27 : Essential 40 ⟨27, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k28 : Essential 40 ⟨28, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k29 : Essential 40 ⟨29, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k30 : Essential 40 ⟨30, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k31 : Essential 40 ⟨31, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k32 : Essential 40 ⟨32, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k33 : Essential 40 ⟨33, by omega⟩ := ⟨configOfMask 40 4, by native_decide⟩
theorem essential_n40_k34 : Essential 40 ⟨34, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k35 : Essential 40 ⟨35, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k36 : Essential 40 ⟨36, by omega⟩ := ⟨configOfMask 40 8, by native_decide⟩
theorem essential_n40_k37 : Essential 40 ⟨37, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k38 : Essential 40 ⟨38, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k39 : Essential 40 ⟨39, by omega⟩ := ⟨configOfMask 40 4, by native_decide⟩
theorem essential_n40_k40 : Essential 40 ⟨40, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k41 : Essential 40 ⟨41, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k42 : Essential 40 ⟨42, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k43 : Essential 40 ⟨43, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k44 : Essential 40 ⟨44, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k45 : Essential 40 ⟨45, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k46 : Essential 40 ⟨46, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k47 : Essential 40 ⟨47, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k48 : Essential 40 ⟨48, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k49 : Essential 40 ⟨49, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k50 : Essential 40 ⟨50, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k51 : Essential 40 ⟨51, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k52 : Essential 40 ⟨52, by omega⟩ := ⟨configOfMask 40 8, by native_decide⟩
theorem essential_n40_k53 : Essential 40 ⟨53, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k54 : Essential 40 ⟨54, by omega⟩ := ⟨configOfMask 40 32, by native_decide⟩
theorem essential_n40_k55 : Essential 40 ⟨55, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k56 : Essential 40 ⟨56, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k57 : Essential 40 ⟨57, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k58 : Essential 40 ⟨58, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k59 : Essential 40 ⟨59, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k60 : Essential 40 ⟨60, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k61 : Essential 40 ⟨61, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k62 : Essential 40 ⟨62, by omega⟩ := ⟨configOfMask 40 4, by native_decide⟩
theorem essential_n40_k63 : Essential 40 ⟨63, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k64 : Essential 40 ⟨64, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k65 : Essential 40 ⟨65, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k66 : Essential 40 ⟨66, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k67 : Essential 40 ⟨67, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k68 : Essential 40 ⟨68, by omega⟩ := ⟨configOfMask 40 8, by native_decide⟩
theorem essential_n40_k69 : Essential 40 ⟨69, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k70 : Essential 40 ⟨70, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k71 : Essential 40 ⟨71, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k72 : Essential 40 ⟨72, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k73 : Essential 40 ⟨73, by omega⟩ := ⟨configOfMask 40 12, by native_decide⟩
theorem essential_n40_k74 : Essential 40 ⟨74, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k75 : Essential 40 ⟨75, by omega⟩ := ⟨configOfMask 40 4, by native_decide⟩
theorem essential_n40_k76 : Essential 40 ⟨76, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k77 : Essential 40 ⟨77, by omega⟩ := ⟨configOfMask 40 12, by native_decide⟩
theorem essential_n40_k78 : Essential 40 ⟨78, by omega⟩ := ⟨configOfMask 40 2, by native_decide⟩
theorem essential_n40_k79 : Essential 40 ⟨79, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩
theorem essential_n40_k80 : Essential 40 ⟨80, by omega⟩ := ⟨configOfMask 40 0, by native_decide⟩





-- ─── BOUNDARY CELL FULL SENSITIVITY (M1) ────────────────────────────────────
--
-- We prove the STRONGER statement for the left boundary cell (k=0):
--   rule30n n (flipCell c ⟨0,...⟩) = !(rule30n n c)   for ALL configs c
-- This is "full sensitivity" — not just ∃ witness, but ∀ config.
--
-- Proof chain:
--   (1) rule30Local_flip_first:   flipping first arg complements output
--   (2) caStep_length:            caStep shrinks list by 2
--   (3) caStep_modifyHead_not:    caStep commutes with flipping the head
--   (4) caEvolve_modifyHead_not:  n steps propagate the head-flip to the result
--   (5) ofFn_modifyHead_flipFirst: flipCell at k=0 = modifyHead on configToList
--   (6) left_boundary_full_sensitive: the theorem itself

-- (1) Flipping the first argument of rule30Local complements the output.
--     Proof: XOR is linear in its first argument: (!p) XOR x = !(p XOR x).
theorem rule30Local_flip_first (p q r : Bool) :
    rule30Local (!p) q r = !(rule30Local p q r) := by
  cases p <;> cases q <;> cases r <;> rfl

-- (2) caStep reduces list length by exactly 2 (or to 0 if list is too short).
theorem caStep_length : ∀ l : List Bool, (caStep l).length = l.length - 2
  | []                  => by simp [caStep]
  | [_]                 => by simp [caStep]
  | [_, _]              => by simp [caStep]
  | _ :: b :: c :: rest => by
      simp only [caStep, List.length_cons]
      have := caStep_length (b :: c :: rest)
      simp only [List.length_cons] at this
      omega

-- (3) Flipping the head of the input list flips the head of caStep's output.
--     The tail of caStep's output doesn't depend on the head, so it's unchanged.
theorem caStep_modifyHead_not (l : List Bool) (h : 3 ≤ l.length) :
    caStep (l.modifyHead Bool.not) = (caStep l).modifyHead Bool.not := by
  match l, h with
  | b :: q :: r :: rest, _ =>
    simp only [List.modifyHead, caStep, rule30Local_flip_first]

-- (4) After n CA steps on a 2n+1 list, flipping the head flips the final output.
--     Induction: each step preserves the "flipped-head" invariant via (3).
theorem caEvolve_modifyHead_not (n : Nat) (l : List Bool) (hl : l.length = 2 * n + 1) :
    (caEvolve n (l.modifyHead Bool.not)).headD false =
    !((caEvolve n l).headD false) := by
  induction n generalizing l with
  | zero =>
    -- l has length 1, so l = [b]
    match l with
    | [b] => simp [caEvolve, List.modifyHead, List.headD]
  | succ n ih =>
    simp only [caEvolve]
    -- l has length 2(n+1)+1 = 2n+3 ≥ 3, so caStep_modifyHead_not applies
    have hlen3 : 3 ≤ l.length := by omega
    rw [caStep_modifyHead_not l hlen3]
    -- Now apply ih to caStep l, which has length 2n+1
    apply ih
    have := caStep_length l
    omega

-- (5) flipCell at index 0 corresponds to modifyHead Bool.not on configToList.
--     Both produce a list identical to the original except the first element is flipped.
theorem ofFn_modifyHead_flipFirst {n : Nat} (c : Config n) :
    configToList (flipCell c ⟨0, by omega⟩) = (configToList c).modifyHead Bool.not := by
  simp only [configToList]
  -- Expand flipCell to its lambda definition
  unfold flipCell
  -- Split the head off both sides using List.ofFn_succ, then simplify modifyHead
  simp only [List.ofFn_succ, List.modifyHead, Fin.ext_iff, Fin.val_zero, ite_true]
  -- Head: (if 0.val = 0 then !c 0 else c 0) = !c 0  ✓ by ite_true
  -- Tail: (if (i.succ).val = 0 then !c i.succ else c i.succ) = c i.succ
  --       reduces to rfl since (i.succ).val = i.val+1 ≠ 0 definitionally
  rfl

-- (6) THE LEFT BOUNDARY FULL SENSITIVITY THEOREM.
--     For ALL configs c, flipping the leftmost initial cell complements the output.
--     This is strictly stronger than "essential": it holds for every config, not just ∃ one.
theorem left_boundary_full_sensitive (n : Nat) (c : Config n) :
    rule30n n (flipCell c ⟨0, by omega⟩) = !(rule30n n c) := by
  simp only [rule30n, ofFn_modifyHead_flipFirst]
  exact caEvolve_modifyHead_not n (configToList c)
    (by simp [configToList, List.length_ofFn])

-- Immediate corollary: left boundary is essential for ALL n (no witness needed).
theorem essential_left_boundary (n : Nat) : Essential n ⟨0, by omega⟩ :=
  -- Witness: all-zeros config. rule30n gives some value b; flipped gives !b ≠ b.
  ⟨fun _ => false, by
    rw [left_boundary_full_sensitive]
    intro h
    exact (Bool.not_eq_self _).mp h.symm⟩

-- ─── RIGHT BOUNDARY: signal propagation approach ───────────────────────────────
--
-- Based on the PRIZE3_RIGHT_BOUNDARY_FINAL.lean proof

-- Simp lemmas for specific values
theorem rule30Local_fff : rule30Local false false false = false := rfl
theorem rule30Local_fft : rule30Local false false true  = true  := rfl

-- caStep reduces all-false by 2
theorem caStep_all_false : ∀ (n : Nat),
    caStep (List.replicate (n + 2) false) = List.replicate n false
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      rw [show List.replicate (n + 2 + 2) false =
          false :: false :: false :: List.replicate (n + 1) false from by
          simp [List.replicate_succ]]
      simp only [caStep, rule30Local_fff]
      rw [show false :: false :: List.replicate (n + 1) false =
          List.replicate (n + 3) false from by
          simp [List.replicate_succ]]
      rw [show n + 3 = (n + 1) + 2 from by omega]
      rw [caStep_all_false (n + 1)]
      simp [List.replicate_succ]

-- caEvolve preserves all-false to single false
theorem caEvolve_all_false : ∀ (n : Nat),
    caEvolve n (List.replicate (2 * n + 1) false) = [false]
  | 0 => rfl
  | (n + 1) => by
      simp only [caEvolve]
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by omega]
      rw [caStep_all_false (2 * n + 1)]
      exact caEvolve_all_false n

-- flipLast: flip the last element of a list
def flipLast : List Bool → List Bool
  | []      => []
  | [x]     => [!x]
  | x :: xs => x :: flipLast xs

-- flipLast distributes over cons
theorem flipLast_cons (x y : Bool) (zs : List Bool) :
    flipLast (x :: y :: zs) = x :: flipLast (y :: zs) := rfl

-- flipLast converts all-false to signal configuration
theorem flipLast_all_false : ∀ (n : Nat),
    flipLast (List.replicate (n + 1) false) = List.replicate n false ++ [true]
  | 0 => rfl
  | (n + 1) => by
      rw [show List.replicate (n + 1 + 1) false =
          false :: false :: List.replicate n false from by simp [List.replicate_succ]]
      rw [flipLast_cons false false (List.replicate n false)]
      rw [show false :: List.replicate n false = List.replicate (n + 1) false from by
          simp [List.replicate_succ]]
      rw [flipLast_all_false n]
      simp [List.replicate_succ, List.cons_append]

-- Helper: caStep cons pattern
theorem caStep_cons3_pattern (p q r : Bool) (rest : List Bool) :
    caStep (p :: q :: r :: rest) = rule30Local p q r :: caStep (q :: r :: rest) := rfl

-- Signal propagation: single T at right eats 2 falses per step
theorem caStep_right_signal : ∀ (n : Nat),
    caStep (List.replicate (n + 2) false ++ [true]) = List.replicate n false ++ [true]
  | 0 => rfl   -- caStep [F, F, T] = [T]  ✓
  | (n + 1) => by
      rw [show List.replicate (n + 1 + 2) false ++ [true] =
          false :: false :: false :: (List.replicate n false ++ [true]) from by
          simp [List.replicate_succ, List.cons_append]]
      rw [caStep_cons3_pattern]
      simp only [rule30Local_fff]
      rw [show List.replicate (n + 1) false ++ [true] =
          false :: (List.replicate n false ++ [true]) from by
          simp [List.replicate_succ, List.cons_append]]
      congr 1
      rw [show false :: false :: (List.replicate n false ++ [true]) =
          List.replicate (n + 2) false ++ [true] from by
          simp [List.replicate_succ, List.cons_append]]
      exact caStep_right_signal n

-- After n+1 steps, signal reaches output
theorem caEvolve_right_signal : ∀ (n : Nat),
    caEvolve (n + 1) (List.replicate (2 * (n + 1)) false ++ [true]) = [true]
  | 0 => rfl
  | (n + 1) => by
      simp only [caEvolve]
      rw [show 2 * (n + 1 + 1) = (2 * (n + 1)) + 2 from by omega]
      rw [caStep_right_signal (2 * (n + 1))]
      exact caEvolve_right_signal n

-- Right boundary is essential
-- Strategy: witness is all-false config, which produces false output.
-- Flipping the rightmost cell creates a signal that propagates to the output.
-- Proof: signal propagation via caStep_right_signal and caEvolve_right_signal
-- Bridge from PRIZE3_RIGHT_BOUNDARY_FINAL.lean

-- Helper: List.ofFn of constant false function = List.replicate
-- (List.ofFn_const does not exist in this Lean version; prove from scratch)
private theorem ofFn_const_false (m : Nat) :
    List.ofFn (fun _ : Fin m => false) = List.replicate m false := by
  apply List.ext_getElem
  · simp [List.length_replicate]
  · intro i h1 h2
    simp [List.getElem_replicate]

-- Helper A: configToList of all-false Config = List.replicate
private theorem configToList_false {n : Nat} :
    configToList (fun _ : Fin (2 * n + 1) => false) = List.replicate (2 * n + 1) false :=
  ofFn_const_false (2 * n + 1)

-- Helper B: configToList of (flipCell all-false at last pos) = signal configuration
-- Flipping cell ⟨2*n, _⟩ of all-false gives: (2*n falses) ++ [true]
private theorem configToList_flipCell_last_false {n : Nat} :
    configToList (flipCell (fun _ : Fin (2 * n + 1) => false) ⟨2 * n, by omega⟩) =
    List.replicate (2 * n) false ++ [true] := by
  -- First rewrite flipCell explicitly: flip the last position of all-false → indicator fn
  have hflip : flipCell (fun _ : Fin (2 * n + 1) => false) ⟨2 * n, by omega⟩ =
               (fun j : Fin (2 * n + 1) => if j.val = 2 * n then true else false) := by
    funext j
    simp [flipCell, Fin.ext_iff]
  unfold configToList
  rw [hflip]
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_append, List.length_replicate]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    simp only []
    by_cases hi : i = 2 * n
    · -- Last position: indicator = true, append gives true
      -- hi : i = 2 * n; condition i = 2*n is true, so if-branch = true
      simp only [hi, show 2 * n = 2 * n from rfl, ite_true]
      rw [List.getElem_append_right (by simp [List.length_replicate])]
      simp [List.length_replicate]
    · -- Interior: indicator = false, replicate gives false
      have hlt : i < 2 * n := by
        simp [List.length_ofFn] at h1; omega
      simp only [hi, ite_false]
      rw [List.getElem_append_left (by simp [List.length_replicate]; exact hlt)]
      simp [List.getElem_replicate]

theorem essential_right_boundary (n : Nat) (hn : 1 ≤ n) :
    Essential n ⟨2 * n, by omega⟩ := by
  -- Witness: all-false configuration
  refine ⟨fun _ => false, ?_⟩
  simp only [rule30n, ne_eq]
  -- Rewrite both configToList expressions using helpers
  rw [configToList_false, configToList_flipCell_last_false]
  -- Unflipped all-false → [false] (by caEvolve_all_false)
  rw [caEvolve_all_false]
  -- Flipped (signal config) → [true]: write n = m+1 (using hn : 1 ≤ n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- caEvolve (m+1) (replicate (2*(m+1)) false ++ [true]) = [true]
  rw [caEvolve_right_signal m]
  -- Goal: [false].headD false ≠ [true].headD false, i.e., false ≠ true
  decide

-- ─── THE KEY OPEN THEOREM: all_cells_essential ─────────────────────────────

/-- THEOREM: Every initial cell in the n-step dependency cone is essential.
    This is the Prize #3 sensitivity lemma.

    PROOF STRATEGY:

    We combine three key approaches:

    (1) LEFT BOUNDARY (k=0):
        Already proved via full sensitivity: for ALL configs, flipping cell 0
        complements the output.

    (2) RIGHT BOUNDARY (k=2n):
        Proved via signal propagation: starting from all-false, flipping the
        rightmost cell creates a signal that propagates and changes output.

    (3) INTERIOR CELLS and SMALL n:
        For n ≤ 4: proved explicitly with witness masks via native_decide
        For n ≥ 5: requires cone decomposition or exhaustive search (ongoing)

    CURRENT STATUS: 16/17 lemmas proved in original ConeStructure.lean
    This version adds:
    - Left boundary full sensitivity (existing)
    - Right boundary signal propagation (new)
    - Base cases n ≤ 4 (existing)
    Remaining: general case for all interior cells and n ≥ 5
-/
-- Helper to cast specific finite values
theorem cast_essential_n1 (k : Fin 3) : Essential 1 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n1_k0
  | ⟨1, _⟩ => exact essential_n1_k1
  | ⟨2, _⟩ => exact essential_n1_k2
  | ⟨k_val + 3, h⟩ => omega

theorem cast_essential_n2 (k : Fin 5) : Essential 2 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n2_k0
  | ⟨1, _⟩ => exact essential_n2_k1
  | ⟨2, _⟩ => exact essential_n2_k2
  | ⟨3, _⟩ => exact essential_n2_k3
  | ⟨4, _⟩ => exact essential_n2_k4
  | ⟨k_val + 5, h⟩ => omega

theorem cast_essential_n3 (k : Fin 7) : Essential 3 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n3_k0
  | ⟨1, _⟩ => exact essential_n3_k1
  | ⟨2, _⟩ => exact essential_n3_k2
  | ⟨3, _⟩ => exact essential_n3_k3
  | ⟨4, _⟩ => exact essential_n3_k4
  | ⟨5, _⟩ => exact essential_n3_k5
  | ⟨6, _⟩ => exact essential_n3_k6
  | ⟨k_val + 7, h⟩ => omega

theorem cast_essential_n4 (k : Fin 9) : Essential 4 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n4_k0
  | ⟨1, _⟩ => exact essential_n4_k1
  | ⟨2, _⟩ => exact essential_n4_k2
  | ⟨3, _⟩ => exact essential_n4_k3
  | ⟨4, _⟩ => exact essential_n4_k4
  | ⟨5, _⟩ => exact essential_n4_k5
  | ⟨6, _⟩ => exact essential_n4_k6
  | ⟨7, _⟩ => exact essential_n4_k7
  | ⟨8, _⟩ => exact essential_n4_k8
  | ⟨k_val + 9, h⟩ => omega

theorem cast_essential_n5 (k : Fin 11) : Essential 5 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n5_k0
  | ⟨1, _⟩ => exact essential_n5_k1
  | ⟨2, _⟩ => exact essential_n5_k2
  | ⟨3, _⟩ => exact essential_n5_k3
  | ⟨4, _⟩ => exact essential_n5_k4
  | ⟨5, _⟩ => exact essential_n5_k5
  | ⟨6, _⟩ => exact essential_n5_k6
  | ⟨7, _⟩ => exact essential_n5_k7
  | ⟨8, _⟩ => exact essential_n5_k8
  | ⟨9, _⟩ => exact essential_n5_k9
  | ⟨10, _⟩ => exact essential_n5_k10
  | ⟨k_val + 11, h⟩ => omega

theorem cast_essential_n6 (k : Fin 13) : Essential 6 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n6_k0
  | ⟨1, _⟩ => exact essential_n6_k1
  | ⟨2, _⟩ => exact essential_n6_k2
  | ⟨3, _⟩ => exact essential_n6_k3
  | ⟨4, _⟩ => exact essential_n6_k4
  | ⟨5, _⟩ => exact essential_n6_k5
  | ⟨6, _⟩ => exact essential_n6_k6
  | ⟨7, _⟩ => exact essential_n6_k7
  | ⟨8, _⟩ => exact essential_n6_k8
  | ⟨9, _⟩ => exact essential_n6_k9
  | ⟨10, _⟩ => exact essential_n6_k10
  | ⟨11, _⟩ => exact essential_n6_k11
  | ⟨12, _⟩ => exact essential_n6_k12
  | ⟨k_val + 13, h⟩ => omega

theorem cast_essential_n7 (k : Fin 15) : Essential 7 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n7_k0
  | ⟨1, _⟩ => exact essential_n7_k1
  | ⟨2, _⟩ => exact essential_n7_k2
  | ⟨3, _⟩ => exact essential_n7_k3
  | ⟨4, _⟩ => exact essential_n7_k4
  | ⟨5, _⟩ => exact essential_n7_k5
  | ⟨6, _⟩ => exact essential_n7_k6
  | ⟨7, _⟩ => exact essential_n7_k7
  | ⟨8, _⟩ => exact essential_n7_k8
  | ⟨9, _⟩ => exact essential_n7_k9
  | ⟨10, _⟩ => exact essential_n7_k10
  | ⟨11, _⟩ => exact essential_n7_k11
  | ⟨12, _⟩ => exact essential_n7_k12
  | ⟨13, _⟩ => exact essential_n7_k13
  | ⟨14, _⟩ => exact essential_n7_k14
  | ⟨k_val + 15, h⟩ => omega

theorem cast_essential_n8 (k : Fin 17) : Essential 8 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n8_k0
  | ⟨1, _⟩ => exact essential_n8_k1
  | ⟨2, _⟩ => exact essential_n8_k2
  | ⟨3, _⟩ => exact essential_n8_k3
  | ⟨4, _⟩ => exact essential_n8_k4
  | ⟨5, _⟩ => exact essential_n8_k5
  | ⟨6, _⟩ => exact essential_n8_k6
  | ⟨7, _⟩ => exact essential_n8_k7
  | ⟨8, _⟩ => exact essential_n8_k8
  | ⟨9, _⟩ => exact essential_n8_k9
  | ⟨10, _⟩ => exact essential_n8_k10
  | ⟨11, _⟩ => exact essential_n8_k11
  | ⟨12, _⟩ => exact essential_n8_k12
  | ⟨13, _⟩ => exact essential_n8_k13
  | ⟨14, _⟩ => exact essential_n8_k14
  | ⟨15, _⟩ => exact essential_n8_k15
  | ⟨16, _⟩ => exact essential_n8_k16
  | ⟨k_val + 17, h⟩ => omega

theorem cast_essential_n13 (k : Fin 27) : Essential 13 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n13_k0
  | ⟨1, _⟩ => exact essential_n13_k1
  | ⟨2, _⟩ => exact essential_n13_k2
  | ⟨3, _⟩ => exact essential_n13_k3
  | ⟨4, _⟩ => exact essential_n13_k4
  | ⟨5, _⟩ => exact essential_n13_k5
  | ⟨6, _⟩ => exact essential_n13_k6
  | ⟨7, _⟩ => exact essential_n13_k7
  | ⟨8, _⟩ => exact essential_n13_k8
  | ⟨9, _⟩ => exact essential_n13_k9
  | ⟨10, _⟩ => exact essential_n13_k10
  | ⟨11, _⟩ => exact essential_n13_k11
  | ⟨12, _⟩ => exact essential_n13_k12
  | ⟨13, _⟩ => exact essential_n13_k13
  | ⟨14, _⟩ => exact essential_n13_k14
  | ⟨15, _⟩ => exact essential_n13_k15
  | ⟨16, _⟩ => exact essential_n13_k16
  | ⟨17, _⟩ => exact essential_n13_k17
  | ⟨18, _⟩ => exact essential_n13_k18
  | ⟨19, _⟩ => exact essential_n13_k19
  | ⟨20, _⟩ => exact essential_n13_k20
  | ⟨21, _⟩ => exact essential_n13_k21
  | ⟨22, _⟩ => exact essential_n13_k22
  | ⟨23, _⟩ => exact essential_n13_k23
  | ⟨24, _⟩ => exact essential_n13_k24
  | ⟨25, _⟩ => exact essential_n13_k25
  | ⟨26, _⟩ => exact essential_n13_k26
  | ⟨k_val + 27, h⟩ => omega

theorem cast_essential_n14 (k : Fin 29) : Essential 14 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n14_k0
  | ⟨1, _⟩ => exact essential_n14_k1
  | ⟨2, _⟩ => exact essential_n14_k2
  | ⟨3, _⟩ => exact essential_n14_k3
  | ⟨4, _⟩ => exact essential_n14_k4
  | ⟨5, _⟩ => exact essential_n14_k5
  | ⟨6, _⟩ => exact essential_n14_k6
  | ⟨7, _⟩ => exact essential_n14_k7
  | ⟨8, _⟩ => exact essential_n14_k8
  | ⟨9, _⟩ => exact essential_n14_k9
  | ⟨10, _⟩ => exact essential_n14_k10
  | ⟨11, _⟩ => exact essential_n14_k11
  | ⟨12, _⟩ => exact essential_n14_k12
  | ⟨13, _⟩ => exact essential_n14_k13
  | ⟨14, _⟩ => exact essential_n14_k14
  | ⟨15, _⟩ => exact essential_n14_k15
  | ⟨16, _⟩ => exact essential_n14_k16
  | ⟨17, _⟩ => exact essential_n14_k17
  | ⟨18, _⟩ => exact essential_n14_k18
  | ⟨19, _⟩ => exact essential_n14_k19
  | ⟨20, _⟩ => exact essential_n14_k20
  | ⟨21, _⟩ => exact essential_n14_k21
  | ⟨22, _⟩ => exact essential_n14_k22
  | ⟨23, _⟩ => exact essential_n14_k23
  | ⟨24, _⟩ => exact essential_n14_k24
  | ⟨25, _⟩ => exact essential_n14_k25
  | ⟨26, _⟩ => exact essential_n14_k26
  | ⟨27, _⟩ => exact essential_n14_k27
  | ⟨28, _⟩ => exact essential_n14_k28
  | ⟨k_val + 29, h⟩ => omega

theorem cast_essential_n15 (k : Fin 31) : Essential 15 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n15_k0
  | ⟨1, _⟩ => exact essential_n15_k1
  | ⟨2, _⟩ => exact essential_n15_k2
  | ⟨3, _⟩ => exact essential_n15_k3
  | ⟨4, _⟩ => exact essential_n15_k4
  | ⟨5, _⟩ => exact essential_n15_k5
  | ⟨6, _⟩ => exact essential_n15_k6
  | ⟨7, _⟩ => exact essential_n15_k7
  | ⟨8, _⟩ => exact essential_n15_k8
  | ⟨9, _⟩ => exact essential_n15_k9
  | ⟨10, _⟩ => exact essential_n15_k10
  | ⟨11, _⟩ => exact essential_n15_k11
  | ⟨12, _⟩ => exact essential_n15_k12
  | ⟨13, _⟩ => exact essential_n15_k13
  | ⟨14, _⟩ => exact essential_n15_k14
  | ⟨15, _⟩ => exact essential_n15_k15
  | ⟨16, _⟩ => exact essential_n15_k16
  | ⟨17, _⟩ => exact essential_n15_k17
  | ⟨18, _⟩ => exact essential_n15_k18
  | ⟨19, _⟩ => exact essential_n15_k19
  | ⟨20, _⟩ => exact essential_n15_k20
  | ⟨21, _⟩ => exact essential_n15_k21
  | ⟨22, _⟩ => exact essential_n15_k22
  | ⟨23, _⟩ => exact essential_n15_k23
  | ⟨24, _⟩ => exact essential_n15_k24
  | ⟨25, _⟩ => exact essential_n15_k25
  | ⟨26, _⟩ => exact essential_n15_k26
  | ⟨27, _⟩ => exact essential_n15_k27
  | ⟨28, _⟩ => exact essential_n15_k28
  | ⟨29, _⟩ => exact essential_n15_k29
  | ⟨30, _⟩ => exact essential_n15_k30
  | ⟨k_val + 31, h⟩ => omega

theorem cast_essential_n18 (k : Fin 37) : Essential 18 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n18_k0
  | ⟨1, _⟩ => exact essential_n18_k1
  | ⟨2, _⟩ => exact essential_n18_k2
  | ⟨3, _⟩ => exact essential_n18_k3
  | ⟨4, _⟩ => exact essential_n18_k4
  | ⟨5, _⟩ => exact essential_n18_k5
  | ⟨6, _⟩ => exact essential_n18_k6
  | ⟨7, _⟩ => exact essential_n18_k7
  | ⟨8, _⟩ => exact essential_n18_k8
  | ⟨9, _⟩ => exact essential_n18_k9
  | ⟨10, _⟩ => exact essential_n18_k10
  | ⟨11, _⟩ => exact essential_n18_k11
  | ⟨12, _⟩ => exact essential_n18_k12
  | ⟨13, _⟩ => exact essential_n18_k13
  | ⟨14, _⟩ => exact essential_n18_k14
  | ⟨15, _⟩ => exact essential_n18_k15
  | ⟨16, _⟩ => exact essential_n18_k16
  | ⟨17, _⟩ => exact essential_n18_k17
  | ⟨18, _⟩ => exact essential_n18_k18
  | ⟨19, _⟩ => exact essential_n18_k19
  | ⟨20, _⟩ => exact essential_n18_k20
  | ⟨21, _⟩ => exact essential_n18_k21
  | ⟨22, _⟩ => exact essential_n18_k22
  | ⟨23, _⟩ => exact essential_n18_k23
  | ⟨24, _⟩ => exact essential_n18_k24
  | ⟨25, _⟩ => exact essential_n18_k25
  | ⟨26, _⟩ => exact essential_n18_k26
  | ⟨27, _⟩ => exact essential_n18_k27
  | ⟨28, _⟩ => exact essential_n18_k28
  | ⟨29, _⟩ => exact essential_n18_k29
  | ⟨30, _⟩ => exact essential_n18_k30
  | ⟨31, _⟩ => exact essential_n18_k31
  | ⟨32, _⟩ => exact essential_n18_k32
  | ⟨33, _⟩ => exact essential_n18_k33
  | ⟨34, _⟩ => exact essential_n18_k34
  | ⟨35, _⟩ => exact essential_n18_k35
  | ⟨36, _⟩ => exact essential_n18_k36
  | ⟨k_val + 37, h⟩ => omega

theorem cast_essential_n19 (k : Fin 39) : Essential 19 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n19_k0
  | ⟨1, _⟩ => exact essential_n19_k1
  | ⟨2, _⟩ => exact essential_n19_k2
  | ⟨3, _⟩ => exact essential_n19_k3
  | ⟨4, _⟩ => exact essential_n19_k4
  | ⟨5, _⟩ => exact essential_n19_k5
  | ⟨6, _⟩ => exact essential_n19_k6
  | ⟨7, _⟩ => exact essential_n19_k7
  | ⟨8, _⟩ => exact essential_n19_k8
  | ⟨9, _⟩ => exact essential_n19_k9
  | ⟨10, _⟩ => exact essential_n19_k10
  | ⟨11, _⟩ => exact essential_n19_k11
  | ⟨12, _⟩ => exact essential_n19_k12
  | ⟨13, _⟩ => exact essential_n19_k13
  | ⟨14, _⟩ => exact essential_n19_k14
  | ⟨15, _⟩ => exact essential_n19_k15
  | ⟨16, _⟩ => exact essential_n19_k16
  | ⟨17, _⟩ => exact essential_n19_k17
  | ⟨18, _⟩ => exact essential_n19_k18
  | ⟨19, _⟩ => exact essential_n19_k19
  | ⟨20, _⟩ => exact essential_n19_k20
  | ⟨21, _⟩ => exact essential_n19_k21
  | ⟨22, _⟩ => exact essential_n19_k22
  | ⟨23, _⟩ => exact essential_n19_k23
  | ⟨24, _⟩ => exact essential_n19_k24
  | ⟨25, _⟩ => exact essential_n19_k25
  | ⟨26, _⟩ => exact essential_n19_k26
  | ⟨27, _⟩ => exact essential_n19_k27
  | ⟨28, _⟩ => exact essential_n19_k28
  | ⟨29, _⟩ => exact essential_n19_k29
  | ⟨30, _⟩ => exact essential_n19_k30
  | ⟨31, _⟩ => exact essential_n19_k31
  | ⟨32, _⟩ => exact essential_n19_k32
  | ⟨33, _⟩ => exact essential_n19_k33
  | ⟨34, _⟩ => exact essential_n19_k34
  | ⟨35, _⟩ => exact essential_n19_k35
  | ⟨36, _⟩ => exact essential_n19_k36
  | ⟨37, _⟩ => exact essential_n19_k37
  | ⟨38, _⟩ => exact essential_n19_k38
  | ⟨k_val + 39, h⟩ => omega

theorem cast_essential_n20 (k : Fin 41) : Essential 20 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n20_k0
  | ⟨1, _⟩ => exact essential_n20_k1
  | ⟨2, _⟩ => exact essential_n20_k2
  | ⟨3, _⟩ => exact essential_n20_k3
  | ⟨4, _⟩ => exact essential_n20_k4
  | ⟨5, _⟩ => exact essential_n20_k5
  | ⟨6, _⟩ => exact essential_n20_k6
  | ⟨7, _⟩ => exact essential_n20_k7
  | ⟨8, _⟩ => exact essential_n20_k8
  | ⟨9, _⟩ => exact essential_n20_k9
  | ⟨10, _⟩ => exact essential_n20_k10
  | ⟨11, _⟩ => exact essential_n20_k11
  | ⟨12, _⟩ => exact essential_n20_k12
  | ⟨13, _⟩ => exact essential_n20_k13
  | ⟨14, _⟩ => exact essential_n20_k14
  | ⟨15, _⟩ => exact essential_n20_k15
  | ⟨16, _⟩ => exact essential_n20_k16
  | ⟨17, _⟩ => exact essential_n20_k17
  | ⟨18, _⟩ => exact essential_n20_k18
  | ⟨19, _⟩ => exact essential_n20_k19
  | ⟨20, _⟩ => exact essential_n20_k20
  | ⟨21, _⟩ => exact essential_n20_k21
  | ⟨22, _⟩ => exact essential_n20_k22
  | ⟨23, _⟩ => exact essential_n20_k23
  | ⟨24, _⟩ => exact essential_n20_k24
  | ⟨25, _⟩ => exact essential_n20_k25
  | ⟨26, _⟩ => exact essential_n20_k26
  | ⟨27, _⟩ => exact essential_n20_k27
  | ⟨28, _⟩ => exact essential_n20_k28
  | ⟨29, _⟩ => exact essential_n20_k29
  | ⟨30, _⟩ => exact essential_n20_k30
  | ⟨31, _⟩ => exact essential_n20_k31
  | ⟨32, _⟩ => exact essential_n20_k32
  | ⟨33, _⟩ => exact essential_n20_k33
  | ⟨34, _⟩ => exact essential_n20_k34
  | ⟨35, _⟩ => exact essential_n20_k35
  | ⟨36, _⟩ => exact essential_n20_k36
  | ⟨37, _⟩ => exact essential_n20_k37
  | ⟨38, _⟩ => exact essential_n20_k38
  | ⟨39, _⟩ => exact essential_n20_k39
  | ⟨40, _⟩ => exact essential_n20_k40
  | ⟨k_val + 41, h⟩ => omega

theorem cast_essential_n21 (k : Fin 43) : Essential 21 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n21_k0
  | ⟨1, _⟩ => exact essential_n21_k1
  | ⟨2, _⟩ => exact essential_n21_k2
  | ⟨3, _⟩ => exact essential_n21_k3
  | ⟨4, _⟩ => exact essential_n21_k4
  | ⟨5, _⟩ => exact essential_n21_k5
  | ⟨6, _⟩ => exact essential_n21_k6
  | ⟨7, _⟩ => exact essential_n21_k7
  | ⟨8, _⟩ => exact essential_n21_k8
  | ⟨9, _⟩ => exact essential_n21_k9
  | ⟨10, _⟩ => exact essential_n21_k10
  | ⟨11, _⟩ => exact essential_n21_k11
  | ⟨12, _⟩ => exact essential_n21_k12
  | ⟨13, _⟩ => exact essential_n21_k13
  | ⟨14, _⟩ => exact essential_n21_k14
  | ⟨15, _⟩ => exact essential_n21_k15
  | ⟨16, _⟩ => exact essential_n21_k16
  | ⟨17, _⟩ => exact essential_n21_k17
  | ⟨18, _⟩ => exact essential_n21_k18
  | ⟨19, _⟩ => exact essential_n21_k19
  | ⟨20, _⟩ => exact essential_n21_k20
  | ⟨21, _⟩ => exact essential_n21_k21
  | ⟨22, _⟩ => exact essential_n21_k22
  | ⟨23, _⟩ => exact essential_n21_k23
  | ⟨24, _⟩ => exact essential_n21_k24
  | ⟨25, _⟩ => exact essential_n21_k25
  | ⟨26, _⟩ => exact essential_n21_k26
  | ⟨27, _⟩ => exact essential_n21_k27
  | ⟨28, _⟩ => exact essential_n21_k28
  | ⟨29, _⟩ => exact essential_n21_k29
  | ⟨30, _⟩ => exact essential_n21_k30
  | ⟨31, _⟩ => exact essential_n21_k31
  | ⟨32, _⟩ => exact essential_n21_k32
  | ⟨33, _⟩ => exact essential_n21_k33
  | ⟨34, _⟩ => exact essential_n21_k34
  | ⟨35, _⟩ => exact essential_n21_k35
  | ⟨36, _⟩ => exact essential_n21_k36
  | ⟨37, _⟩ => exact essential_n21_k37
  | ⟨38, _⟩ => exact essential_n21_k38
  | ⟨39, _⟩ => exact essential_n21_k39
  | ⟨40, _⟩ => exact essential_n21_k40
  | ⟨41, _⟩ => exact essential_n21_k41
  | ⟨42, _⟩ => exact essential_n21_k42
  | ⟨k_val + 43, h⟩ => omega

theorem cast_essential_n22 (k : Fin 45) : Essential 22 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n22_k0
  | ⟨1, _⟩ => exact essential_n22_k1
  | ⟨2, _⟩ => exact essential_n22_k2
  | ⟨3, _⟩ => exact essential_n22_k3
  | ⟨4, _⟩ => exact essential_n22_k4
  | ⟨5, _⟩ => exact essential_n22_k5
  | ⟨6, _⟩ => exact essential_n22_k6
  | ⟨7, _⟩ => exact essential_n22_k7
  | ⟨8, _⟩ => exact essential_n22_k8
  | ⟨9, _⟩ => exact essential_n22_k9
  | ⟨10, _⟩ => exact essential_n22_k10
  | ⟨11, _⟩ => exact essential_n22_k11
  | ⟨12, _⟩ => exact essential_n22_k12
  | ⟨13, _⟩ => exact essential_n22_k13
  | ⟨14, _⟩ => exact essential_n22_k14
  | ⟨15, _⟩ => exact essential_n22_k15
  | ⟨16, _⟩ => exact essential_n22_k16
  | ⟨17, _⟩ => exact essential_n22_k17
  | ⟨18, _⟩ => exact essential_n22_k18
  | ⟨19, _⟩ => exact essential_n22_k19
  | ⟨20, _⟩ => exact essential_n22_k20
  | ⟨21, _⟩ => exact essential_n22_k21
  | ⟨22, _⟩ => exact essential_n22_k22
  | ⟨23, _⟩ => exact essential_n22_k23
  | ⟨24, _⟩ => exact essential_n22_k24
  | ⟨25, _⟩ => exact essential_n22_k25
  | ⟨26, _⟩ => exact essential_n22_k26
  | ⟨27, _⟩ => exact essential_n22_k27
  | ⟨28, _⟩ => exact essential_n22_k28
  | ⟨29, _⟩ => exact essential_n22_k29
  | ⟨30, _⟩ => exact essential_n22_k30
  | ⟨31, _⟩ => exact essential_n22_k31
  | ⟨32, _⟩ => exact essential_n22_k32
  | ⟨33, _⟩ => exact essential_n22_k33
  | ⟨34, _⟩ => exact essential_n22_k34
  | ⟨35, _⟩ => exact essential_n22_k35
  | ⟨36, _⟩ => exact essential_n22_k36
  | ⟨37, _⟩ => exact essential_n22_k37
  | ⟨38, _⟩ => exact essential_n22_k38
  | ⟨39, _⟩ => exact essential_n22_k39
  | ⟨40, _⟩ => exact essential_n22_k40
  | ⟨41, _⟩ => exact essential_n22_k41
  | ⟨42, _⟩ => exact essential_n22_k42
  | ⟨43, _⟩ => exact essential_n22_k43
  | ⟨44, _⟩ => exact essential_n22_k44
  | ⟨k_val + 45, h⟩ => omega

theorem cast_essential_n23 (k : Fin 47) : Essential 23 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n23_k0
  | ⟨1, _⟩ => exact essential_n23_k1
  | ⟨2, _⟩ => exact essential_n23_k2
  | ⟨3, _⟩ => exact essential_n23_k3
  | ⟨4, _⟩ => exact essential_n23_k4
  | ⟨5, _⟩ => exact essential_n23_k5
  | ⟨6, _⟩ => exact essential_n23_k6
  | ⟨7, _⟩ => exact essential_n23_k7
  | ⟨8, _⟩ => exact essential_n23_k8
  | ⟨9, _⟩ => exact essential_n23_k9
  | ⟨10, _⟩ => exact essential_n23_k10
  | ⟨11, _⟩ => exact essential_n23_k11
  | ⟨12, _⟩ => exact essential_n23_k12
  | ⟨13, _⟩ => exact essential_n23_k13
  | ⟨14, _⟩ => exact essential_n23_k14
  | ⟨15, _⟩ => exact essential_n23_k15
  | ⟨16, _⟩ => exact essential_n23_k16
  | ⟨17, _⟩ => exact essential_n23_k17
  | ⟨18, _⟩ => exact essential_n23_k18
  | ⟨19, _⟩ => exact essential_n23_k19
  | ⟨20, _⟩ => exact essential_n23_k20
  | ⟨21, _⟩ => exact essential_n23_k21
  | ⟨22, _⟩ => exact essential_n23_k22
  | ⟨23, _⟩ => exact essential_n23_k23
  | ⟨24, _⟩ => exact essential_n23_k24
  | ⟨25, _⟩ => exact essential_n23_k25
  | ⟨26, _⟩ => exact essential_n23_k26
  | ⟨27, _⟩ => exact essential_n23_k27
  | ⟨28, _⟩ => exact essential_n23_k28
  | ⟨29, _⟩ => exact essential_n23_k29
  | ⟨30, _⟩ => exact essential_n23_k30
  | ⟨31, _⟩ => exact essential_n23_k31
  | ⟨32, _⟩ => exact essential_n23_k32
  | ⟨33, _⟩ => exact essential_n23_k33
  | ⟨34, _⟩ => exact essential_n23_k34
  | ⟨35, _⟩ => exact essential_n23_k35
  | ⟨36, _⟩ => exact essential_n23_k36
  | ⟨37, _⟩ => exact essential_n23_k37
  | ⟨38, _⟩ => exact essential_n23_k38
  | ⟨39, _⟩ => exact essential_n23_k39
  | ⟨40, _⟩ => exact essential_n23_k40
  | ⟨41, _⟩ => exact essential_n23_k41
  | ⟨42, _⟩ => exact essential_n23_k42
  | ⟨43, _⟩ => exact essential_n23_k43
  | ⟨44, _⟩ => exact essential_n23_k44
  | ⟨45, _⟩ => exact essential_n23_k45
  | ⟨46, _⟩ => exact essential_n23_k46
  | ⟨k_val + 47, h⟩ => omega

theorem cast_essential_n24 (k : Fin 49) : Essential 24 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n24_k0
  | ⟨1, _⟩ => exact essential_n24_k1
  | ⟨2, _⟩ => exact essential_n24_k2
  | ⟨3, _⟩ => exact essential_n24_k3
  | ⟨4, _⟩ => exact essential_n24_k4
  | ⟨5, _⟩ => exact essential_n24_k5
  | ⟨6, _⟩ => exact essential_n24_k6
  | ⟨7, _⟩ => exact essential_n24_k7
  | ⟨8, _⟩ => exact essential_n24_k8
  | ⟨9, _⟩ => exact essential_n24_k9
  | ⟨10, _⟩ => exact essential_n24_k10
  | ⟨11, _⟩ => exact essential_n24_k11
  | ⟨12, _⟩ => exact essential_n24_k12
  | ⟨13, _⟩ => exact essential_n24_k13
  | ⟨14, _⟩ => exact essential_n24_k14
  | ⟨15, _⟩ => exact essential_n24_k15
  | ⟨16, _⟩ => exact essential_n24_k16
  | ⟨17, _⟩ => exact essential_n24_k17
  | ⟨18, _⟩ => exact essential_n24_k18
  | ⟨19, _⟩ => exact essential_n24_k19
  | ⟨20, _⟩ => exact essential_n24_k20
  | ⟨21, _⟩ => exact essential_n24_k21
  | ⟨22, _⟩ => exact essential_n24_k22
  | ⟨23, _⟩ => exact essential_n24_k23
  | ⟨24, _⟩ => exact essential_n24_k24
  | ⟨25, _⟩ => exact essential_n24_k25
  | ⟨26, _⟩ => exact essential_n24_k26
  | ⟨27, _⟩ => exact essential_n24_k27
  | ⟨28, _⟩ => exact essential_n24_k28
  | ⟨29, _⟩ => exact essential_n24_k29
  | ⟨30, _⟩ => exact essential_n24_k30
  | ⟨31, _⟩ => exact essential_n24_k31
  | ⟨32, _⟩ => exact essential_n24_k32
  | ⟨33, _⟩ => exact essential_n24_k33
  | ⟨34, _⟩ => exact essential_n24_k34
  | ⟨35, _⟩ => exact essential_n24_k35
  | ⟨36, _⟩ => exact essential_n24_k36
  | ⟨37, _⟩ => exact essential_n24_k37
  | ⟨38, _⟩ => exact essential_n24_k38
  | ⟨39, _⟩ => exact essential_n24_k39
  | ⟨40, _⟩ => exact essential_n24_k40
  | ⟨41, _⟩ => exact essential_n24_k41
  | ⟨42, _⟩ => exact essential_n24_k42
  | ⟨43, _⟩ => exact essential_n24_k43
  | ⟨44, _⟩ => exact essential_n24_k44
  | ⟨45, _⟩ => exact essential_n24_k45
  | ⟨46, _⟩ => exact essential_n24_k46
  | ⟨47, _⟩ => exact essential_n24_k47
  | ⟨48, _⟩ => exact essential_n24_k48
  | ⟨k_val + 49, h⟩ => omega

theorem cast_essential_n26 (k : Fin 53) : Essential 26 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n26_k0
  | ⟨1, _⟩ => exact essential_n26_k1
  | ⟨2, _⟩ => exact essential_n26_k2
  | ⟨3, _⟩ => exact essential_n26_k3
  | ⟨4, _⟩ => exact essential_n26_k4
  | ⟨5, _⟩ => exact essential_n26_k5
  | ⟨6, _⟩ => exact essential_n26_k6
  | ⟨7, _⟩ => exact essential_n26_k7
  | ⟨8, _⟩ => exact essential_n26_k8
  | ⟨9, _⟩ => exact essential_n26_k9
  | ⟨10, _⟩ => exact essential_n26_k10
  | ⟨11, _⟩ => exact essential_n26_k11
  | ⟨12, _⟩ => exact essential_n26_k12
  | ⟨13, _⟩ => exact essential_n26_k13
  | ⟨14, _⟩ => exact essential_n26_k14
  | ⟨15, _⟩ => exact essential_n26_k15
  | ⟨16, _⟩ => exact essential_n26_k16
  | ⟨17, _⟩ => exact essential_n26_k17
  | ⟨18, _⟩ => exact essential_n26_k18
  | ⟨19, _⟩ => exact essential_n26_k19
  | ⟨20, _⟩ => exact essential_n26_k20
  | ⟨21, _⟩ => exact essential_n26_k21
  | ⟨22, _⟩ => exact essential_n26_k22
  | ⟨23, _⟩ => exact essential_n26_k23
  | ⟨24, _⟩ => exact essential_n26_k24
  | ⟨25, _⟩ => exact essential_n26_k25
  | ⟨26, _⟩ => exact essential_n26_k26
  | ⟨27, _⟩ => exact essential_n26_k27
  | ⟨28, _⟩ => exact essential_n26_k28
  | ⟨29, _⟩ => exact essential_n26_k29
  | ⟨30, _⟩ => exact essential_n26_k30
  | ⟨31, _⟩ => exact essential_n26_k31
  | ⟨32, _⟩ => exact essential_n26_k32
  | ⟨33, _⟩ => exact essential_n26_k33
  | ⟨34, _⟩ => exact essential_n26_k34
  | ⟨35, _⟩ => exact essential_n26_k35
  | ⟨36, _⟩ => exact essential_n26_k36
  | ⟨37, _⟩ => exact essential_n26_k37
  | ⟨38, _⟩ => exact essential_n26_k38
  | ⟨39, _⟩ => exact essential_n26_k39
  | ⟨40, _⟩ => exact essential_n26_k40
  | ⟨41, _⟩ => exact essential_n26_k41
  | ⟨42, _⟩ => exact essential_n26_k42
  | ⟨43, _⟩ => exact essential_n26_k43
  | ⟨44, _⟩ => exact essential_n26_k44
  | ⟨45, _⟩ => exact essential_n26_k45
  | ⟨46, _⟩ => exact essential_n26_k46
  | ⟨47, _⟩ => exact essential_n26_k47
  | ⟨48, _⟩ => exact essential_n26_k48
  | ⟨49, _⟩ => exact essential_n26_k49
  | ⟨50, _⟩ => exact essential_n26_k50
  | ⟨51, _⟩ => exact essential_n26_k51
  | ⟨52, _⟩ => exact essential_n26_k52
  | ⟨k_val + 53, h⟩ => omega

theorem cast_essential_n27 (k : Fin 55) : Essential 27 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n27_k0
  | ⟨1, _⟩ => exact essential_n27_k1
  | ⟨2, _⟩ => exact essential_n27_k2
  | ⟨3, _⟩ => exact essential_n27_k3
  | ⟨4, _⟩ => exact essential_n27_k4
  | ⟨5, _⟩ => exact essential_n27_k5
  | ⟨6, _⟩ => exact essential_n27_k6
  | ⟨7, _⟩ => exact essential_n27_k7
  | ⟨8, _⟩ => exact essential_n27_k8
  | ⟨9, _⟩ => exact essential_n27_k9
  | ⟨10, _⟩ => exact essential_n27_k10
  | ⟨11, _⟩ => exact essential_n27_k11
  | ⟨12, _⟩ => exact essential_n27_k12
  | ⟨13, _⟩ => exact essential_n27_k13
  | ⟨14, _⟩ => exact essential_n27_k14
  | ⟨15, _⟩ => exact essential_n27_k15
  | ⟨16, _⟩ => exact essential_n27_k16
  | ⟨17, _⟩ => exact essential_n27_k17
  | ⟨18, _⟩ => exact essential_n27_k18
  | ⟨19, _⟩ => exact essential_n27_k19
  | ⟨20, _⟩ => exact essential_n27_k20
  | ⟨21, _⟩ => exact essential_n27_k21
  | ⟨22, _⟩ => exact essential_n27_k22
  | ⟨23, _⟩ => exact essential_n27_k23
  | ⟨24, _⟩ => exact essential_n27_k24
  | ⟨25, _⟩ => exact essential_n27_k25
  | ⟨26, _⟩ => exact essential_n27_k26
  | ⟨27, _⟩ => exact essential_n27_k27
  | ⟨28, _⟩ => exact essential_n27_k28
  | ⟨29, _⟩ => exact essential_n27_k29
  | ⟨30, _⟩ => exact essential_n27_k30
  | ⟨31, _⟩ => exact essential_n27_k31
  | ⟨32, _⟩ => exact essential_n27_k32
  | ⟨33, _⟩ => exact essential_n27_k33
  | ⟨34, _⟩ => exact essential_n27_k34
  | ⟨35, _⟩ => exact essential_n27_k35
  | ⟨36, _⟩ => exact essential_n27_k36
  | ⟨37, _⟩ => exact essential_n27_k37
  | ⟨38, _⟩ => exact essential_n27_k38
  | ⟨39, _⟩ => exact essential_n27_k39
  | ⟨40, _⟩ => exact essential_n27_k40
  | ⟨41, _⟩ => exact essential_n27_k41
  | ⟨42, _⟩ => exact essential_n27_k42
  | ⟨43, _⟩ => exact essential_n27_k43
  | ⟨44, _⟩ => exact essential_n27_k44
  | ⟨45, _⟩ => exact essential_n27_k45
  | ⟨46, _⟩ => exact essential_n27_k46
  | ⟨47, _⟩ => exact essential_n27_k47
  | ⟨48, _⟩ => exact essential_n27_k48
  | ⟨49, _⟩ => exact essential_n27_k49
  | ⟨50, _⟩ => exact essential_n27_k50
  | ⟨51, _⟩ => exact essential_n27_k51
  | ⟨52, _⟩ => exact essential_n27_k52
  | ⟨53, _⟩ => exact essential_n27_k53
  | ⟨54, _⟩ => exact essential_n27_k54
  | ⟨k_val + 55, h⟩ => omega

theorem cast_essential_n28 (k : Fin 57) : Essential 28 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n28_k0
  | ⟨1, _⟩ => exact essential_n28_k1
  | ⟨2, _⟩ => exact essential_n28_k2
  | ⟨3, _⟩ => exact essential_n28_k3
  | ⟨4, _⟩ => exact essential_n28_k4
  | ⟨5, _⟩ => exact essential_n28_k5
  | ⟨6, _⟩ => exact essential_n28_k6
  | ⟨7, _⟩ => exact essential_n28_k7
  | ⟨8, _⟩ => exact essential_n28_k8
  | ⟨9, _⟩ => exact essential_n28_k9
  | ⟨10, _⟩ => exact essential_n28_k10
  | ⟨11, _⟩ => exact essential_n28_k11
  | ⟨12, _⟩ => exact essential_n28_k12
  | ⟨13, _⟩ => exact essential_n28_k13
  | ⟨14, _⟩ => exact essential_n28_k14
  | ⟨15, _⟩ => exact essential_n28_k15
  | ⟨16, _⟩ => exact essential_n28_k16
  | ⟨17, _⟩ => exact essential_n28_k17
  | ⟨18, _⟩ => exact essential_n28_k18
  | ⟨19, _⟩ => exact essential_n28_k19
  | ⟨20, _⟩ => exact essential_n28_k20
  | ⟨21, _⟩ => exact essential_n28_k21
  | ⟨22, _⟩ => exact essential_n28_k22
  | ⟨23, _⟩ => exact essential_n28_k23
  | ⟨24, _⟩ => exact essential_n28_k24
  | ⟨25, _⟩ => exact essential_n28_k25
  | ⟨26, _⟩ => exact essential_n28_k26
  | ⟨27, _⟩ => exact essential_n28_k27
  | ⟨28, _⟩ => exact essential_n28_k28
  | ⟨29, _⟩ => exact essential_n28_k29
  | ⟨30, _⟩ => exact essential_n28_k30
  | ⟨31, _⟩ => exact essential_n28_k31
  | ⟨32, _⟩ => exact essential_n28_k32
  | ⟨33, _⟩ => exact essential_n28_k33
  | ⟨34, _⟩ => exact essential_n28_k34
  | ⟨35, _⟩ => exact essential_n28_k35
  | ⟨36, _⟩ => exact essential_n28_k36
  | ⟨37, _⟩ => exact essential_n28_k37
  | ⟨38, _⟩ => exact essential_n28_k38
  | ⟨39, _⟩ => exact essential_n28_k39
  | ⟨40, _⟩ => exact essential_n28_k40
  | ⟨41, _⟩ => exact essential_n28_k41
  | ⟨42, _⟩ => exact essential_n28_k42
  | ⟨43, _⟩ => exact essential_n28_k43
  | ⟨44, _⟩ => exact essential_n28_k44
  | ⟨45, _⟩ => exact essential_n28_k45
  | ⟨46, _⟩ => exact essential_n28_k46
  | ⟨47, _⟩ => exact essential_n28_k47
  | ⟨48, _⟩ => exact essential_n28_k48
  | ⟨49, _⟩ => exact essential_n28_k49
  | ⟨50, _⟩ => exact essential_n28_k50
  | ⟨51, _⟩ => exact essential_n28_k51
  | ⟨52, _⟩ => exact essential_n28_k52
  | ⟨53, _⟩ => exact essential_n28_k53
  | ⟨54, _⟩ => exact essential_n28_k54
  | ⟨55, _⟩ => exact essential_n28_k55
  | ⟨56, _⟩ => exact essential_n28_k56
  | ⟨k_val + 57, h⟩ => omega

theorem cast_essential_n29 (k : Fin 59) : Essential 29 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n29_k0
  | ⟨1, _⟩ => exact essential_n29_k1
  | ⟨2, _⟩ => exact essential_n29_k2
  | ⟨3, _⟩ => exact essential_n29_k3
  | ⟨4, _⟩ => exact essential_n29_k4
  | ⟨5, _⟩ => exact essential_n29_k5
  | ⟨6, _⟩ => exact essential_n29_k6
  | ⟨7, _⟩ => exact essential_n29_k7
  | ⟨8, _⟩ => exact essential_n29_k8
  | ⟨9, _⟩ => exact essential_n29_k9
  | ⟨10, _⟩ => exact essential_n29_k10
  | ⟨11, _⟩ => exact essential_n29_k11
  | ⟨12, _⟩ => exact essential_n29_k12
  | ⟨13, _⟩ => exact essential_n29_k13
  | ⟨14, _⟩ => exact essential_n29_k14
  | ⟨15, _⟩ => exact essential_n29_k15
  | ⟨16, _⟩ => exact essential_n29_k16
  | ⟨17, _⟩ => exact essential_n29_k17
  | ⟨18, _⟩ => exact essential_n29_k18
  | ⟨19, _⟩ => exact essential_n29_k19
  | ⟨20, _⟩ => exact essential_n29_k20
  | ⟨21, _⟩ => exact essential_n29_k21
  | ⟨22, _⟩ => exact essential_n29_k22
  | ⟨23, _⟩ => exact essential_n29_k23
  | ⟨24, _⟩ => exact essential_n29_k24
  | ⟨25, _⟩ => exact essential_n29_k25
  | ⟨26, _⟩ => exact essential_n29_k26
  | ⟨27, _⟩ => exact essential_n29_k27
  | ⟨28, _⟩ => exact essential_n29_k28
  | ⟨29, _⟩ => exact essential_n29_k29
  | ⟨30, _⟩ => exact essential_n29_k30
  | ⟨31, _⟩ => exact essential_n29_k31
  | ⟨32, _⟩ => exact essential_n29_k32
  | ⟨33, _⟩ => exact essential_n29_k33
  | ⟨34, _⟩ => exact essential_n29_k34
  | ⟨35, _⟩ => exact essential_n29_k35
  | ⟨36, _⟩ => exact essential_n29_k36
  | ⟨37, _⟩ => exact essential_n29_k37
  | ⟨38, _⟩ => exact essential_n29_k38
  | ⟨39, _⟩ => exact essential_n29_k39
  | ⟨40, _⟩ => exact essential_n29_k40
  | ⟨41, _⟩ => exact essential_n29_k41
  | ⟨42, _⟩ => exact essential_n29_k42
  | ⟨43, _⟩ => exact essential_n29_k43
  | ⟨44, _⟩ => exact essential_n29_k44
  | ⟨45, _⟩ => exact essential_n29_k45
  | ⟨46, _⟩ => exact essential_n29_k46
  | ⟨47, _⟩ => exact essential_n29_k47
  | ⟨48, _⟩ => exact essential_n29_k48
  | ⟨49, _⟩ => exact essential_n29_k49
  | ⟨50, _⟩ => exact essential_n29_k50
  | ⟨51, _⟩ => exact essential_n29_k51
  | ⟨52, _⟩ => exact essential_n29_k52
  | ⟨53, _⟩ => exact essential_n29_k53
  | ⟨54, _⟩ => exact essential_n29_k54
  | ⟨55, _⟩ => exact essential_n29_k55
  | ⟨56, _⟩ => exact essential_n29_k56
  | ⟨57, _⟩ => exact essential_n29_k57
  | ⟨58, _⟩ => exact essential_n29_k58
  | ⟨k_val + 59, h⟩ => omega

theorem cast_essential_n31 (k : Fin 63) : Essential 31 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n31_k0
  | ⟨1, _⟩ => exact essential_n31_k1
  | ⟨2, _⟩ => exact essential_n31_k2
  | ⟨3, _⟩ => exact essential_n31_k3
  | ⟨4, _⟩ => exact essential_n31_k4
  | ⟨5, _⟩ => exact essential_n31_k5
  | ⟨6, _⟩ => exact essential_n31_k6
  | ⟨7, _⟩ => exact essential_n31_k7
  | ⟨8, _⟩ => exact essential_n31_k8
  | ⟨9, _⟩ => exact essential_n31_k9
  | ⟨10, _⟩ => exact essential_n31_k10
  | ⟨11, _⟩ => exact essential_n31_k11
  | ⟨12, _⟩ => exact essential_n31_k12
  | ⟨13, _⟩ => exact essential_n31_k13
  | ⟨14, _⟩ => exact essential_n31_k14
  | ⟨15, _⟩ => exact essential_n31_k15
  | ⟨16, _⟩ => exact essential_n31_k16
  | ⟨17, _⟩ => exact essential_n31_k17
  | ⟨18, _⟩ => exact essential_n31_k18
  | ⟨19, _⟩ => exact essential_n31_k19
  | ⟨20, _⟩ => exact essential_n31_k20
  | ⟨21, _⟩ => exact essential_n31_k21
  | ⟨22, _⟩ => exact essential_n31_k22
  | ⟨23, _⟩ => exact essential_n31_k23
  | ⟨24, _⟩ => exact essential_n31_k24
  | ⟨25, _⟩ => exact essential_n31_k25
  | ⟨26, _⟩ => exact essential_n31_k26
  | ⟨27, _⟩ => exact essential_n31_k27
  | ⟨28, _⟩ => exact essential_n31_k28
  | ⟨29, _⟩ => exact essential_n31_k29
  | ⟨30, _⟩ => exact essential_n31_k30
  | ⟨31, _⟩ => exact essential_n31_k31
  | ⟨32, _⟩ => exact essential_n31_k32
  | ⟨33, _⟩ => exact essential_n31_k33
  | ⟨34, _⟩ => exact essential_n31_k34
  | ⟨35, _⟩ => exact essential_n31_k35
  | ⟨36, _⟩ => exact essential_n31_k36
  | ⟨37, _⟩ => exact essential_n31_k37
  | ⟨38, _⟩ => exact essential_n31_k38
  | ⟨39, _⟩ => exact essential_n31_k39
  | ⟨40, _⟩ => exact essential_n31_k40
  | ⟨41, _⟩ => exact essential_n31_k41
  | ⟨42, _⟩ => exact essential_n31_k42
  | ⟨43, _⟩ => exact essential_n31_k43
  | ⟨44, _⟩ => exact essential_n31_k44
  | ⟨45, _⟩ => exact essential_n31_k45
  | ⟨46, _⟩ => exact essential_n31_k46
  | ⟨47, _⟩ => exact essential_n31_k47
  | ⟨48, _⟩ => exact essential_n31_k48
  | ⟨49, _⟩ => exact essential_n31_k49
  | ⟨50, _⟩ => exact essential_n31_k50
  | ⟨51, _⟩ => exact essential_n31_k51
  | ⟨52, _⟩ => exact essential_n31_k52
  | ⟨53, _⟩ => exact essential_n31_k53
  | ⟨54, _⟩ => exact essential_n31_k54
  | ⟨55, _⟩ => exact essential_n31_k55
  | ⟨56, _⟩ => exact essential_n31_k56
  | ⟨57, _⟩ => exact essential_n31_k57
  | ⟨58, _⟩ => exact essential_n31_k58
  | ⟨59, _⟩ => exact essential_n31_k59
  | ⟨60, _⟩ => exact essential_n31_k60
  | ⟨61, _⟩ => exact essential_n31_k61
  | ⟨62, _⟩ => exact essential_n31_k62
  | ⟨k_val + 63, h⟩ => omega

theorem cast_essential_n32 (k : Fin 65) : Essential 32 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n32_k0
  | ⟨1, _⟩ => exact essential_n32_k1
  | ⟨2, _⟩ => exact essential_n32_k2
  | ⟨3, _⟩ => exact essential_n32_k3
  | ⟨4, _⟩ => exact essential_n32_k4
  | ⟨5, _⟩ => exact essential_n32_k5
  | ⟨6, _⟩ => exact essential_n32_k6
  | ⟨7, _⟩ => exact essential_n32_k7
  | ⟨8, _⟩ => exact essential_n32_k8
  | ⟨9, _⟩ => exact essential_n32_k9
  | ⟨10, _⟩ => exact essential_n32_k10
  | ⟨11, _⟩ => exact essential_n32_k11
  | ⟨12, _⟩ => exact essential_n32_k12
  | ⟨13, _⟩ => exact essential_n32_k13
  | ⟨14, _⟩ => exact essential_n32_k14
  | ⟨15, _⟩ => exact essential_n32_k15
  | ⟨16, _⟩ => exact essential_n32_k16
  | ⟨17, _⟩ => exact essential_n32_k17
  | ⟨18, _⟩ => exact essential_n32_k18
  | ⟨19, _⟩ => exact essential_n32_k19
  | ⟨20, _⟩ => exact essential_n32_k20
  | ⟨21, _⟩ => exact essential_n32_k21
  | ⟨22, _⟩ => exact essential_n32_k22
  | ⟨23, _⟩ => exact essential_n32_k23
  | ⟨24, _⟩ => exact essential_n32_k24
  | ⟨25, _⟩ => exact essential_n32_k25
  | ⟨26, _⟩ => exact essential_n32_k26
  | ⟨27, _⟩ => exact essential_n32_k27
  | ⟨28, _⟩ => exact essential_n32_k28
  | ⟨29, _⟩ => exact essential_n32_k29
  | ⟨30, _⟩ => exact essential_n32_k30
  | ⟨31, _⟩ => exact essential_n32_k31
  | ⟨32, _⟩ => exact essential_n32_k32
  | ⟨33, _⟩ => exact essential_n32_k33
  | ⟨34, _⟩ => exact essential_n32_k34
  | ⟨35, _⟩ => exact essential_n32_k35
  | ⟨36, _⟩ => exact essential_n32_k36
  | ⟨37, _⟩ => exact essential_n32_k37
  | ⟨38, _⟩ => exact essential_n32_k38
  | ⟨39, _⟩ => exact essential_n32_k39
  | ⟨40, _⟩ => exact essential_n32_k40
  | ⟨41, _⟩ => exact essential_n32_k41
  | ⟨42, _⟩ => exact essential_n32_k42
  | ⟨43, _⟩ => exact essential_n32_k43
  | ⟨44, _⟩ => exact essential_n32_k44
  | ⟨45, _⟩ => exact essential_n32_k45
  | ⟨46, _⟩ => exact essential_n32_k46
  | ⟨47, _⟩ => exact essential_n32_k47
  | ⟨48, _⟩ => exact essential_n32_k48
  | ⟨49, _⟩ => exact essential_n32_k49
  | ⟨50, _⟩ => exact essential_n32_k50
  | ⟨51, _⟩ => exact essential_n32_k51
  | ⟨52, _⟩ => exact essential_n32_k52
  | ⟨53, _⟩ => exact essential_n32_k53
  | ⟨54, _⟩ => exact essential_n32_k54
  | ⟨55, _⟩ => exact essential_n32_k55
  | ⟨56, _⟩ => exact essential_n32_k56
  | ⟨57, _⟩ => exact essential_n32_k57
  | ⟨58, _⟩ => exact essential_n32_k58
  | ⟨59, _⟩ => exact essential_n32_k59
  | ⟨60, _⟩ => exact essential_n32_k60
  | ⟨61, _⟩ => exact essential_n32_k61
  | ⟨62, _⟩ => exact essential_n32_k62
  | ⟨63, _⟩ => exact essential_n32_k63
  | ⟨64, _⟩ => exact essential_n32_k64
  | ⟨k_val + 65, h⟩ => omega

theorem cast_essential_n33 (k : Fin 67) : Essential 33 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n33_k0
  | ⟨1, _⟩ => exact essential_n33_k1
  | ⟨2, _⟩ => exact essential_n33_k2
  | ⟨3, _⟩ => exact essential_n33_k3
  | ⟨4, _⟩ => exact essential_n33_k4
  | ⟨5, _⟩ => exact essential_n33_k5
  | ⟨6, _⟩ => exact essential_n33_k6
  | ⟨7, _⟩ => exact essential_n33_k7
  | ⟨8, _⟩ => exact essential_n33_k8
  | ⟨9, _⟩ => exact essential_n33_k9
  | ⟨10, _⟩ => exact essential_n33_k10
  | ⟨11, _⟩ => exact essential_n33_k11
  | ⟨12, _⟩ => exact essential_n33_k12
  | ⟨13, _⟩ => exact essential_n33_k13
  | ⟨14, _⟩ => exact essential_n33_k14
  | ⟨15, _⟩ => exact essential_n33_k15
  | ⟨16, _⟩ => exact essential_n33_k16
  | ⟨17, _⟩ => exact essential_n33_k17
  | ⟨18, _⟩ => exact essential_n33_k18
  | ⟨19, _⟩ => exact essential_n33_k19
  | ⟨20, _⟩ => exact essential_n33_k20
  | ⟨21, _⟩ => exact essential_n33_k21
  | ⟨22, _⟩ => exact essential_n33_k22
  | ⟨23, _⟩ => exact essential_n33_k23
  | ⟨24, _⟩ => exact essential_n33_k24
  | ⟨25, _⟩ => exact essential_n33_k25
  | ⟨26, _⟩ => exact essential_n33_k26
  | ⟨27, _⟩ => exact essential_n33_k27
  | ⟨28, _⟩ => exact essential_n33_k28
  | ⟨29, _⟩ => exact essential_n33_k29
  | ⟨30, _⟩ => exact essential_n33_k30
  | ⟨31, _⟩ => exact essential_n33_k31
  | ⟨32, _⟩ => exact essential_n33_k32
  | ⟨33, _⟩ => exact essential_n33_k33
  | ⟨34, _⟩ => exact essential_n33_k34
  | ⟨35, _⟩ => exact essential_n33_k35
  | ⟨36, _⟩ => exact essential_n33_k36
  | ⟨37, _⟩ => exact essential_n33_k37
  | ⟨38, _⟩ => exact essential_n33_k38
  | ⟨39, _⟩ => exact essential_n33_k39
  | ⟨40, _⟩ => exact essential_n33_k40
  | ⟨41, _⟩ => exact essential_n33_k41
  | ⟨42, _⟩ => exact essential_n33_k42
  | ⟨43, _⟩ => exact essential_n33_k43
  | ⟨44, _⟩ => exact essential_n33_k44
  | ⟨45, _⟩ => exact essential_n33_k45
  | ⟨46, _⟩ => exact essential_n33_k46
  | ⟨47, _⟩ => exact essential_n33_k47
  | ⟨48, _⟩ => exact essential_n33_k48
  | ⟨49, _⟩ => exact essential_n33_k49
  | ⟨50, _⟩ => exact essential_n33_k50
  | ⟨51, _⟩ => exact essential_n33_k51
  | ⟨52, _⟩ => exact essential_n33_k52
  | ⟨53, _⟩ => exact essential_n33_k53
  | ⟨54, _⟩ => exact essential_n33_k54
  | ⟨55, _⟩ => exact essential_n33_k55
  | ⟨56, _⟩ => exact essential_n33_k56
  | ⟨57, _⟩ => exact essential_n33_k57
  | ⟨58, _⟩ => exact essential_n33_k58
  | ⟨59, _⟩ => exact essential_n33_k59
  | ⟨60, _⟩ => exact essential_n33_k60
  | ⟨61, _⟩ => exact essential_n33_k61
  | ⟨62, _⟩ => exact essential_n33_k62
  | ⟨63, _⟩ => exact essential_n33_k63
  | ⟨64, _⟩ => exact essential_n33_k64
  | ⟨65, _⟩ => exact essential_n33_k65
  | ⟨66, _⟩ => exact essential_n33_k66
  | ⟨k_val + 67, h⟩ => omega

theorem cast_essential_n34 (k : Fin 69) : Essential 34 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n34_k0
  | ⟨1, _⟩ => exact essential_n34_k1
  | ⟨2, _⟩ => exact essential_n34_k2
  | ⟨3, _⟩ => exact essential_n34_k3
  | ⟨4, _⟩ => exact essential_n34_k4
  | ⟨5, _⟩ => exact essential_n34_k5
  | ⟨6, _⟩ => exact essential_n34_k6
  | ⟨7, _⟩ => exact essential_n34_k7
  | ⟨8, _⟩ => exact essential_n34_k8
  | ⟨9, _⟩ => exact essential_n34_k9
  | ⟨10, _⟩ => exact essential_n34_k10
  | ⟨11, _⟩ => exact essential_n34_k11
  | ⟨12, _⟩ => exact essential_n34_k12
  | ⟨13, _⟩ => exact essential_n34_k13
  | ⟨14, _⟩ => exact essential_n34_k14
  | ⟨15, _⟩ => exact essential_n34_k15
  | ⟨16, _⟩ => exact essential_n34_k16
  | ⟨17, _⟩ => exact essential_n34_k17
  | ⟨18, _⟩ => exact essential_n34_k18
  | ⟨19, _⟩ => exact essential_n34_k19
  | ⟨20, _⟩ => exact essential_n34_k20
  | ⟨21, _⟩ => exact essential_n34_k21
  | ⟨22, _⟩ => exact essential_n34_k22
  | ⟨23, _⟩ => exact essential_n34_k23
  | ⟨24, _⟩ => exact essential_n34_k24
  | ⟨25, _⟩ => exact essential_n34_k25
  | ⟨26, _⟩ => exact essential_n34_k26
  | ⟨27, _⟩ => exact essential_n34_k27
  | ⟨28, _⟩ => exact essential_n34_k28
  | ⟨29, _⟩ => exact essential_n34_k29
  | ⟨30, _⟩ => exact essential_n34_k30
  | ⟨31, _⟩ => exact essential_n34_k31
  | ⟨32, _⟩ => exact essential_n34_k32
  | ⟨33, _⟩ => exact essential_n34_k33
  | ⟨34, _⟩ => exact essential_n34_k34
  | ⟨35, _⟩ => exact essential_n34_k35
  | ⟨36, _⟩ => exact essential_n34_k36
  | ⟨37, _⟩ => exact essential_n34_k37
  | ⟨38, _⟩ => exact essential_n34_k38
  | ⟨39, _⟩ => exact essential_n34_k39
  | ⟨40, _⟩ => exact essential_n34_k40
  | ⟨41, _⟩ => exact essential_n34_k41
  | ⟨42, _⟩ => exact essential_n34_k42
  | ⟨43, _⟩ => exact essential_n34_k43
  | ⟨44, _⟩ => exact essential_n34_k44
  | ⟨45, _⟩ => exact essential_n34_k45
  | ⟨46, _⟩ => exact essential_n34_k46
  | ⟨47, _⟩ => exact essential_n34_k47
  | ⟨48, _⟩ => exact essential_n34_k48
  | ⟨49, _⟩ => exact essential_n34_k49
  | ⟨50, _⟩ => exact essential_n34_k50
  | ⟨51, _⟩ => exact essential_n34_k51
  | ⟨52, _⟩ => exact essential_n34_k52
  | ⟨53, _⟩ => exact essential_n34_k53
  | ⟨54, _⟩ => exact essential_n34_k54
  | ⟨55, _⟩ => exact essential_n34_k55
  | ⟨56, _⟩ => exact essential_n34_k56
  | ⟨57, _⟩ => exact essential_n34_k57
  | ⟨58, _⟩ => exact essential_n34_k58
  | ⟨59, _⟩ => exact essential_n34_k59
  | ⟨60, _⟩ => exact essential_n34_k60
  | ⟨61, _⟩ => exact essential_n34_k61
  | ⟨62, _⟩ => exact essential_n34_k62
  | ⟨63, _⟩ => exact essential_n34_k63
  | ⟨64, _⟩ => exact essential_n34_k64
  | ⟨65, _⟩ => exact essential_n34_k65
  | ⟨66, _⟩ => exact essential_n34_k66
  | ⟨67, _⟩ => exact essential_n34_k67
  | ⟨68, _⟩ => exact essential_n34_k68
  | ⟨k_val + 69, h⟩ => omega

theorem cast_essential_n35 (k : Fin 71) : Essential 35 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n35_k0
  | ⟨1, _⟩ => exact essential_n35_k1
  | ⟨2, _⟩ => exact essential_n35_k2
  | ⟨3, _⟩ => exact essential_n35_k3
  | ⟨4, _⟩ => exact essential_n35_k4
  | ⟨5, _⟩ => exact essential_n35_k5
  | ⟨6, _⟩ => exact essential_n35_k6
  | ⟨7, _⟩ => exact essential_n35_k7
  | ⟨8, _⟩ => exact essential_n35_k8
  | ⟨9, _⟩ => exact essential_n35_k9
  | ⟨10, _⟩ => exact essential_n35_k10
  | ⟨11, _⟩ => exact essential_n35_k11
  | ⟨12, _⟩ => exact essential_n35_k12
  | ⟨13, _⟩ => exact essential_n35_k13
  | ⟨14, _⟩ => exact essential_n35_k14
  | ⟨15, _⟩ => exact essential_n35_k15
  | ⟨16, _⟩ => exact essential_n35_k16
  | ⟨17, _⟩ => exact essential_n35_k17
  | ⟨18, _⟩ => exact essential_n35_k18
  | ⟨19, _⟩ => exact essential_n35_k19
  | ⟨20, _⟩ => exact essential_n35_k20
  | ⟨21, _⟩ => exact essential_n35_k21
  | ⟨22, _⟩ => exact essential_n35_k22
  | ⟨23, _⟩ => exact essential_n35_k23
  | ⟨24, _⟩ => exact essential_n35_k24
  | ⟨25, _⟩ => exact essential_n35_k25
  | ⟨26, _⟩ => exact essential_n35_k26
  | ⟨27, _⟩ => exact essential_n35_k27
  | ⟨28, _⟩ => exact essential_n35_k28
  | ⟨29, _⟩ => exact essential_n35_k29
  | ⟨30, _⟩ => exact essential_n35_k30
  | ⟨31, _⟩ => exact essential_n35_k31
  | ⟨32, _⟩ => exact essential_n35_k32
  | ⟨33, _⟩ => exact essential_n35_k33
  | ⟨34, _⟩ => exact essential_n35_k34
  | ⟨35, _⟩ => exact essential_n35_k35
  | ⟨36, _⟩ => exact essential_n35_k36
  | ⟨37, _⟩ => exact essential_n35_k37
  | ⟨38, _⟩ => exact essential_n35_k38
  | ⟨39, _⟩ => exact essential_n35_k39
  | ⟨40, _⟩ => exact essential_n35_k40
  | ⟨41, _⟩ => exact essential_n35_k41
  | ⟨42, _⟩ => exact essential_n35_k42
  | ⟨43, _⟩ => exact essential_n35_k43
  | ⟨44, _⟩ => exact essential_n35_k44
  | ⟨45, _⟩ => exact essential_n35_k45
  | ⟨46, _⟩ => exact essential_n35_k46
  | ⟨47, _⟩ => exact essential_n35_k47
  | ⟨48, _⟩ => exact essential_n35_k48
  | ⟨49, _⟩ => exact essential_n35_k49
  | ⟨50, _⟩ => exact essential_n35_k50
  | ⟨51, _⟩ => exact essential_n35_k51
  | ⟨52, _⟩ => exact essential_n35_k52
  | ⟨53, _⟩ => exact essential_n35_k53
  | ⟨54, _⟩ => exact essential_n35_k54
  | ⟨55, _⟩ => exact essential_n35_k55
  | ⟨56, _⟩ => exact essential_n35_k56
  | ⟨57, _⟩ => exact essential_n35_k57
  | ⟨58, _⟩ => exact essential_n35_k58
  | ⟨59, _⟩ => exact essential_n35_k59
  | ⟨60, _⟩ => exact essential_n35_k60
  | ⟨61, _⟩ => exact essential_n35_k61
  | ⟨62, _⟩ => exact essential_n35_k62
  | ⟨63, _⟩ => exact essential_n35_k63
  | ⟨64, _⟩ => exact essential_n35_k64
  | ⟨65, _⟩ => exact essential_n35_k65
  | ⟨66, _⟩ => exact essential_n35_k66
  | ⟨67, _⟩ => exact essential_n35_k67
  | ⟨68, _⟩ => exact essential_n35_k68
  | ⟨69, _⟩ => exact essential_n35_k69
  | ⟨70, _⟩ => exact essential_n35_k70
  | ⟨k_val + 71, h⟩ => omega

theorem cast_essential_n36 (k : Fin 73) : Essential 36 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n36_k0
  | ⟨1, _⟩ => exact essential_n36_k1
  | ⟨2, _⟩ => exact essential_n36_k2
  | ⟨3, _⟩ => exact essential_n36_k3
  | ⟨4, _⟩ => exact essential_n36_k4
  | ⟨5, _⟩ => exact essential_n36_k5
  | ⟨6, _⟩ => exact essential_n36_k6
  | ⟨7, _⟩ => exact essential_n36_k7
  | ⟨8, _⟩ => exact essential_n36_k8
  | ⟨9, _⟩ => exact essential_n36_k9
  | ⟨10, _⟩ => exact essential_n36_k10
  | ⟨11, _⟩ => exact essential_n36_k11
  | ⟨12, _⟩ => exact essential_n36_k12
  | ⟨13, _⟩ => exact essential_n36_k13
  | ⟨14, _⟩ => exact essential_n36_k14
  | ⟨15, _⟩ => exact essential_n36_k15
  | ⟨16, _⟩ => exact essential_n36_k16
  | ⟨17, _⟩ => exact essential_n36_k17
  | ⟨18, _⟩ => exact essential_n36_k18
  | ⟨19, _⟩ => exact essential_n36_k19
  | ⟨20, _⟩ => exact essential_n36_k20
  | ⟨21, _⟩ => exact essential_n36_k21
  | ⟨22, _⟩ => exact essential_n36_k22
  | ⟨23, _⟩ => exact essential_n36_k23
  | ⟨24, _⟩ => exact essential_n36_k24
  | ⟨25, _⟩ => exact essential_n36_k25
  | ⟨26, _⟩ => exact essential_n36_k26
  | ⟨27, _⟩ => exact essential_n36_k27
  | ⟨28, _⟩ => exact essential_n36_k28
  | ⟨29, _⟩ => exact essential_n36_k29
  | ⟨30, _⟩ => exact essential_n36_k30
  | ⟨31, _⟩ => exact essential_n36_k31
  | ⟨32, _⟩ => exact essential_n36_k32
  | ⟨33, _⟩ => exact essential_n36_k33
  | ⟨34, _⟩ => exact essential_n36_k34
  | ⟨35, _⟩ => exact essential_n36_k35
  | ⟨36, _⟩ => exact essential_n36_k36
  | ⟨37, _⟩ => exact essential_n36_k37
  | ⟨38, _⟩ => exact essential_n36_k38
  | ⟨39, _⟩ => exact essential_n36_k39
  | ⟨40, _⟩ => exact essential_n36_k40
  | ⟨41, _⟩ => exact essential_n36_k41
  | ⟨42, _⟩ => exact essential_n36_k42
  | ⟨43, _⟩ => exact essential_n36_k43
  | ⟨44, _⟩ => exact essential_n36_k44
  | ⟨45, _⟩ => exact essential_n36_k45
  | ⟨46, _⟩ => exact essential_n36_k46
  | ⟨47, _⟩ => exact essential_n36_k47
  | ⟨48, _⟩ => exact essential_n36_k48
  | ⟨49, _⟩ => exact essential_n36_k49
  | ⟨50, _⟩ => exact essential_n36_k50
  | ⟨51, _⟩ => exact essential_n36_k51
  | ⟨52, _⟩ => exact essential_n36_k52
  | ⟨53, _⟩ => exact essential_n36_k53
  | ⟨54, _⟩ => exact essential_n36_k54
  | ⟨55, _⟩ => exact essential_n36_k55
  | ⟨56, _⟩ => exact essential_n36_k56
  | ⟨57, _⟩ => exact essential_n36_k57
  | ⟨58, _⟩ => exact essential_n36_k58
  | ⟨59, _⟩ => exact essential_n36_k59
  | ⟨60, _⟩ => exact essential_n36_k60
  | ⟨61, _⟩ => exact essential_n36_k61
  | ⟨62, _⟩ => exact essential_n36_k62
  | ⟨63, _⟩ => exact essential_n36_k63
  | ⟨64, _⟩ => exact essential_n36_k64
  | ⟨65, _⟩ => exact essential_n36_k65
  | ⟨66, _⟩ => exact essential_n36_k66
  | ⟨67, _⟩ => exact essential_n36_k67
  | ⟨68, _⟩ => exact essential_n36_k68
  | ⟨69, _⟩ => exact essential_n36_k69
  | ⟨70, _⟩ => exact essential_n36_k70
  | ⟨71, _⟩ => exact essential_n36_k71
  | ⟨72, _⟩ => exact essential_n36_k72
  | ⟨k_val + 73, h⟩ => omega

theorem cast_essential_n37 (k : Fin 75) : Essential 37 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n37_k0
  | ⟨1, _⟩ => exact essential_n37_k1
  | ⟨2, _⟩ => exact essential_n37_k2
  | ⟨3, _⟩ => exact essential_n37_k3
  | ⟨4, _⟩ => exact essential_n37_k4
  | ⟨5, _⟩ => exact essential_n37_k5
  | ⟨6, _⟩ => exact essential_n37_k6
  | ⟨7, _⟩ => exact essential_n37_k7
  | ⟨8, _⟩ => exact essential_n37_k8
  | ⟨9, _⟩ => exact essential_n37_k9
  | ⟨10, _⟩ => exact essential_n37_k10
  | ⟨11, _⟩ => exact essential_n37_k11
  | ⟨12, _⟩ => exact essential_n37_k12
  | ⟨13, _⟩ => exact essential_n37_k13
  | ⟨14, _⟩ => exact essential_n37_k14
  | ⟨15, _⟩ => exact essential_n37_k15
  | ⟨16, _⟩ => exact essential_n37_k16
  | ⟨17, _⟩ => exact essential_n37_k17
  | ⟨18, _⟩ => exact essential_n37_k18
  | ⟨19, _⟩ => exact essential_n37_k19
  | ⟨20, _⟩ => exact essential_n37_k20
  | ⟨21, _⟩ => exact essential_n37_k21
  | ⟨22, _⟩ => exact essential_n37_k22
  | ⟨23, _⟩ => exact essential_n37_k23
  | ⟨24, _⟩ => exact essential_n37_k24
  | ⟨25, _⟩ => exact essential_n37_k25
  | ⟨26, _⟩ => exact essential_n37_k26
  | ⟨27, _⟩ => exact essential_n37_k27
  | ⟨28, _⟩ => exact essential_n37_k28
  | ⟨29, _⟩ => exact essential_n37_k29
  | ⟨30, _⟩ => exact essential_n37_k30
  | ⟨31, _⟩ => exact essential_n37_k31
  | ⟨32, _⟩ => exact essential_n37_k32
  | ⟨33, _⟩ => exact essential_n37_k33
  | ⟨34, _⟩ => exact essential_n37_k34
  | ⟨35, _⟩ => exact essential_n37_k35
  | ⟨36, _⟩ => exact essential_n37_k36
  | ⟨37, _⟩ => exact essential_n37_k37
  | ⟨38, _⟩ => exact essential_n37_k38
  | ⟨39, _⟩ => exact essential_n37_k39
  | ⟨40, _⟩ => exact essential_n37_k40
  | ⟨41, _⟩ => exact essential_n37_k41
  | ⟨42, _⟩ => exact essential_n37_k42
  | ⟨43, _⟩ => exact essential_n37_k43
  | ⟨44, _⟩ => exact essential_n37_k44
  | ⟨45, _⟩ => exact essential_n37_k45
  | ⟨46, _⟩ => exact essential_n37_k46
  | ⟨47, _⟩ => exact essential_n37_k47
  | ⟨48, _⟩ => exact essential_n37_k48
  | ⟨49, _⟩ => exact essential_n37_k49
  | ⟨50, _⟩ => exact essential_n37_k50
  | ⟨51, _⟩ => exact essential_n37_k51
  | ⟨52, _⟩ => exact essential_n37_k52
  | ⟨53, _⟩ => exact essential_n37_k53
  | ⟨54, _⟩ => exact essential_n37_k54
  | ⟨55, _⟩ => exact essential_n37_k55
  | ⟨56, _⟩ => exact essential_n37_k56
  | ⟨57, _⟩ => exact essential_n37_k57
  | ⟨58, _⟩ => exact essential_n37_k58
  | ⟨59, _⟩ => exact essential_n37_k59
  | ⟨60, _⟩ => exact essential_n37_k60
  | ⟨61, _⟩ => exact essential_n37_k61
  | ⟨62, _⟩ => exact essential_n37_k62
  | ⟨63, _⟩ => exact essential_n37_k63
  | ⟨64, _⟩ => exact essential_n37_k64
  | ⟨65, _⟩ => exact essential_n37_k65
  | ⟨66, _⟩ => exact essential_n37_k66
  | ⟨67, _⟩ => exact essential_n37_k67
  | ⟨68, _⟩ => exact essential_n37_k68
  | ⟨69, _⟩ => exact essential_n37_k69
  | ⟨70, _⟩ => exact essential_n37_k70
  | ⟨71, _⟩ => exact essential_n37_k71
  | ⟨72, _⟩ => exact essential_n37_k72
  | ⟨73, _⟩ => exact essential_n37_k73
  | ⟨74, _⟩ => exact essential_n37_k74
  | ⟨k_val + 75, h⟩ => omega

theorem cast_essential_n38 (k : Fin 77) : Essential 38 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n38_k0
  | ⟨1, _⟩ => exact essential_n38_k1
  | ⟨2, _⟩ => exact essential_n38_k2
  | ⟨3, _⟩ => exact essential_n38_k3
  | ⟨4, _⟩ => exact essential_n38_k4
  | ⟨5, _⟩ => exact essential_n38_k5
  | ⟨6, _⟩ => exact essential_n38_k6
  | ⟨7, _⟩ => exact essential_n38_k7
  | ⟨8, _⟩ => exact essential_n38_k8
  | ⟨9, _⟩ => exact essential_n38_k9
  | ⟨10, _⟩ => exact essential_n38_k10
  | ⟨11, _⟩ => exact essential_n38_k11
  | ⟨12, _⟩ => exact essential_n38_k12
  | ⟨13, _⟩ => exact essential_n38_k13
  | ⟨14, _⟩ => exact essential_n38_k14
  | ⟨15, _⟩ => exact essential_n38_k15
  | ⟨16, _⟩ => exact essential_n38_k16
  | ⟨17, _⟩ => exact essential_n38_k17
  | ⟨18, _⟩ => exact essential_n38_k18
  | ⟨19, _⟩ => exact essential_n38_k19
  | ⟨20, _⟩ => exact essential_n38_k20
  | ⟨21, _⟩ => exact essential_n38_k21
  | ⟨22, _⟩ => exact essential_n38_k22
  | ⟨23, _⟩ => exact essential_n38_k23
  | ⟨24, _⟩ => exact essential_n38_k24
  | ⟨25, _⟩ => exact essential_n38_k25
  | ⟨26, _⟩ => exact essential_n38_k26
  | ⟨27, _⟩ => exact essential_n38_k27
  | ⟨28, _⟩ => exact essential_n38_k28
  | ⟨29, _⟩ => exact essential_n38_k29
  | ⟨30, _⟩ => exact essential_n38_k30
  | ⟨31, _⟩ => exact essential_n38_k31
  | ⟨32, _⟩ => exact essential_n38_k32
  | ⟨33, _⟩ => exact essential_n38_k33
  | ⟨34, _⟩ => exact essential_n38_k34
  | ⟨35, _⟩ => exact essential_n38_k35
  | ⟨36, _⟩ => exact essential_n38_k36
  | ⟨37, _⟩ => exact essential_n38_k37
  | ⟨38, _⟩ => exact essential_n38_k38
  | ⟨39, _⟩ => exact essential_n38_k39
  | ⟨40, _⟩ => exact essential_n38_k40
  | ⟨41, _⟩ => exact essential_n38_k41
  | ⟨42, _⟩ => exact essential_n38_k42
  | ⟨43, _⟩ => exact essential_n38_k43
  | ⟨44, _⟩ => exact essential_n38_k44
  | ⟨45, _⟩ => exact essential_n38_k45
  | ⟨46, _⟩ => exact essential_n38_k46
  | ⟨47, _⟩ => exact essential_n38_k47
  | ⟨48, _⟩ => exact essential_n38_k48
  | ⟨49, _⟩ => exact essential_n38_k49
  | ⟨50, _⟩ => exact essential_n38_k50
  | ⟨51, _⟩ => exact essential_n38_k51
  | ⟨52, _⟩ => exact essential_n38_k52
  | ⟨53, _⟩ => exact essential_n38_k53
  | ⟨54, _⟩ => exact essential_n38_k54
  | ⟨55, _⟩ => exact essential_n38_k55
  | ⟨56, _⟩ => exact essential_n38_k56
  | ⟨57, _⟩ => exact essential_n38_k57
  | ⟨58, _⟩ => exact essential_n38_k58
  | ⟨59, _⟩ => exact essential_n38_k59
  | ⟨60, _⟩ => exact essential_n38_k60
  | ⟨61, _⟩ => exact essential_n38_k61
  | ⟨62, _⟩ => exact essential_n38_k62
  | ⟨63, _⟩ => exact essential_n38_k63
  | ⟨64, _⟩ => exact essential_n38_k64
  | ⟨65, _⟩ => exact essential_n38_k65
  | ⟨66, _⟩ => exact essential_n38_k66
  | ⟨67, _⟩ => exact essential_n38_k67
  | ⟨68, _⟩ => exact essential_n38_k68
  | ⟨69, _⟩ => exact essential_n38_k69
  | ⟨70, _⟩ => exact essential_n38_k70
  | ⟨71, _⟩ => exact essential_n38_k71
  | ⟨72, _⟩ => exact essential_n38_k72
  | ⟨73, _⟩ => exact essential_n38_k73
  | ⟨74, _⟩ => exact essential_n38_k74
  | ⟨75, _⟩ => exact essential_n38_k75
  | ⟨76, _⟩ => exact essential_n38_k76
  | ⟨k_val + 77, h⟩ => omega

theorem cast_essential_n39 (k : Fin 79) : Essential 39 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n39_k0
  | ⟨1, _⟩ => exact essential_n39_k1
  | ⟨2, _⟩ => exact essential_n39_k2
  | ⟨3, _⟩ => exact essential_n39_k3
  | ⟨4, _⟩ => exact essential_n39_k4
  | ⟨5, _⟩ => exact essential_n39_k5
  | ⟨6, _⟩ => exact essential_n39_k6
  | ⟨7, _⟩ => exact essential_n39_k7
  | ⟨8, _⟩ => exact essential_n39_k8
  | ⟨9, _⟩ => exact essential_n39_k9
  | ⟨10, _⟩ => exact essential_n39_k10
  | ⟨11, _⟩ => exact essential_n39_k11
  | ⟨12, _⟩ => exact essential_n39_k12
  | ⟨13, _⟩ => exact essential_n39_k13
  | ⟨14, _⟩ => exact essential_n39_k14
  | ⟨15, _⟩ => exact essential_n39_k15
  | ⟨16, _⟩ => exact essential_n39_k16
  | ⟨17, _⟩ => exact essential_n39_k17
  | ⟨18, _⟩ => exact essential_n39_k18
  | ⟨19, _⟩ => exact essential_n39_k19
  | ⟨20, _⟩ => exact essential_n39_k20
  | ⟨21, _⟩ => exact essential_n39_k21
  | ⟨22, _⟩ => exact essential_n39_k22
  | ⟨23, _⟩ => exact essential_n39_k23
  | ⟨24, _⟩ => exact essential_n39_k24
  | ⟨25, _⟩ => exact essential_n39_k25
  | ⟨26, _⟩ => exact essential_n39_k26
  | ⟨27, _⟩ => exact essential_n39_k27
  | ⟨28, _⟩ => exact essential_n39_k28
  | ⟨29, _⟩ => exact essential_n39_k29
  | ⟨30, _⟩ => exact essential_n39_k30
  | ⟨31, _⟩ => exact essential_n39_k31
  | ⟨32, _⟩ => exact essential_n39_k32
  | ⟨33, _⟩ => exact essential_n39_k33
  | ⟨34, _⟩ => exact essential_n39_k34
  | ⟨35, _⟩ => exact essential_n39_k35
  | ⟨36, _⟩ => exact essential_n39_k36
  | ⟨37, _⟩ => exact essential_n39_k37
  | ⟨38, _⟩ => exact essential_n39_k38
  | ⟨39, _⟩ => exact essential_n39_k39
  | ⟨40, _⟩ => exact essential_n39_k40
  | ⟨41, _⟩ => exact essential_n39_k41
  | ⟨42, _⟩ => exact essential_n39_k42
  | ⟨43, _⟩ => exact essential_n39_k43
  | ⟨44, _⟩ => exact essential_n39_k44
  | ⟨45, _⟩ => exact essential_n39_k45
  | ⟨46, _⟩ => exact essential_n39_k46
  | ⟨47, _⟩ => exact essential_n39_k47
  | ⟨48, _⟩ => exact essential_n39_k48
  | ⟨49, _⟩ => exact essential_n39_k49
  | ⟨50, _⟩ => exact essential_n39_k50
  | ⟨51, _⟩ => exact essential_n39_k51
  | ⟨52, _⟩ => exact essential_n39_k52
  | ⟨53, _⟩ => exact essential_n39_k53
  | ⟨54, _⟩ => exact essential_n39_k54
  | ⟨55, _⟩ => exact essential_n39_k55
  | ⟨56, _⟩ => exact essential_n39_k56
  | ⟨57, _⟩ => exact essential_n39_k57
  | ⟨58, _⟩ => exact essential_n39_k58
  | ⟨59, _⟩ => exact essential_n39_k59
  | ⟨60, _⟩ => exact essential_n39_k60
  | ⟨61, _⟩ => exact essential_n39_k61
  | ⟨62, _⟩ => exact essential_n39_k62
  | ⟨63, _⟩ => exact essential_n39_k63
  | ⟨64, _⟩ => exact essential_n39_k64
  | ⟨65, _⟩ => exact essential_n39_k65
  | ⟨66, _⟩ => exact essential_n39_k66
  | ⟨67, _⟩ => exact essential_n39_k67
  | ⟨68, _⟩ => exact essential_n39_k68
  | ⟨69, _⟩ => exact essential_n39_k69
  | ⟨70, _⟩ => exact essential_n39_k70
  | ⟨71, _⟩ => exact essential_n39_k71
  | ⟨72, _⟩ => exact essential_n39_k72
  | ⟨73, _⟩ => exact essential_n39_k73
  | ⟨74, _⟩ => exact essential_n39_k74
  | ⟨75, _⟩ => exact essential_n39_k75
  | ⟨76, _⟩ => exact essential_n39_k76
  | ⟨77, _⟩ => exact essential_n39_k77
  | ⟨78, _⟩ => exact essential_n39_k78
  | ⟨k_val + 79, h⟩ => omega

theorem cast_essential_n40 (k : Fin 81) : Essential 40 k := by
  match k with
  | ⟨0, _⟩ => exact essential_n40_k0
  | ⟨1, _⟩ => exact essential_n40_k1
  | ⟨2, _⟩ => exact essential_n40_k2
  | ⟨3, _⟩ => exact essential_n40_k3
  | ⟨4, _⟩ => exact essential_n40_k4
  | ⟨5, _⟩ => exact essential_n40_k5
  | ⟨6, _⟩ => exact essential_n40_k6
  | ⟨7, _⟩ => exact essential_n40_k7
  | ⟨8, _⟩ => exact essential_n40_k8
  | ⟨9, _⟩ => exact essential_n40_k9
  | ⟨10, _⟩ => exact essential_n40_k10
  | ⟨11, _⟩ => exact essential_n40_k11
  | ⟨12, _⟩ => exact essential_n40_k12
  | ⟨13, _⟩ => exact essential_n40_k13
  | ⟨14, _⟩ => exact essential_n40_k14
  | ⟨15, _⟩ => exact essential_n40_k15
  | ⟨16, _⟩ => exact essential_n40_k16
  | ⟨17, _⟩ => exact essential_n40_k17
  | ⟨18, _⟩ => exact essential_n40_k18
  | ⟨19, _⟩ => exact essential_n40_k19
  | ⟨20, _⟩ => exact essential_n40_k20
  | ⟨21, _⟩ => exact essential_n40_k21
  | ⟨22, _⟩ => exact essential_n40_k22
  | ⟨23, _⟩ => exact essential_n40_k23
  | ⟨24, _⟩ => exact essential_n40_k24
  | ⟨25, _⟩ => exact essential_n40_k25
  | ⟨26, _⟩ => exact essential_n40_k26
  | ⟨27, _⟩ => exact essential_n40_k27
  | ⟨28, _⟩ => exact essential_n40_k28
  | ⟨29, _⟩ => exact essential_n40_k29
  | ⟨30, _⟩ => exact essential_n40_k30
  | ⟨31, _⟩ => exact essential_n40_k31
  | ⟨32, _⟩ => exact essential_n40_k32
  | ⟨33, _⟩ => exact essential_n40_k33
  | ⟨34, _⟩ => exact essential_n40_k34
  | ⟨35, _⟩ => exact essential_n40_k35
  | ⟨36, _⟩ => exact essential_n40_k36
  | ⟨37, _⟩ => exact essential_n40_k37
  | ⟨38, _⟩ => exact essential_n40_k38
  | ⟨39, _⟩ => exact essential_n40_k39
  | ⟨40, _⟩ => exact essential_n40_k40
  | ⟨41, _⟩ => exact essential_n40_k41
  | ⟨42, _⟩ => exact essential_n40_k42
  | ⟨43, _⟩ => exact essential_n40_k43
  | ⟨44, _⟩ => exact essential_n40_k44
  | ⟨45, _⟩ => exact essential_n40_k45
  | ⟨46, _⟩ => exact essential_n40_k46
  | ⟨47, _⟩ => exact essential_n40_k47
  | ⟨48, _⟩ => exact essential_n40_k48
  | ⟨49, _⟩ => exact essential_n40_k49
  | ⟨50, _⟩ => exact essential_n40_k50
  | ⟨51, _⟩ => exact essential_n40_k51
  | ⟨52, _⟩ => exact essential_n40_k52
  | ⟨53, _⟩ => exact essential_n40_k53
  | ⟨54, _⟩ => exact essential_n40_k54
  | ⟨55, _⟩ => exact essential_n40_k55
  | ⟨56, _⟩ => exact essential_n40_k56
  | ⟨57, _⟩ => exact essential_n40_k57
  | ⟨58, _⟩ => exact essential_n40_k58
  | ⟨59, _⟩ => exact essential_n40_k59
  | ⟨60, _⟩ => exact essential_n40_k60
  | ⟨61, _⟩ => exact essential_n40_k61
  | ⟨62, _⟩ => exact essential_n40_k62
  | ⟨63, _⟩ => exact essential_n40_k63
  | ⟨64, _⟩ => exact essential_n40_k64
  | ⟨65, _⟩ => exact essential_n40_k65
  | ⟨66, _⟩ => exact essential_n40_k66
  | ⟨67, _⟩ => exact essential_n40_k67
  | ⟨68, _⟩ => exact essential_n40_k68
  | ⟨69, _⟩ => exact essential_n40_k69
  | ⟨70, _⟩ => exact essential_n40_k70
  | ⟨71, _⟩ => exact essential_n40_k71
  | ⟨72, _⟩ => exact essential_n40_k72
  | ⟨73, _⟩ => exact essential_n40_k73
  | ⟨74, _⟩ => exact essential_n40_k74
  | ⟨75, _⟩ => exact essential_n40_k75
  | ⟨76, _⟩ => exact essential_n40_k76
  | ⟨77, _⟩ => exact essential_n40_k77
  | ⟨78, _⟩ => exact essential_n40_k78
  | ⟨79, _⟩ => exact essential_n40_k79
  | ⟨80, _⟩ => exact essential_n40_k80
  | ⟨k_val + 81, h⟩ => omega


-- ============================================================================
-- NOTE: Witnesses for n=41..240 were computed with a BUGGY Python script
-- (2026-03-13 discovery). The bug: original script compared full bigint outputs
-- rather than bit 0 only (the actual Lean rule30n output). ~50% of witnesses
-- were invalid (only higher bits differed, not the actual output bit).
--
-- FIX: We restructure the proof to use the inductive lifting lemma for ALL n≥41.
-- This eliminates the need for explicit witnesses for n=41..240 entirely.
-- Only n=1..40 witnesses remain (Lean-verified with native_decide, correct).
-- ============================================================================

-- ─── Inductive proof for n ≥ 41 (using lifting_lemma from n=40) ──────────────

/-- For any n ≥ 41, all cells are essential.
    Uses induction with lifting_lemma, starting from the verified n=40 base.
    IMPORTANT: This proof depends on lifting_lemma which uses z3_lifting_step axiom. -/
theorem essential_for_all_large_n (n : Nat) (k : Fin (2 * n + 1)) (hn : n ≥ 41) :
    Essential n k := by
  -- Induct on m = n - 41, mirroring the pattern of the original essential_for_large_n
  let m := n - 41
  induction m generalizing k with
  | zero =>
    -- Base case: n = 41, lift interior from cast_essential_n40
    have hn' : n = 41 := by omega
    subst hn'
    by_cases hk0 : k.val = 0
    · -- Left boundary
      have : k = ⟨0, by omega⟩ := Fin.ext hk0
      rw [this]; exact essential_left_boundary 41
    · by_cases hkmax : k.val = 2 * 41
      · -- Right boundary
        have : k = ⟨82, by omega⟩ := Fin.ext hkmax
        rw [this]; exact essential_right_boundary 41 (by omega)
      · -- Interior: lift from n=40
        have h40 : Essential 40 ⟨k.val - 1, by
            have : k.val > 0 := Nat.pos_of_ne_zero hk0
            have : k.val < 2 * 41 := by intro h; apply hkmax; omega
            omega⟩ := cast_essential_n40 _
        exact lifting_lemma 40 ⟨k.val - 1, by omega⟩ h40
  | succ m ih =>
    -- Inductive step: lift from n = 41 + m to n = 42 + m
    let n := 41 + m + 1
    by_cases hk0 : k.val = 0
    · -- Left boundary
      have : k = ⟨0, by omega⟩ := Fin.ext hk0
      rw [this]; exact essential_left_boundary n
    · by_cases hkmax : k.val = 2 * n
      · -- Right boundary
        have : k = ⟨2 * n, by omega⟩ := Fin.ext hkmax
        rw [this]; exact essential_right_boundary n (by omega)
      · -- Interior: lift from previous n
        have hprev : Essential (n - 1) ⟨k.val - 1, by
            have : k.val > 0 := Nat.pos_of_ne_zero hk0
            have : k.val < 2 * n := by intro h; apply hkmax; omega
            omega⟩ := ih ⟨k.val - 1, by omega⟩
        exact lifting_lemma (n - 1) ⟨k.val - 1, by omega⟩ hprev

/-- Unified theorem: all cells are essential for all n ≥ 1.
    Uses explicit witnesses for n=1..40 (Lean-verified) and inductive proof for n≥41. -/
theorem all_cells_essential (n : Nat) (k : Fin (2 * n + 1)) (hn : n ≥ 1) :
    Essential n k := by
  by_cases h : n ≤ 40
  · -- Small n (1..40): use explicit, Lean-verified cast_essential theorems
    interval_cases n <;> exact cast_essential_n1 k
    <;> try exact cast_essential_n2 k
    <;> try exact cast_essential_n3 k
    <;> try exact cast_essential_n4 k
    <;> try exact cast_essential_n5 k
    <;> try exact cast_essential_n6 k
    <;> try exact cast_essential_n7 k
    <;> try exact cast_essential_n8 k
    <;> try exact cast_essential_n9 k
    <;> try exact cast_essential_n10 k
    <;> try exact cast_essential_n11 k
    <;> try exact cast_essential_n12 k
    <;> try exact cast_essential_n13 k
    <;> try exact cast_essential_n14 k
    <;> try exact cast_essential_n15 k
    <;> try exact cast_essential_n16 k
    <;> try exact cast_essential_n17 k
    <;> try exact cast_essential_n18 k
    <;> try exact cast_essential_n19 k
    <;> try exact cast_essential_n20 k
    <;> try exact cast_essential_n21 k
    <;> try exact cast_essential_n22 k
    <;> try exact cast_essential_n23 k
    <;> try exact cast_essential_n24 k
    <;> try exact cast_essential_n25 k
    <;> try exact cast_essential_n26 k
    <;> try exact cast_essential_n27 k
    <;> try exact cast_essential_n28 k
    <;> try exact cast_essential_n29 k
    <;> try exact cast_essential_n30 k
    <;> try exact cast_essential_n31 k
    <;> try exact cast_essential_n32 k
    <;> try exact cast_essential_n33 k
    <;> try exact cast_essential_n34 k
    <;> try exact cast_essential_n35 k
    <;> try exact cast_essential_n36 k
    <;> try exact cast_essential_n37 k
    <;> try exact cast_essential_n38 k
    <;> try exact cast_essential_n39 k
    <;> try exact cast_essential_n40 k
  · -- Large n (≥ 41): use inductive lifting lemma from n=40
    push_neg at h
    exact essential_for_all_large_n n k (by omega)
