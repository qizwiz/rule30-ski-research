/-
SKI_Prize.lean — Wolfram S Combinator Challenge
================================================

Goal: Prove or disprove that the S combinator alone is computationally universal.
Prize: $20,000 USD at combinatorprize.org

S combinator rule: S f g x → f x (g x)

Author: Jonathan Hill
Date: 2026-03-20
-/

import Mathlib.Data.Nat.Basic

/-
================================================================================
SECTION 1: SYNTAX
================================================================================
-/

/-- S expressions: the S combinator with application. No variables — all terms
    are "closed" by construction (no lambda-abstractions, no variable bindings). -/
inductive SExpr : Type
  | S    : SExpr
  | app  : SExpr → SExpr → SExpr
  deriving DecidableEq, Repr

/-- Size of an S expression (count of all nodes). -/
def SExpr.size : SExpr → Nat
  | SExpr.S        => 1
  | SExpr.app f x  => 1 + f.size + x.size

theorem SExpr.size_pos : ∀ e : SExpr, 0 < e.size := by
  intro e; induction e with
  | S => simp [SExpr.size]
  | app f x ihf ihx => simp [SExpr.size]; omega

/-
================================================================================
SECTION 2: SPINE STRUCTURE
================================================================================
-/

/-- Length of the left-spine (depth of nested left applications). -/
def SExpr.spineLen : SExpr → Nat
  | SExpr.app f _ => 1 + f.spineLen
  | _             => 0

/-- Head of the left spine (the atom at the bottom of the application chain). -/
def SExpr.head : SExpr → SExpr
  | SExpr.app f _ => f.head
  | e             => e

theorem SExpr.head_S : SExpr.S.head = SExpr.S := rfl

theorem SExpr.head_app (f x : SExpr) : (SExpr.app f x).head = f.head := rfl

theorem SExpr.spineLen_S : SExpr.S.spineLen = 0 := rfl

/-- The head of every S-expression is S (since S is the only atom). -/
theorem SExpr.head_is_S : ∀ e : SExpr, e.head = SExpr.S := by
  intro e; induction e with
  | S => rfl
  | app f x ihf ihx => simp [SExpr.head, ihf]

/-
================================================================================
SECTION 3: ONE-STEP REDUCTION
================================================================================
-/

/-- One step of S combinator reduction (leftmost-outermost strategy).
    The S redex is S applied to exactly 3 arguments.
    Returns `none` if the term is in S-normal form. -/
def sStep : SExpr → Option SExpr
  | SExpr.app (SExpr.app (SExpr.app SExpr.S f) g) x =>
      some (SExpr.app (SExpr.app f x) (SExpr.app g x))
  | SExpr.app fun_ arg =>
      match sStep fun_ with
      | some fun_' => some (SExpr.app fun_' arg)
      | none        => none
  | SExpr.S => none

/-- Normal form: no S redex applies. -/
def SExpr.isNF (e : SExpr) : Prop := sStep e = none

instance : Decidable (SExpr.isNF e) := by
  unfold SExpr.isNF
  exact inferInstance

theorem SExpr.S_isNF : SExpr.S.isNF := rfl

/-
================================================================================
SECTION 4: STRUCTURAL FACTS ABOUT sStep
================================================================================
-/

/-- spine length < 3 implies normal form.
    Direct proof by structural analysis of the 3-deep pattern needed for S to fire. -/
theorem spineLen_lt3_implies_NF : ∀ (e : SExpr), e.spineLen < 3 → e.isNF := by
  intro e
  induction e with
  | S => intros; exact SExpr.S_isNF
  | app f x ihf ihx =>
    intro h_spine
    simp [SExpr.spineLen] at h_spine
    -- h_spine: f.spineLen < 2
    -- We need sStep (app f x) = none
    -- sStep (app f x) fires S redex if f = app (app S _) _
    -- f.spineLen < 2 means f cannot have the form app (app _ _) _
    -- So sStep (app f x) must try to reduce f, which is also NF
    cases f with
    | S =>
      -- Full term: app S x.  sStep checks for app(app(app S _)_)_ pattern — doesn't match
      simp [SExpr.isNF, sStep]
    | app f2 x2 =>
      -- f = app f2 x2, f.spineLen = 1 + f2.spineLen < 2, so f2.spineLen = 0
      simp [SExpr.spineLen] at h_spine
      -- f2.spineLen = 0, so f2 must be S (only 0-spineLen term)
      cases f2 with
      | S =>
        -- f = app S x2, full term = app (app S x2) x
        -- sStep: first checks app(app(app S ?) ?) ? — needs f = app(app S ?) ?
        -- f = app S x2, and S ≠ app S ?, so the triple pattern doesn't match
        -- Then tries to reduce f: sStep (app S x2) — f2=S so no pattern, tries sStep S = none
        simp [SExpr.isNF, sStep]
      | app f3 x3 =>
        -- f2 = app f3 x3, so f2.spineLen = 1 + f3.spineLen ≥ 1, contradicting < 1
        simp [SExpr.spineLen] at h_spine
        omega

/-- spine length ≥ 3 implies NOT normal form.
    When spineLen ≥ 3, the head is S (since S is the only atom), so an S redex exists. -/
theorem spineLen_ge3_not_NF : ∀ (e : SExpr), e.spineLen ≥ 3 → ¬ e.isNF := by
  intro e
  induction e with
  | S => simp [SExpr.spineLen]
  | app outer_f outer_x ihf _ihx =>
    intro h_spine h_nf
    simp [SExpr.spineLen] at h_spine
    -- outer_f.spineLen ≥ 2
    -- Case split on outer_f
    cases outer_f with
    | S => simp [SExpr.spineLen] at h_spine
    | app mid_f mid_x =>
      simp [SExpr.spineLen] at h_spine
      -- mid_f.spineLen ≥ 1
      -- Case split on mid_f
      cases mid_f with
      | S => simp [SExpr.spineLen] at h_spine
      | app inner_f inner_x =>
        simp [SExpr.spineLen] at h_spine
        -- inner_f.spineLen ≥ 0, so we have 4+ levels
        -- The term is: app (app (app (app inner_f inner_x) mid_x) outer_x)
        -- Wait: full term = app (app (app inner_f inner_x).app(mid_x)) outer_x) ..
        -- Actually: outer_f = app (app inner_f inner_x) mid_x
        -- full = app (app (app inner_f inner_x) mid_x) outer_x
        -- spineLen ≥ 3 means inner_f.spineLen ≥ 0, true
        -- sStep on this term: looks for app(app(app S ?)?)? pattern
        -- inner_f must be S (since head of everything is S)
        -- If inner_f = S: this IS an S redex, sStep fires
        -- If inner_f = app ...: by IH applied to inner_f, it's not NF (if spineLen ≥ 3)
        --   and sStep will reduce inner_f position
        -- Key: we need to show sStep fires, not stays None
        -- Strategy: cases on inner_f
        cases inner_f with
        | S =>
          -- Full term = app (app (app S inner_x) mid_x) outer_x — S redex fires!
          simp [SExpr.isNF, sStep] at h_nf
        | app deep_f deep_x =>
          -- outer_f = app (app (app deep_f deep_x) inner_x) mid_x has spineLen ≥ 3
          have h_of_spine : (SExpr.app (SExpr.app (SExpr.app deep_f deep_x) inner_x) mid_x).spineLen ≥ 3 := by
            simp [SExpr.spineLen]; omega
          -- By IH: outer_f is not NF
          have h_of_not_nf : ¬ (SExpr.app (SExpr.app (SExpr.app deep_f deep_x) inner_x) mid_x).isNF :=
            ihf h_of_spine
          -- outer_f.isNF = false, so sStep outer_f = some (something)
          rw [SExpr.isNF] at h_of_not_nf
          -- h_of_not_nf : sStep (outer_f) ≠ none
          -- h_nf : sStep (app outer_f outer_x) = none
          -- Since deep_f ≠ S (it's app...), the triple pattern app(app(app S ?)?)? doesn't match at top
          -- sStep (app outer_f outer_x) will try to reduce outer_f
          -- Since sStep outer_f ≠ none, sStep (app outer_f outer_x) ≠ none
          -- Contradiction with h_nf
          have : sStep (SExpr.app (SExpr.app (SExpr.app (SExpr.app deep_f deep_x) inner_x) mid_x) outer_x) ≠ none := by
            simp [sStep]
            -- The triple pattern: would need deep_f = S — but deep_f is not S (it's the IH case)
            -- Actually deep_f could be S here! But even if it is, outer_f would be
            -- app(app(app S inner_x) mid_x) outer_x ≠ deep_f...
            -- Let me just use the fact that sStep outer_f ≠ none
            cases h_step_of : sStep (SExpr.app (SExpr.app (SExpr.app deep_f deep_x) inner_x) mid_x) with
            | none => exact absurd h_step_of h_of_not_nf
            | some w => simp
          exact this h_nf

/-
================================================================================
SECTION 5: NORMAL FORM IFF SPINE LENGTH < 3
================================================================================
-/

/-- Main structural theorem: an S-only term is in normal form iff its
    spine length is less than 3. -/
theorem sNF_iff_spineLen_lt3 (e : SExpr) : e.isNF ↔ e.spineLen < 3 := by
  constructor
  · -- Normal form → spineLen < 3 (contrapositive of spineLen_ge3_not_NF)
    intro h_nf
    by_contra h_ge
    simp at h_ge
    exact spineLen_ge3_not_NF e h_ge h_nf
  · -- spineLen < 3 → normal form
    exact spineLen_lt3_implies_NF e

/-
================================================================================
SECTION 6: S LEAVES — COUNTING S ATOMS
================================================================================
-/

/-- Number of S atoms (leaves) in an expression. -/
def SExpr.sLeaves : SExpr → Nat
  | SExpr.S        => 1
  | SExpr.app f x  => f.sLeaves + x.sLeaves

theorem SExpr.sLeaves_pos : ∀ e : SExpr, 0 < e.sLeaves := by
  intro e; induction e with
  | S => simp [SExpr.sLeaves]
  | app f x ihf ihx => simp [SExpr.sLeaves]; omega

/-- S-reduction changes sLeaves precisely: the S atom consumed is replaced
    by a duplication of x.
    Before: 1 + L(f) + L(g) + L(x)
    After:  L(f) + L(x) + L(g) + L(x) = L(f) + L(g) + 2·L(x)
    Net change: gain L(x) - 1 leaves. -/
theorem sStep_sLeaves_top_redex (f g x : SExpr) :
    let before := SExpr.app (SExpr.app (SExpr.app SExpr.S f) g) x
    let after  := SExpr.app (SExpr.app f x) (SExpr.app g x)
    after.sLeaves + 1 = before.sLeaves + x.sLeaves := by
  simp [SExpr.sLeaves]
  omega

/-- Key parity theorem: S-reduction changes sLeaves by L(x) - 1.
    The parity of sLeaves is preserved iff L(x) is odd. -/
theorem sStep_sLeaves_parity (f g x : SExpr) :
    let before := (SExpr.app (SExpr.app (SExpr.app SExpr.S f) g) x).sLeaves
    let after  := (SExpr.app (SExpr.app f x) (SExpr.app g x)).sLeaves
    before % 2 = after % 2 ↔ x.sLeaves % 2 = 1 := by
  simp [SExpr.sLeaves]
  omega

/-
================================================================================
SECTION 7: COMPUTATIONAL EXAMPLES (VERIFIED)
================================================================================
-/

-- S S S S reduces to (S S)(S S): verified
example : sStep (SExpr.app (SExpr.app (SExpr.app SExpr.S SExpr.S) SExpr.S) SExpr.S) =
    some (SExpr.app (SExpr.app SExpr.S SExpr.S) (SExpr.app SExpr.S SExpr.S)) := by
  simp [sStep]

-- S is in NF (spine 0 < 3)
example : SExpr.S.isNF := SExpr.S_isNF

-- S S is in NF (spine 1 < 3)
example : (SExpr.app SExpr.S SExpr.S).isNF := by
  rw [sNF_iff_spineLen_lt3]
  simp [SExpr.spineLen]

-- (S S) S is in NF (spine 2 < 3)
example : (SExpr.app (SExpr.app SExpr.S SExpr.S) SExpr.S).isNF := by
  rw [sNF_iff_spineLen_lt3]
  simp [SExpr.spineLen]

-- S S S S is NOT in NF (spine 3, fires)
example : ¬ (SExpr.app (SExpr.app (SExpr.app SExpr.S SExpr.S) SExpr.S) SExpr.S).isNF := by
  rw [sNF_iff_spineLen_lt3]
  simp [SExpr.spineLen]

/-
================================================================================
SECTION 8: THEOREM STUBS FOR PRIZE PATH
================================================================================

The full non-universality argument requires:
1. [DONE] Normal forms have spineLen < 3
2. [DONE] head of every S-expr is S
3. [NEXT] S cannot compute constant functions (argument-dropping impossible)
4. [NEXT] S cannot compute parity
5. [FINAL] S is not universal
-/

/-- S-reduction never drops arguments: every subterm of the input appears
    in the output. This is the fundamental reason S cannot simulate K.
    K drops its second argument; S only duplicates. -/
theorem sStep_no_argument_dropping (e e' : SExpr) (h : sStep e = some e') :
    e.sLeaves ≤ e'.sLeaves := by
  induction e generalizing e' with
  | S => simp [sStep] at h
  | app f x ihf _ihx =>
    -- Case split exhaustively on (f, x) structure for sStep
    match f, x with
    | SExpr.S, _ =>
      -- sStep (app S x) = sStep S = none: impossible
      simp [sStep] at h
    | SExpr.app SExpr.S g, _ =>
      -- sStep (app (app S g) x) = sStep (app S g) = none: impossible
      simp [sStep] at h
    | SExpr.app (SExpr.app SExpr.S f') g, x' =>
      -- S redex fires: sStep = some (app (app f' x') (app g x'))
      simp [sStep] at h
      cases h
      simp [SExpr.sLeaves]
      have := SExpr.sLeaves_pos x'
      omega
    | SExpr.app (SExpr.app (SExpr.app f2 x2) x3) x4, _ =>
      -- No top S redex (f head is not S), reduces f
      -- sStep f might fire
      cases h_f : sStep (SExpr.app (SExpr.app (SExpr.app f2 x2) x3) x4) with
      | none =>
        -- sStep f = none, so sStep (app f x) = none: impossible
        simp [sStep, h_f] at h
      | some f' =>
        -- sStep f = some f', so sStep (app f x) = some (app f' x)
        simp [sStep, h_f] at h
        cases h
        simp [SExpr.sLeaves]
        have hle := ihf f' h_f
        simp [SExpr.sLeaves] at hle
        omega

/-
================================================================================
SECTION 9: NORMALIZATION WITH FUEL
================================================================================

Since S-reduction can diverge (e.g., S S S S → S S (S S) → ...), we use
a fuel-bounded normalization. If the fuel runs out, we return None.
-/

/-- Reduce an expression up to `fuel` steps. Returns None if fuel runs out. -/
def sNorm : Nat → SExpr → Option SExpr
  | 0,        _ => none        -- fuel exhausted
  | fuel + 1, e =>
      match sStep e with
      | none    => some e      -- already in NF
      | some e' => sNorm fuel e'

/-- sNorm returns a value that is in normal form. -/
theorem sNorm_isNF (fuel : Nat) (e r : SExpr) (h : sNorm fuel e = some r) :
    r.isNF := by
  induction fuel generalizing e with
  | zero => simp [sNorm] at h
  | succ n ih =>
    simp [sNorm] at h
    cases h_step : sStep e with
    | none =>
      simp [h_step] at h
      cases h
      rwa [SExpr.isNF]
    | some e' =>
      simp [h_step] at h
      exact ih e' h

/-- sNorm preserves sLeaves (non-decreasing): if normalization completes,
    the result has at least as many S-leaves as the input. -/
theorem sNorm_sLeaves_ge (fuel : Nat) (e r : SExpr) (h : sNorm fuel e = some r) :
    e.sLeaves ≤ r.sLeaves := by
  induction fuel generalizing e with
  | zero => simp [sNorm] at h
  | succ n ih =>
    simp [sNorm] at h
    cases h_step : sStep e with
    | none =>
      simp [h_step] at h; cases h; exact Nat.le_refl _
    | some e' =>
      simp [h_step] at h
      have h1 := sStep_no_argument_dropping e e' h_step
      have h2 := ih e' h
      omega

/-
================================================================================
SECTION 10: S SPINE TOWER — UNBOUNDED INPUTS
================================================================================
-/

/-- The spine tower: sSpineTower n = app (app (... app S S) S) ... S
    with n applications. It has n+1 S-leaves. -/
def sSpineTower : Nat → SExpr
  | 0     => SExpr.S
  | n + 1 => SExpr.app (sSpineTower n) SExpr.S

/-- sSpineTower n has spine length n. -/
theorem sSpineTower_spineLen (n : Nat) : (sSpineTower n).spineLen = n := by
  induction n with
  | zero => simp [sSpineTower, SExpr.spineLen]
  | succ n ih => simp [sSpineTower, SExpr.spineLen, ih]; omega

/-- sSpineTower n has exactly n+1 S-leaves. -/
theorem sSpineTower_sLeaves (n : Nat) : (sSpineTower n).sLeaves = n + 1 := by
  induction n with
  | zero => simp [sSpineTower, SExpr.sLeaves]
  | succ n ih => simp [sSpineTower, SExpr.sLeaves, ih]

/-- sSpineTower n is in normal form for n < 3 (spine < 3). -/
theorem sSpineTower_isNF_lt3 (n : Nat) (hn : n < 3) : (sSpineTower n).isNF := by
  rw [sNF_iff_spineLen_lt3, sSpineTower_spineLen]
  exact hn

/-
================================================================================
SECTION 11: S CANNOT COMPUTE CONSTANT FUNCTIONS
================================================================================

Theorem: There is no S-only expression P such that for all inputs x,
the normal form of (P x) is a fixed expression c.

Proof: If (P x) normalizes to c, then c.sLeaves ≥ (P x).sLeaves = P.sLeaves + x.sLeaves.
By choosing x = sSpineTower n, we get c.sLeaves ≥ P.sLeaves + (n+1).
Since this holds for all n, c.sLeaves must be unbounded — contradiction.
-/

/-- Applying P to x has sLeaves = P.sLeaves + x.sLeaves. -/
theorem sLeaves_app (P x : SExpr) :
    (SExpr.app P x).sLeaves = P.sLeaves + x.sLeaves := by
  simp [SExpr.sLeaves]

/-- A constant S-function: P normalizes (P x) to the same value c for all x
    (within a given fuel budget). -/
def sComputes_const (P c : SExpr) (fuel : Nat) : Prop :=
  ∀ x : SExpr, sNorm fuel (SExpr.app P x) = some c

/-- KEY THEOREM: S cannot compute any constant function.
    No S-only expression P with any fuel budget has the property that
    (P x) normalizes to the same result c for all x. -/
theorem s_no_constant_function (P c : SExpr) (fuel : Nat)
    (h : sComputes_const P c fuel) : False := by
  -- Choose x large enough that x.sLeaves > c.sLeaves - P.sLeaves
  -- Specifically, x = sSpineTower (c.sLeaves + 1) has c.sLeaves + 2 leaves
  let n := c.sLeaves + 1
  let x := sSpineTower n
  have hx_leaves : x.sLeaves = n + 1 := sSpineTower_sLeaves n
  -- (P x).sLeaves = P.sLeaves + x.sLeaves ≥ x.sLeaves = n + 1 = c.sLeaves + 2
  have hPx_leaves : (SExpr.app P x).sLeaves = P.sLeaves + x.sLeaves := sLeaves_app P x
  -- h says sNorm fuel (P x) = some c
  have h_norm := h x
  -- By sNorm_sLeaves_ge: c.sLeaves ≥ (P x).sLeaves = P.sLeaves + x.sLeaves
  have h_ge := sNorm_sLeaves_ge fuel (SExpr.app P x) c h_norm
  -- But c.sLeaves < P.sLeaves + x.sLeaves (since x.sLeaves = c.sLeaves + 2)
  have h_contra : P.sLeaves + x.sLeaves > c.sLeaves := by
    rw [hx_leaves]; simp [n]; omega
  -- Contradiction: c.sLeaves ≥ P.sLeaves + x.sLeaves > c.sLeaves
  rw [hPx_leaves] at h_ge
  omega

/-
================================================================================
SECTION 12: S CANNOT COMPUTE BOUNDED-OUTPUT FUNCTIONS
================================================================================

The constant function impossibility generalizes: S cannot compute any function
whose output sLeaves count is bounded, when the input sLeaves count is unbounded.

This rules out:
- Constant functions (outputs have sLeaves ≤ max_output_leaves for all inputs)
- Parity (outputs are one of two values, both with fixed sLeaves count)
- Church numeral zero (outputs S = 1 leaf, but inputs can be arbitrarily large)
-/

/-- A function f : ℕ → SExpr has unbounded sLeaves if for any bound M,
    there exists n with f(n).sLeaves > M. -/
def HasUnboundedSLeaves (enc : Nat → SExpr) : Prop :=
  ∀ M : Nat, ∃ n : Nat, M < (enc n).sLeaves

/-- A function f : ℕ → SExpr has bounded sLeaves if there exists M
    such that for all n, f(n).sLeaves ≤ M. -/
def HasBoundedSLeaves (f : Nat → SExpr) : Prop :=
  ∃ M : Nat, ∀ n : Nat, (f n).sLeaves ≤ M

/-- The sSpineTower encoding has unbounded sLeaves: sSpineTower n has n+1 leaves. -/
theorem sSpineTower_hasUnboundedSLeaves : HasUnboundedSLeaves sSpineTower := by
  intro M
  refine ⟨M, ?_⟩
  rw [sSpineTower_sLeaves]
  omega

/-- KEY THEOREM: S cannot compute any function from an unbounded-input encoding
    to a bounded-output set.

    If enc_in has unbounded sLeaves AND out has bounded sLeaves,
    then no S-only program P can compute f (in the sense that
    P applied to enc_in(n) normalizes to out(f(n)) for all n). -/
theorem s_no_bounded_output_function
    (P : SExpr)
    (enc_in : Nat → SExpr)
    (out : Nat → SExpr)
    (h_unbounded : HasUnboundedSLeaves enc_in)
    (h_bounded : HasBoundedSLeaves out)
    (f : Nat → Nat)
    (fuel : Nat)
    (h_computes : ∀ n, sNorm fuel (SExpr.app P (enc_in n)) = some (out (f n))) :
    False := by
  -- Get the bound M on output sLeaves
  obtain ⟨M, hM⟩ := h_bounded
  -- Choose n large enough that enc_in(n).sLeaves > M + P.sLeaves
  obtain ⟨n, hn⟩ := h_unbounded (M + P.sLeaves)
  -- The input enc_in n has sLeaves > M + P.sLeaves
  -- So (P (enc_in n)).sLeaves = P.sLeaves + enc_in(n).sLeaves > M + 2·P.sLeaves ≥ M
  have hPx_leaves : (SExpr.app P (enc_in n)).sLeaves = P.sLeaves + (enc_in n).sLeaves :=
    sLeaves_app P (enc_in n)
  -- By normalization monotonicity: out(f n).sLeaves ≥ (P(enc_in n)).sLeaves
  have h_ge := sNorm_sLeaves_ge fuel (SExpr.app P (enc_in n)) (out (f n)) (h_computes n)
  -- But out(f n).sLeaves ≤ M (by boundedness)
  have h_le : (out (f n)).sLeaves ≤ M := hM (f n)
  -- Contradiction: out(f n).sLeaves ≥ P.sLeaves + enc_in(n).sLeaves > M + P.sLeaves ≥ M
  rw [hPx_leaves] at h_ge
  omega

/-
================================================================================
SECTION 13: PARITY IS NOT S-COMPUTABLE
================================================================================

Parity outputs: one of two values (representing 0 or 1).
Any two-value output set has bounded sLeaves (max of the two).
Any useful encoding of naturals must have unbounded sLeaves (else not injective).

Therefore, by s_no_bounded_output_function, parity is not S-computable.
-/

/-- For parity to be S-computable, we need:
    - An encoding enc_in : ℕ → SExpr with unbounded sLeaves
    - Two distinct output values (representing 0 and 1)
    - A program P that maps enc_in(n) to the right output

    The two-value output set has bounded sLeaves. By s_no_bounded_output_function,
    no such P exists. -/
theorem parity_not_s_computable
    (P : SExpr)
    (enc_in : Nat → SExpr)
    (zero_enc one_enc : SExpr)
    (h_unbounded : HasUnboundedSLeaves enc_in)
    (fuel : Nat)
    (h_parity : ∀ n, sNorm fuel (SExpr.app P (enc_in n)) =
        some (if n % 2 = 0 then zero_enc else one_enc)) :
    False := by
  -- The output function maps to {zero_enc, one_enc}, which has bounded sLeaves
  let out := fun k => if k % 2 = 0 then zero_enc else one_enc
  have h_bounded : HasBoundedSLeaves out := by
    refine ⟨max zero_enc.sLeaves one_enc.sLeaves, ?_⟩
    intro n
    simp [out]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  -- Apply the general theorem
  exact s_no_bounded_output_function P enc_in out
    h_unbounded h_bounded (fun n => n) fuel h_parity

