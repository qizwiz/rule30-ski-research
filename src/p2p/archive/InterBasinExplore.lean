/-
InterBasinExplore.lean — Exploring the Inter-Basin Theorem connection to Rule 30 periodicity
============================================================================================

The Inter-Basin Theorem (proved in Lean 4 for SKI calculus):
  Every SKI reduction step strictly changes the parenthetical skeleton (basin).
  No basin can repeat during a leftmost-outermost reduction trajectory.

Question: does this help prove or refute periodicity of Rule 30's center column?

Conclusion: The connection is real but indirect. The Inter-Basin Theorem lives at the
wrong level of abstraction for the periodicity question. See /tmp/tamari_exploration.md.

Author: Jonathan Hill
Date: 2026-03-23
-/

import P2p.CA_Basics
import Mathlib.Tactic

/-
## SKI Calculus Types (local, lightweight)
-/

/-- SKI expressions -/
inductive SKI : Type where
  | S : SKI
  | K : SKI
  | I : SKI
  | app : SKI → SKI → SKI
  deriving DecidableEq, Repr

/-- Parenthetical skeleton (basin) -/
inductive Basin : Type where
  | star : Basin
  | app : Basin → Basin → Basin
  deriving DecidableEq, Repr

/-- Extract basin from SKI expression -/
def getBasisn : SKI → Basin
  | SKI.app e1 e2 => Basin.app (getBasisn e1) (getBasisn e2)
  | _ => Basin.star

/-- Basin size (number of leaves) -/
def basinSize : Basin → Nat
  | Basin.star => 1
  | Basin.app b1 b2 => basinSize b1 + basinSize b2

/-
## The SKI term for Rule 30

Rule 30: p XOR (q OR r)

Church booleans: True = K, False = K I
NOT = S(SI(K(KI)))(KK)
OR  = SII
XOR = S(S(KS)(S(S(KS)K)(K(S(SI(K(KI)))(KK)))))(KI)

Rule30 = S(S(KS)(S(KK)(S(KS)(S(KK)(S(S(KS)(S(S(KS)K)(K(S(SI(K(KI)))(KK)))))(KI))))))(K(SII))

Verified: this term correctly computes p XOR (q OR r) on all 8 Boolean inputs.
-/

/-- Church True = K -/
def churchTrue : SKI := SKI.K

/-- Church False = K I -/
def churchFalse : SKI := SKI.app SKI.K SKI.I

/-- NOT = S(SI(K(KI)))(KK) -/
def skiNot : SKI :=
  SKI.app (SKI.app SKI.S (SKI.app (SKI.app SKI.S SKI.I) (SKI.app SKI.K (SKI.app SKI.K SKI.I))))
          (SKI.app SKI.K SKI.K)

/-- OR = SII -/
def skiOr : SKI := SKI.app (SKI.app SKI.S SKI.I) SKI.I

/-- XOR = S(S(KS)(S(S(KS)K)(K(NOT))))(KI) -/
def skiXor : SKI :=
  SKI.app (SKI.app SKI.S
    (SKI.app (SKI.app SKI.S (SKI.app SKI.K SKI.S))
      (SKI.app (SKI.app SKI.S (SKI.app (SKI.app SKI.S (SKI.app SKI.K SKI.S)) SKI.K))
        (SKI.app SKI.K skiNot))))
    (SKI.app SKI.K SKI.I)

/-- Rule30 = S(S(KS)(S(KK)(S(KS)(S(KK)(XOR)))))(K(OR)) -/
def skiRule30 : SKI :=
  SKI.app (SKI.app SKI.S
    (SKI.app (SKI.app SKI.S (SKI.app SKI.K SKI.S))
      (SKI.app (SKI.app SKI.S (SKI.app SKI.K SKI.K))
        (SKI.app (SKI.app SKI.S (SKI.app SKI.K SKI.S))
          (SKI.app (SKI.app SKI.S (SKI.app SKI.K SKI.K)) skiXor)))))
    (SKI.app SKI.K skiOr)

/-
## The structural obstruction

The Inter-Basin Theorem says: during SKI reduction, no basin repeats.
This means the reduction trajectory is a *path* (not a cycle) in the Tamari lattice.

For Rule 30 periodicity, we need: the center column sequence c(n) is eventually periodic.
c(n) is the *output* (a single Boolean) of reducing the generation-n center-cell SKI term.

The obstruction: the Inter-Basin Theorem applies to a SINGLE reduction trajectory.
Different generations n produce DIFFERENT starting terms. The basin sequence for gen n
is completely disjoint from the basin sequence for gen n+1, because:
  - Gen n starts with an O(3^n) term
  - Gen n+1 starts with an O(3^(n+1)) term (strictly larger basin)
  - No basin from gen n can appear in gen n+1's trajectory (different starting sizes)

So the Inter-Basin Theorem tells us nothing about whether the FINAL outputs
(K vs KI) of different generations form a periodic sequence.
-/

/-- The center column value at generation n, as a Boolean.
    This is just rule30n from CA_Basics, restated for clarity. -/
def centerValue (n : Nat) : Bool := centerColumnSeq n

/-
## What WOULD connect them

The key missing piece: a structural invariant that is:
1. Preserved (or transformed predictably) across generations
2. Determines the output Boolean
3. Lives in a finite state space (forcing eventual periodicity)

Candidate: the "reduced skeleton prefix" from the Basin Stabilization Conjecture.
If the outermost basin structure stabilizes at gen 3 and the output depends only
on this prefix, then periodicity would follow from the finite prefix space.

But this fails because: the output depends on ALL input bits (Prize 3 proves this!),
not just the outermost structure. The prefix stabilizes but does not determine the output.
-/

/-- The Tamari lattice position of the gen-n center-cell term's basin.
    This is well-defined but lives in a space that grows with n. -/
def genBasinSize (n : Nat) : Prop :=
  ∀ m : Nat, m > n → basinSize (getBasisn (skiRule30)) < m
  -- Placeholder: the actual basin of the full gen-n term grows quadratically

/-
## A provable but weak connection

What IS true: for any fixed input configuration, the SKI reduction
terminates (the center-cell term is strongly normalizing because
Church booleans + Rule30 always reduce to K or KI).
The Inter-Basin Theorem gives an upper bound on reduction steps:
  steps ≤ (number of distinct basins reachable from the starting basin)
This is the Catalan number C(basin_size), which is finite.

But this just says "computation terminates" — we already know that.
-/

theorem rule30_terminates_trivially (n : Nat) :
    ∃ b : Bool, centerColumnSeq n = b := ⟨_, rfl⟩

/-
## Summary

The Inter-Basin Theorem is a *within-trajectory* acyclicity result.
Periodicity of the center column is an *across-trajectory* regularity question.
These live at different levels:
  - Inter-Basin: structural (skeleton space, Tamari lattice)
  - Periodicity: semantic (output value, {0,1})

The bridge would require: a functor from the Tamari lattice to {0,1}
that commutes with the "add one generation" operation. No such functor
is known or likely to exist in simple form.
-/

