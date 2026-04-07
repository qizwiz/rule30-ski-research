/-
SubcaseB_RightOffset8.lean
==========================

Narrow right-boundary lemmas for the defect-state machine.

Discovery (2026-04-04, defect_state_machine_notes.md, right_offset8_notes.md):
  In active windows (n',m) ∈ {(4112,34), (4113,36), (8210,38)}:
  - Right offsets 2,4,6,10,12,14,16 annihilate the defect ray (→ Dead)
  - In a wider scan through offsets 2..128, offset 8 is the UNIQUE survivor
  - Offset 8 produces a truncated ray matching a nearby inactive base case
    in the tested local near-center window (last 400 rows, width 241)

This file states two narrow lemmas:
  (A) rightBoundary_kill_conjectural: common annihilator offsets kill the
      center perturbation (F_m = G_{m, right-offset-k})
  (B) rightOffset8_reduction_conjectural: offset 8 reduces the active
      center output to the inactive-base center output

Both are CONJECTURAL: empirically observed but not yet structurally proved.
The statements use current defect-state language honestly.

Author: Jonathan Hill
Date: 2026-04-04
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas

set_option maxHeartbeats 800000000

/-!
## Right-boundary perturbation config

For an active SubcaseB position m at tape step T = n'+1, the right-boundary
perturbation at offset k adds a spike at position 2*T - k (near the right edge).

This is the three-spike config: spike at m, spike at 2*T (the twoSpikeLast
right-edge spike), AND an auxiliary spike at 2*T - k.

The defect-state evidence compares:
  - active:   spike(m) + right-edge(2T)  → center output
  - perturbed: spike(m) + right-edge(2T) + aux(2T-k) → center output

When these agree, the auxiliary spike annihilates the defect channel.
-/

/-- Three-spike config: spikes at m, 2T (right edge), and 2T-k (right-offset-k aux). -/
def rightBoundaryThreeSpikeList (m k T : ℕ) : List Bool :=
  List.ofFn fun i : Fin (2 * T + 1) =>
    decide (i.val = m ∨ i.val = 2 * T ∨ i.val = 2 * T - k)

/-- Center output of the active two-spike config (spike at m + right edge). -/
def rightBoundaryActiveCenter (m T : ℕ) : Bool :=
  (caEvolve T (twoSpikeList m (2 * T) (2 * T + 1))).getD 0 false

/-- Center output of the perturbed three-spike config (with right-offset-k aux). -/
def rightBoundaryPerturbedCenter (m k T : ℕ) : Bool :=
  (caEvolve T (rightBoundaryThreeSpikeList m k T)).getD 0 false

/-!
## Lemma (A): Annihilator offsets kill the defect channel

For common right offsets k ∈ {2,4,6,10,12,14,16}, the auxiliary spike
annihilates the defect ray, so the perturbed center equals the active center.

This is empirically observed in the tested active windows but NOT yet
structurally proved. The structural mechanism is the OR-firewall: the
auxiliary spike's cone intersects the defect channel's path to the center
at a position where the OR gate absorbs the perturbation.

Claim class: CONJECTURAL (empirical, not proved).
-/

/-- Right-boundary annihilation for common kill offsets.

    For active SubcaseB positions m ∈ {34, 36, 38} at tape step T ≥ 3087,
    and right offset k ∈ {2, 4, 6, 10, 12, 14, 16}, the perturbed center
    output equals the active center output.

    Empirical basis: defect_state_machine_notes.md — tested in windows
    (4112,34), (4113,36), (8210,38) with all listed offsets producing Dead.

    SORRY: Not yet structurally proved. The OR-firewall argument from
    SubcaseB_Firewall.lean should extend to this case, but the three-spike
    interaction needs careful causal-cone analysis. -/
theorem rightBoundary_kill_conjectural
    (m k T : ℕ)
    (hm : m = 34 ∨ m = 36 ∨ m = 38)
    (hk : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 10 ∨ k = 12 ∨ k = 14 ∨ k = 16)
    (hT : 3087 ≤ T)
    (hbounds : m + 1 < 2 * T + 1) (hkb : k < 2 * T) (hmk : m ≠ 2 * T - k) :
    rightBoundaryPerturbedCenter m k T = rightBoundaryActiveCenter m T := by
  -- CONJECTURAL: empirically observed, not structurally proved.
  -- The OR-firewall argument should apply: the aux spike at 2T-k creates
  -- a cone that intersects the defect channel's path, and the OR gate
  -- absorbs the perturbation. But the three-spike causal-cone geometry
  -- needs careful analysis.
  sorry

/-!
## Lemma (B): Right offset 8 reduction

Offset 8 is the UNIQUE surviving right toggle in the tested band 2..128.
It does NOT annihilate the defect channel. Instead, it reduces the active
center output to match a nearby inactive-base center output.

Specifically, in the tested windows:
  - (4112,34)+right8 matches base m=30 in the local near-center movie
  - (4113,36)+right8 matches base m=30 and m=32
  - (8210,38)+right8 matches base m=32 and m=34

This suggests offset 8 converts the active full-ray into a truncated-ray
state equivalent to an inactive base case.

Claim class: CONJECTURAL (empirical, not proved).
-/

/-- Center output of an inactive base case (spike at m_base only, no right-edge spike). -/
def rightBoundaryInactiveCenter (m_base T : ℕ) : Bool :=
  (caEvolve T (spikeAtList m_base (2 * T + 1))).getD 0 false

/-- Right-offset-8 reduction lemma.

    For active SubcaseB positions m ∈ {34, 36, 38} at tape step T ≥ 3087,
    the perturbed center with right-offset-8 equals the inactive base center
    for some nearby m_base ∈ {30, 32}.

    Empirical basis: right_offset8_notes.md — in the tested local near-center
    windows (last 400 rows, width 241), the defect movies match exactly:
      - (4112,34)+right8 ↔ m_base=30
      - (4113,36)+right8 ↔ m_base=30,32
      - (8210,38)+right8 ↔ m_base=32,34

    This is the unique surviving right offset in the band 2..128.
    All other right offsets annihilate (→ Dead).

    SORRY: Not yet structurally proved. The reduction mechanism is not yet
    understood — offset 8 may correspond to a fixed local rewrite on the
    incoming defect ray, but this needs causal-cone analysis.

    NOTE: This lemma is stated for center-output equality only. The empirical
    evidence is stronger (full local movie equivalence), but center-output
    equality is the minimal formal claim needed for SubcaseB routing. -/
theorem rightOffset8_reduction_conjectural
    (m T : ℕ)
    (hm : m = 34 ∨ m = 36 ∨ m = 38)
    (hT : 3087 ≤ T)
    (hbounds : m + 1 < 2 * T + 1) (hmk : m ≠ 2 * T - 8) :
    ∃ m_base : ℕ,
      (m_base = 30 ∨ m_base = 32) ∧
      rightBoundaryPerturbedCenter m 8 T = rightBoundaryInactiveCenter m_base T := by
  -- CONJECTURAL: empirically observed in local movie windows, not structurally proved.
  -- The existence of m_base is supported by defect-state evidence but needs
  -- a structural argument about why offset 8 produces a truncated ray equivalent
  -- to an inactive base case.
  sorry

/-!
## Narrowest next lemma: offset-8 center equality for a concrete instance

If the general reduction is too broad, here is a concrete native_decide-checkable
instance that could serve as a base certificate for a future period argument.

This is a single-point verification: T = 4112, m = 34, k = 8.
-/

/-- Concrete base certificate: right-offset-8 reduction at (T=4112, m=34).

    BLOCKED (2026-04-04): native_decide evaluated this claim and found it FALSE.

    The empirical evidence in right_offset8_notes.md reports that the perturbed
    defect movie with right-offset-8 matches the inactive base movie for m_base=30
    in a local near-center window (last 400 rows, width 241). However, this lemma
    claims equality of the center output cell at position 0 after 4112 full steps,
    which is a global claim not guaranteed by local movie equivalence.

    The native_decide failure shows that at the full-tape level, the perturbed
    center with right-offset-8 does NOT equal the inactive base center for
    m_base=30 at T=4112.

    This does NOT refute the local movie equivalence observed empirically.
    It only refutes the stronger claim that the final center bits are equal.

    Narrowest next step:
    (a) Check whether the perturbed center equals the inactive center for a
        DIFFERENT m_base value (e.g., 32) — the notes say (4113,36)+right8
        matches both m_base=30 and m_base=32, so perhaps m=34 maps to 32.
    (b) Reformulate the certificate as a local-window equivalence lemma
        (comparing sub-windows of the evolved tapes) rather than a single
        center-output equality.
    (c) Investigate whether the center outputs differ by a known small offset
        in the tape position, suggesting an alignment issue. -/
lemma rightOffset8_cert_T4112_m34 :
    rightBoundaryPerturbedCenter 34 8 4112 = rightBoundaryInactiveCenter 30 4112 := by
  -- BLOCKED: native_decide found this proposition is FALSE.
  -- See doc-string above for analysis and next steps.
  sorry

/-- Alternative concrete certificate: right-offset-8 reduction at (T=4112, m=34)
    mapped to m_base = 32 instead of 30.

    PROVED (2026-04-04): native_decide confirms this equality.

    Cross-check (research/right8_center_check.py):
      rightBoundaryPerturbedCenter 34 8 4112 = True
      rightBoundaryInactiveCenter 32 4112 = True
      rightBoundaryInactiveCenter 30 4112 = False  (original claim was false)

    Notably, rightBoundaryPerturbedCenter 34 8 4112 = rightBoundaryActiveCenter 34 4112,
    meaning right-offset-8 does NOT change the center output for this instance.
    The "truncated ray" observed in local movies does not affect the center bit. -/
lemma rightOffset8_cert_T4112_m34_alt :
    rightBoundaryPerturbedCenter 34 8 4112 = rightBoundaryInactiveCenter 32 4112 := by
  native_decide

/-- Right-offset-8 is a no-op on the center bit at (T=4112, m=34).

    PROVED (2026-04-04): native_decide confirms the perturbed center equals
    the active center. The auxiliary spike at offset 8 does not change the
    center output, even though it produces a visually different defect movie
    (truncated ray vs full ray) in the local near-center window.

    This is the narrowest checkable certificate for the right-offset-8 anomaly.
    It shows that offset 8, while producing a different defect pattern, does
    not affect the SubcaseB routing decision for this concrete instance. -/
lemma rightOffset8_noop_T4112_m34 :
    rightBoundaryPerturbedCenter 34 8 4112 = rightBoundaryActiveCenter 34 4112 := by
  native_decide
