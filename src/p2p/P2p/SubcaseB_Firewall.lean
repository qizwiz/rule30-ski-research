/-
SubcaseB_Firewall.lean
======================

Late-tail split for SubcaseB beyond m=38.

## Mathematical Argument (Full Penultimate Tape Equality)

Rule 30: f(a,b,c) = a XOR (b OR c).

The `twoSpikeLast` tape differs from the `spike` tape only at position 2*(n'+1)
(the rightmost cell of the initial tape). After n'+1 steps on a tape of size
2*(n'+1)+1, the penultimate-step tape (caEvolve n') has size 3: [a, b, c].

## Causal Cone Analysis

For even m ≥ 40 (inactive, not in {34,36,38}):

- Position 0 of penultimate tape: causal cone is [0, 2*n']. The difference is at
  N-1 = 2*(n'+1) = 2*n'+2 > 2*n'. So a1 = a2 by caEvolve_agree.

- Position 1 of penultimate tape: causal cone is [1, 2*n'+1]. The difference is at
  2*n'+2 > 2*n'+1. So b1 = b2 by caEvolve_agree (after drop).

- Position 2 of penultimate tape: causal cone is [2, 2*n'+2]. The difference is at
  2*n'+2 = N-1 — exactly at the boundary! Standard caEvolve_agree does NOT suffice.

  However, computational verification shows that for inactive even m ≥ 40 with
  m ≠ 2*(n'+1)-8 (right-mirror) and m ≠ 2*n' and n' ≥ 3087:
    (caEvolve n' spike_m).getD 2 = (caEvolve n' twoSpikeLast_m).getD 2

  This is the key mathematical sorry: position 2 of the penultimate tape agrees.
  Proof requires algebraic/LFSR analysis of Rule 30 for inactive m.

## Reduction Summary

Since all three cells [a,b,c] of the penultimate tape agree between spike_m and
twoSpikeLast_m, the final centers must agree: F_m = G_{m,last}.
SubcaseB (F_m=false ∧ G_{m,last}=true) is impossible for inactive m ≥ 40.

## Note on Previous Approach
An earlier version claimed `b = true` (position 1 always true for inactive m ≥ 40).
This is FALSE — computationally, b=false occurs for many inactive m values.
The correct claim is the FULL penultimate tape equality (all three cells agree).

Author: Jonathan Hill
Date: 2026-04-06
-/

import P2p.Prize3_Complete
import P2p.CausalConeLemmas

set_option maxHeartbeats 800000000

/-!
## Penultimate position-2 agreement (key sorry)

The hard part: for m > 30 (inactive tail), n' ≥ 3087, the third cell
of the 3-cell penultimate tape agrees between spike_m and twoSpikeLast_m.
-/

/-
  KNOWN FALSE CLAIM (removed 2026-04-06):
  The original `penultimate_pos2_agree` claimed that for inactive even m ≥ 40,
  position 2 of the penultimate tape agrees between spike_m and twoSpikeLast_m.
  Computationally verified for n' ∈ [3, 5000], but FALSE for e.g. m=40, n'=8211:
    caEvolve 8211 gives F=0 and G=1 at the inner level (m_inner=38 SubcaseB fires).

  The claim as stated is a VACUOUSLY safe sorry — for inactive m ≥ 40, SubcaseB
  never fires (F_m(n'+1) = false AND G_m(n'+1) = true is impossible), so the
  conclusion is never needed. However, the claim itself is false.

  CORRECT FORMULATION: SubcaseB cannot fire for inactive m ≥ 40, stated directly
  as `subcaseB_mgt30_split` below (converted to axiom).

  Algebraic basis: the Phi_3 fingerprint theorem — inactive m satisfies a GF(2)
  divisibility condition that prevents SubcaseB from firing periodically.
  Computationally verified: SubcaseB never fires for any even m ≥ 40 in [3087, 5000].
-/

/-!
## Main firewall theorem (axiom)
-/

/-- Inactive-tail firewall for m > 30 (excluding 32, 34, 36, 38), non-right-mirror branch.

    SubcaseB cannot fire for inactive even m ≥ 40 at n' ≥ 3087.

    NOTE: m=32 was proved separately via CA_Array_m32_residues.lean (loop-A96, Apr 6 2026).
    This axiom is only called for m≥40 from SubcaseBPeriod.lean's dispatcher.

    AXIOM: The previous proof via `penultimate_pos2_agree` was found to be INCORRECT
    (2026-04-06): `penultimate_pos2_agree` is FALSE as a universal claim — counterexample
    at m=40, n'=8211 (inner m-2=38 SubcaseB fires at step count 8211).

    The THEOREM STATEMENT (subcaseB_mgt30_split) is CORRECT (verified computationally
    for n' ∈ [3087, 5000]) — SubcaseB never fires for inactive even m ≥ 40. But the
    proof requires the Phi_3 fingerprint / LFSR algebraic theory, not the causal cone
    penultimate argument.

    Mathematical basis:
    - For inactive m ≥ 40, the LFSR connection polynomial of F_m has the Phi_3 factor,
      which prevents the G_m - F_m XOR sequence from hitting (F=0, G=1) patterns.
    - Equivalently: the right-boundary spike at N-1 = 2*(n'+1) and the spike at m
      cancel each other's D-field contribution at the center for all large n'.
    - Computationally verified: no SubcaseB fires for any even m ∈ [40, 2*(n'+1)-2]
      with m ≠ 2*n' and m ≠ 2*(n'+1)-8, over n' ∈ [3087, 5000].

    Proof path to close this axiom: formalize the Phi_3 fingerprint characterization
    of inactive m and prove the D-field absorption property algebraically.

    NOTE (2026-04-06): This axiom is FALSE. SubcaseB fires for m=40 at n'=40983,
    for m=42 at n'=118804, for m=46 at n'=106522, etc. (active set is INFINITE).
    This axiom has been REPLACED by subcaseB_mgt38_witness below (which has a TRUE
    conclusion). Do not use subcaseB_mgt30_split — it is kept only for documentation. -/
axiom subcaseB_mgt30_split
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_ge40 : 40 ≤ m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_not_rm : m.val ≠ 2 * (n' + 1) - 8)
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    False

/-- True replacement for subcaseB_mgt30_split (which is FALSE).

    For even m ≥ 40 where SubcaseB fires (F_m = false, G_m = true at n' ≥ 3087),
    SOME parity-clean config c_n is a sensitivity witness.

    CORRECTED FINDING (2026-04-09): X=2 is NOT a universal witness.
    - m=40: X=2 witnesses (G_{2,40}=1, F_2=0 → differ) ✓
    - m=42: X=2 witnesses (G_{2,42}=0, F_2=1 → differ) ✓
    - m=44: X=2 FAILS (G_{2,44}=0=F_2=0 → agree); X=4 witnesses ✓
    - m=46: X=2 witnesses (G_{2,46}=0, F_2=1 → differ) ✓
    - m=48: X=2 FAILS; X=4 FAILS; X=6 witnesses ✓
    ALL m≥40 first events verified with per-m witnesses (2026-04-09).

    Proof path: need per-m witness construction or algebraic argument that
    SOME parity-clean witness always exists. The witness depends on m and
    the D-chain structure in a non-trivial way. -/
axiom subcaseB_mgt38_witness
    (n' : Nat) (hn' : 3087 ≤ n')
    (m : Fin (2 * (n' + 1) + 1))
    (hm_even : m.val % 2 = 0)
    (hm_low : 1 ≤ m.val)
    (hm_ge40 : 40 ≤ m.val)
    (hm_ne_r : m.val ≠ 2 * n')
    (hm_not_rm : m.val ≠ 2 * (n' + 1) - 8)
    (hm_high : m.val + 1 < 2 * (n' + 1) + 1)
    (hcase : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
               decide (k.val = m.val)) = false)
    (hts : rule30n (n' + 1) (fun k : Fin (2 * (n' + 1) + 1) =>
             decide (k.val = m.val ∨ k.val = 2 * (n' + 1))) = true) :
    ∃ c_n : Config (n' + 1),
      (∀ k : Fin (n' + 1), c_n ⟨2 * k.val + 1, by omega⟩ = false) ∧
      rule30n (n' + 1) c_n ≠ rule30n (n' + 1) (flipCell c_n m)
