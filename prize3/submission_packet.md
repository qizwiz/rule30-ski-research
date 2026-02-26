# Prize3 Submission Packet (M4, Claim-Hygienic)

Date: 2026-02-26

Purpose: provide a single pre-submission checklist and evidence map without overstating theorem status.

## Required External Status Line
"Prize3 lower-bound theorem is not yet proved in-repo."

## Claim Classes (must stay separated)
- Proved (in-repo):
  - Model and statement freeze: `prize3/model.md`, `prize3/statement.md`
  - Lean foundation + bridge scaffold + conditional cost transfer: `prize3/lean/Prize3Model.lean`
  - Obligation tracking: `prize3/phase3_obligation_matrix.md`
- Empirical (not proof):
  - Repro checks/logs only: `logs/repro/`
- Conjectural / pending:
  - Rule 30 witness instantiation and accounting closure for final `Work_A(n) = Omega(n)` claim.

## Evidence Map
| External sentence type | Allowed now | Evidence |
|---|---|---|
| "Foundational lower-bound artifacts are formalized in Lean." | Yes | `prize3/lean/Prize3Model.lean` |
| "Exactness-to-work bridge is partially formalized under explicit hypotheses." | Yes | `must_observe_required`, conditional cost-transfer lemmas |
| "Rule 30 lower-bound theorem is proved." | No | Blocked by O2-O4 in `prize3/phase3_obligation_matrix.md` |
| "Empirical runs support reproducibility." | Yes | `logs/repro/*.md` |

## Pre-Submission Gate
- [ ] O2 closed: Rule 30 witness discharges `h_witness`.
- [ ] O3 closed: no-skip instantiated for concrete Rule 30 target.
- [ ] O4 closed: accounting transfer instantiated without hidden assumptions.
- [ ] O5 closed: final asymptotic theorem composed in Lean-compatible form.
- [ ] Independent review note logged with explicit objections/dispositions.

## Current Status
- Gate: not claim-ready.
- Highest-value unblocked work: continue witness/accounting instantiation support lemmas and proof decomposition artifacts.
