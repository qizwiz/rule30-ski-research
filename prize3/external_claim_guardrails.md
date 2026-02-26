# Prize3 External Claim Guardrails (M4)

Date: 2026-02-26

Purpose: enforce conservative external wording while O2-O5 remain open.

## Required Status Line (verbatim)
"Prize3 lower-bound theorem is not yet proved in-repo."

## Claim Split (must appear explicitly)
- Proved (in-repo artifacts only)
- Empirical (repro/debug outputs only, not proof)
- Conjectural / pending (open bridge obligations)

## Allowed External Statements (Current)
| Statement pattern | Class | Evidence |
|---|---|---|
| "We formalized foundational cone-width and bridge-support lemmas in Lean." | Proved | `prize3/lean/Prize3Model.lean` |
| "Exactness implies observation of required indices under explicit witness hypotheses." | Proved (conditional) | `must_observe_required`, `observes_required_of_exact` |
| "Under the same explicit hypotheses, unobserved implies not-required." | Proved (conditional) | `not_observes_implies_not_required_of_exact`, `not_observes_next_gen_implies_not_required_next_gen_of_exact` |
| "Runtime checks are reproducible in-repo." | Empirical | `logs/repro/` |
| "Rule 30 witness/accounting instantiation remains open work." | Conjectural / pending | `prize3/phase3_obligation_matrix.md` |

## Disallowed Statements (Until O2-O5 Close)
| Statement pattern | Why disallowed now |
|---|---|
| "Rule 30 lower-bound theorem is proved." | O2-O5 remain open in `prize3/phase3_obligation_matrix.md`. |
| "No-skip is fully proved for concrete Rule 30." | Only abstract/conditional bridge currently proved. |
| "Empirical runs validate the theorem." | Empirical outputs are not accepted as proof steps. |

## Gate Rule
- If a draft contains any disallowed statement, block external release until wording is corrected and re-checked against `prize3/m4_submission_gate.md`.
