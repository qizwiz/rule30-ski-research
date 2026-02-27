# Prize3 External Snippet (Claim-Hygienic)

Date: 2026-02-26

Use this text in outreach/funding materials when Prize3 status must be stated conservatively.

## Required Status Line (verbatim)
"Prize3 lower-bound theorem is not yet proved in-repo."

## Short Copy-Safe Blurb
Prize3 work has formalized foundational artifacts in Lean, including the model/statement freeze, dependency-cone support lemmas, and conditional bridge/cost-transfer scaffolds under explicit hypotheses. Reproducibility checks are in-repo and treated as empirical validation only. Rule 30-specific witness construction and concrete accounting instantiation remain open, so no final theorem claim is made yet.

## Mandatory Split Labels (must appear explicitly)
- Proved:
  - Artifact-level Lean foundations and conditional scaffold lemmas in `prize3/lean/Prize3Model.lean`.
- Empirical (not proof):
  - Repro/runtime logs in `logs/repro/`.
- Conjectural / pending:
  - Rule 30 witness/accounting instantiation needed to close `Work_A(n) = Omega(n)`.

## Reference Gate
- Validate final wording against:
  - `prize3/m4_submission_gate.md`
  - `prize3/submission_packet.md`
  - `prize3/external_claim_guardrails.md`
