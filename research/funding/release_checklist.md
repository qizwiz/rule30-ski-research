# Public Release Checklist

This checklist is optimized for speed-to-credibility and funding conversations.

## 1. Freeze Core Artifacts
- Confirm canonical paper files are current:
  - `papers/rule30_rheology.canonical.tex`
  - `papers/rule30_rheology.canonical.pdf`
- Confirm synced copies are updated via:
  - `scripts/sync_papers.sh`
- Confirm Lean theorem compiles:
  - `lean lean_proofs/InterBasin.lean`

## 2. Reproducibility Pass
- Run core scripts and keep outputs in-repo:
  - `python3 ski_ca_analyzer.py`
  - `python3 ski_rule30_center.py --gen 5`
  - `python3 extract_basins.py`
  - `python3 analyze_growth.py`
- Verify key data files exist and are current:
  - `rule30_matrix.csv`
  - `growth_data.csv`
  - `growth_data_cpp.csv`
  - `python_growth_data.csv`

## 3. Claim Hygiene
- In the paper and one-pagers, separate:
  - Proven (Lean theorem)
  - Empirical (script outputs)
  - Conjectural (future work)
- Remove or reword any claim that implies solved irreducibility.

## 4. Package for Reviewers
- Ensure these docs are present and linked from `research/README.md`:
  - `research/funding/overview.md`
  - `research/funding/pitch.md`
  - `research/funding/research_statement.md`
  - `research/related/portfolio_index.md`
- Keep one canonical artifact index:
  - `research/related/canon.md`

## 5. Publish Sequence
1. Publish preprint package (`rule30_rheology` + Lean + scripts).
2. Publish portfolio index and reproducibility docs.
3. Send targeted outreach emails with one-pager + links.

## 6. Outreach Readiness
- Contact card in every outreach asset:
  - Jonathan Hill
  - `jonathan.f.hill@gmail.com`
  - `@_qizwiz` (`qizwiz`)
- Keep a short FAQ ready:
  - What is proved?
  - What is measured?
  - What is next and fundable in 6-12 months?
