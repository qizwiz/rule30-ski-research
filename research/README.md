# Research Bundle

This folder is a single index for the Rule 30 / SKI / basin work.

Canonical paper:
- `papers/rule30_rheology.canonical.tex`
- `papers/rule30_rheology.canonical.pdf`

Lean proofs:
- `lean_proofs/InterBasin.lean`
- `lean_proofs/Rule30Stability.lean` (draft)

Core scripts:
- `ski_ca_analyzer.py` (SKI compiler + reduction + truth table)
- `ski_rule30_center.py` (global CA center cell builder)
- `ski_graph_engine.py` (hash-consed graph reducer)
- `extract_basins.py` (basin skeleton extraction)
- `rule30_matrix.py` (rule 30 data matrix)
- `analyze_growth.py` (growth analysis)
- `true_irreducibility_test.py` (irreducibility test harness)

Key datasets:
- `rule30_matrix.csv`
- `growth_data.csv`
- `growth_data_cpp.csv`
- `python_growth_data.csv`

Sync paper copies:
- `scripts/sync_papers.sh`

Suggested quick checks:
- `python3 ski_ca_analyzer.py`
- `python3 ski_rule30_center.py --gen 5`
- `python3 extract_basins.py`

Related archive (~/src index + legacy docs):
- `research/related/index.md`
- `research/related/mindmap.md`
- `research/related/recency_top100.md`
- `research/related/top25.md`
- `research/related/graph.md`
- `research/related/canon.md`
- `research/related/portfolio_index.md`
- `research/related/legacy/`
  - `research/related/legacy/summary.md`

Funding kit:
- `research/funding/overview.md`
- `research/funding/outreach_email.md`
- `research/funding/pitch.md`
