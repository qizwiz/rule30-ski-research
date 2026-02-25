#!/usr/bin/env bash
set -euo pipefail

root_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cp "$root_dir/papers/rule30_rheology.canonical.tex" "$root_dir/arxiv_submission/rule30_rheology.tex"
cp "$root_dir/papers/rule30_rheology.canonical.pdf" "$root_dir/arxiv_submission/rule30_rheology.pdf"
cp "$root_dir/papers/rule30_rheology.canonical.tex" "$root_dir/rule30-ski-topology/rule30_rheology.tex"
cp "$root_dir/papers/rule30_rheology.canonical.pdf" "$root_dir/rule30-ski-topology/rule30_rheology.pdf"

echo "Synced canonical paper to arxiv_submission/ and rule30-ski-topology/"
