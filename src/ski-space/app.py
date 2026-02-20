"""
SKI Soup — Hugging Face Space
Launches the meta-soup GA as a background subprocess.
Serves live telemetry via Gradio.
"""

import os
import subprocess
import threading
import time
import json
from pathlib import Path
import gradio as gr
import pandas as pd
from ski_parse import parse_log

STATE_DIR   = Path(os.environ.get("STATE_DIR", "/data/ski-meta"))
META_LOG    = STATE_DIR / "soup.log"
STATE_FILE  = STATE_DIR / "state.json"
GA_PID_FILE = STATE_DIR / "ga.pid"

STATE_DIR.mkdir(parents=True, exist_ok=True)
META_LOG.touch(exist_ok=True)

# ── Launch GA subprocess once ──────────────────────────────────────────────

_ga_proc = None

def _start_ga():
    global _ga_proc
    if GA_PID_FILE.exists():
        old_pid = int(GA_PID_FILE.read_text().strip())
        try:
            os.kill(old_pid, 0)
            print(f"[app] GA already running at PID {old_pid}")
            return
        except ProcessLookupError:
            pass

    log_fh = open(META_LOG, "a")
    _ga_proc = subprocess.Popen(
        ["python3", "ski-meta-soup.py", "--run"],
        stdout=log_fh, stderr=log_fh,
        cwd="/app",
        env={**os.environ, "STATE_DIR": str(STATE_DIR)},
    )
    GA_PID_FILE.write_text(str(_ga_proc.pid))
    print(f"[app] GA started: PID {_ga_proc.pid}")

threading.Thread(target=_start_ga, daemon=True).start()

# ── Telemetry readers ──────────────────────────────────────────────────────

def _load_state():
    try:
        return json.loads(STATE_FILE.read_text())
    except Exception:
        return {}

def _tail_log(n=60):
    try:
        lines = META_LOG.read_text().splitlines()
        # Show only epoch lines and GA status lines, skip Lisp compiler noise
        interesting = [l for l in lines if l.startswith("E ") or l.startswith("[") or "═══" in l or "SCC" in l]
        return "\n".join(interesting[-n:])
    except Exception:
        return "(no log yet — GA starting up, check back in ~2 minutes)"

def _build_plot_df():
    readings = parse_log(str(META_LOG))
    if not readings:
        return pd.DataFrame({"epoch": [], "value": [], "metric": []})

    rows = []
    for r in readings:
        epoch = r["epoch"]
        if "ops/int" in r:
            rows.append({"epoch": epoch, "value": r["ops/int"],      "metric": "ops/interaction"})
        if "RAF" in r:
            rows.append({"epoch": epoch, "value": min(r["RAF"], 300), "metric": "RAF ratio (capped 300)"})
        if "cyc" in r:
            rows.append({"epoch": epoch, "value": r["cyc"],           "metric": "autocatalytic cycles"})
    return pd.DataFrame(rows)

# ── Status card ────────────────────────────────────────────────────────────

def _status_md():
    state = _load_state()
    gen   = state.get("generation", "—")
    nodes = state.get("nodes", [])

    if not nodes:
        return "**Status:** GA initializing — first genome evaluation takes ~2 min..."

    best  = max(nodes, key=lambda n: n["fitness"])
    mean_f = sum(n["fitness"] for n in nodes) / len(nodes)

    # Best genome summary
    g = best.get("genome", {})
    genome_str = (
        f"L={g.get('L','?')}  "
        f"N={g.get('n_tapes','?')}  "
        f"bd={g.get('birth_death','?')}  "
        f"s={g.get('s_weight','?')}/k={g.get('k_weight','?')}/i={g.get('i_weight','?')}"
    )

    lines = [
        f"**Generation {gen}**  |  Best fitness: **{best['fitness']:.4f}**  |  Mean: {mean_f:.4f}",
        f"",
        f"**Best genome:** {genome_str}",
        f"",
        f"| Node | Fitness | Age |",
        f"|------|---------|-----|",
    ]
    for n in sorted(nodes, key=lambda x: -x["fitness"])[:8]:
        lines.append(f"| {n['node_id']} | {n['fitness']:.4f} | {n.get('age',0)} |")

    return "\n".join(lines)

# ── Gradio UI ──────────────────────────────────────────────────────────────

EXPLAINER = """
## What you're watching

This is a genetic algorithm searching for **abiogenesis** — the spontaneous origin of self-sustaining chemistry from random components.

The "soup" is a pool of **SKI combinator** programs (a Turing-complete symbolic calculus). Programs interact by concatenating and reducing — like chemical reactions. No fitness function is hand-coded; survival emerges from the dynamics.

**Three signals mark the phase transition:**

| Signal | What it means | Phase transition signature |
|--------|--------------|---------------------------|
| **ops/interaction** | Computation density per collision | Sudden jump (2→1000+) |
| **RAF ratio** | How far above autocatalytic threshold (Jain-Krishna 2001) | Sustained >1.0 |
| **Autocatalytic cycles** | Closed reaction loops (A makes B makes A) | Count spikes, then stabilizes |

**The genetic algorithm** runs 16 parallel soup instances with different parameters (tape length, population size, alphabet weights). After each evaluation round, high-fitness instances spread their parameters to neighbors on a small-world graph — evolution of the evolutionary conditions themselves.

**What we're looking for:** SCC (strongly connected component) spanning fraction crossing ~50% of the reaction graph. That's the autopoietic transition — the moment the reaction network closes on itself and becomes self-sustaining. Jain & Krishna observed this in 2001 in a toy catalytic network. We're watching for it in a symbolic computation substrate.

The first self-replicator appeared spontaneously: `W x y → x y y` — the W combinator discovered that duplicating its argument is self-replication. It wasn't seeded. It emerged.
"""

with gr.Blocks(title="SKI Soup — Abiogenesis in a Symbolic Calculus") as demo:
    gr.Markdown("# 🧬 SKI Combinator Soup")
    gr.Markdown("*Watching for the spontaneous origin of self-sustaining chemistry in a symbolic system*")

    with gr.Tabs():
        with gr.Tab("Live Telemetry"):
            with gr.Row():
                status_box = gr.Markdown("Loading...")

            plot = gr.LinePlot(
                x="epoch",
                y="value",
                color="metric",
                title="Phase transition signals over time  (gelation = ops/int jumps sharply upward)",
                x_title="Epoch",
                y_title="Value",
            )

            log_box = gr.Code(
                label="Soup log (epoch checkpoints + GA events)",
                language=None,
                lines=15,
            )

            refresh_btn = gr.Button("↻ Refresh", variant="primary")

            def on_refresh():
                return _status_md(), _build_plot_df(), _tail_log()

            refresh_btn.click(on_refresh, outputs=[status_box, plot, log_box])
            demo.load(on_refresh, outputs=[status_box, plot, log_box])

        with gr.Tab("What is this?"):
            gr.Markdown(EXPLAINER)

# ── /api/status endpoint for shepherd polling ─────────────────────────────────
app = demo.app  # Gradio exposes its FastAPI app here

try:
    from fastapi.responses import JSONResponse

    @app.get("/api/status")
    def api_status():
        """Machine-readable soup status for shepherd polling."""
        try:
            data = json.loads(TELEMETRY_FILE.read_text()) if TELEMETRY_FILE.exists() else {}
        except Exception:
            data = {}
        return JSONResponse({
            "status":      data.get("status", "unknown"),
            "epoch":       data.get("epoch", 0),
            "ops_per_int": data.get("ops_per_int", 0.0),
            "entropy":     data.get("entropy", 0.0),
            "raf_ratio":   data.get("raf_ratio", 0.0),
            "cycles":      data.get("cycles", 0),
            "catalysis_p": data.get("cat_p", 0.0),
        })
except Exception as e:
    print(f"[api] Could not register /api/status: {e}")

demo.launch(server_name="0.0.0.0", server_port=7860, theme=gr.themes.Monochrome())
