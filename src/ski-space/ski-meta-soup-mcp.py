#!/usr/bin/env python3
"""
ski-meta-soup-mcp.py

MCP server exposing SKI meta-soup GA state (read-only).
Reads ~/.ski-meta/state.json and ~/.ski-meta/lineage.jsonl.
Also exposes GA health check and restart capability.

Tools:
  get_meta_status     — generation, all node fitnesses, best genome, mean fitness
  get_best_genome     — highest-fitness strategy genome found so far
  get_fitness_landscape — fitness values for all 16 nodes
  get_lineage_tree    — phylogenetic tree of genome lineages
  restart_ga_if_dead  — restart the meta-soup GA if it's not running
"""

import sys
import json
import subprocess
from pathlib import Path

STATE_DIR   = Path.home() / ".ski-meta"
STATE_FILE  = STATE_DIR / "state.json"
LINEAGE_FILE = STATE_DIR / "lineage.jsonl"
PYTHON3     = "/opt/homebrew/bin/python3"
META_SOUP   = Path(__file__).parent / "ski-meta-soup.py"

# ── Tool definitions ──────────────────────────────────────────────────────────

TOOLS = [
    {
        "name": "get_meta_status",
        "description": "Get current meta-soup state: generation, all node fitnesses, best genome, mean fitness.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "get_best_genome",
        "description": "Get the highest-fitness strategy genome found so far, with interpretation.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "get_fitness_landscape",
        "description": "Get fitness values for all nodes in the meta-graph, showing the landscape shape.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "get_lineage_tree",
        "description": "Get the phylogenetic tree of genome lineages: who descended from whom, fitness at each node, dominant clades.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
    {
        "name": "restart_ga_if_dead",
        "description": "Check if meta-soup GA is running. If dead, restart it. Returns status.",
        "inputSchema": {"type": "object", "properties": {}, "required": []}
    },
]

# ── State readers ─────────────────────────────────────────────────────────────

def load_state():
    try:
        return json.loads(STATE_FILE.read_text())
    except Exception as e:
        return {"error": str(e)}

def load_lineage():
    try:
        lines = LINEAGE_FILE.read_text().splitlines()
        return [json.loads(l) for l in lines if l.strip()]
    except Exception:
        return []

def ga_is_running():
    try:
        out = subprocess.check_output(
            ["pgrep", "-f", "ski-meta-soup.py.*--run"],
            stderr=subprocess.DEVNULL
        )
        return bool(out.strip())
    except subprocess.CalledProcessError:
        return False

# ── Tool implementations ──────────────────────────────────────────────────────

def handle_tool(name, args):
    if name == "get_meta_status":
        state = load_state()
        if "error" in state:
            return {"status": "no_data", "error": state["error"]}

        gen   = state.get("generation", 0)
        nodes = state.get("nodes", [])

        if not nodes:
            return {"status": "initializing", "generation": gen}

        best  = max(nodes, key=lambda n: n.get("fitness", 0))
        mean_f = sum(n.get("fitness", 0) for n in nodes) / len(nodes)

        return {
            "generation": gen,
            "n_nodes": len(nodes),
            "mean_fitness": round(mean_f, 6),
            "best_fitness": round(best.get("fitness", 0), 6),
            "best_node_id": best.get("node_id"),
            "best_genome": best.get("genome", {}),
            "nodes": [
                {
                    "node_id": n.get("node_id"),
                    "fitness": round(n.get("fitness", 0), 6),
                    "age": n.get("age", 0),
                    "genome": n.get("genome", {})
                }
                for n in sorted(nodes, key=lambda x: -x.get("fitness", 0))
            ]
        }

    elif name == "get_best_genome":
        state = load_state()
        nodes = state.get("nodes", [])
        if not nodes:
            return {"status": "no_data"}
        best = max(nodes, key=lambda n: n.get("fitness", 0))
        g = best.get("genome", {})
        return {
            "node_id": best.get("node_id"),
            "fitness": round(best.get("fitness", 0), 6),
            "genome": g,
            "interpretation": (
                f"L={g.get('L')} tape length, "
                f"N={g.get('n_tapes')} tapes, "
                f"birth_death={'on' if g.get('birth_death') else 'off'}, "
                f"weights S={g.get('s_weight')}/K={g.get('k_weight')}/I={g.get('i_weight')}, "
                f"extra={g.get('extra_combinators', 'none')}"
            )
        }

    elif name == "get_fitness_landscape":
        state = load_state()
        nodes = state.get("nodes", [])
        if not nodes:
            return {"status": "no_data"}
        landscape = [
            {
                "node_id": n.get("node_id"),
                "fitness": round(n.get("fitness", 0), 6),
                "age": n.get("age", 0),
            }
            for n in nodes
        ]
        fitnesses = [n["fitness"] for n in landscape]
        return {
            "generation": state.get("generation", 0),
            "landscape": sorted(landscape, key=lambda x: -x["fitness"]),
            "max_fitness": max(fitnesses) if fitnesses else 0,
            "min_fitness": min(fitnesses) if fitnesses else 0,
            "mean_fitness": round(sum(fitnesses) / len(fitnesses), 6) if fitnesses else 0,
            "nonzero_count": sum(1 for f in fitnesses if f > 0),
        }

    elif name == "get_lineage_tree":
        lineage = load_lineage()
        if not lineage:
            return {"status": "no_lineage_yet", "message": "No genomes evaluated yet"}

        # Build tree structure
        nodes_by_id = {}
        for entry in lineage:
            nid = entry.get("node_id")
            if nid not in nodes_by_id or entry.get("generation", 0) > nodes_by_id[nid].get("generation", 0):
                nodes_by_id[nid] = entry

        # Find dominant clade (node with highest fitness)
        dominant = max(nodes_by_id.values(), key=lambda x: x.get("fitness", 0), default=None)

        return {
            "total_lineage_entries": len(lineage),
            "unique_nodes": len(nodes_by_id),
            "dominant_node": dominant,
            "lineage_tail": lineage[-10:],  # last 10 entries
        }

    elif name == "restart_ga_if_dead":
        if ga_is_running():
            try:
                pid_out = subprocess.check_output(
                    ["pgrep", "-f", "ski-meta-soup.py.*--run"],
                    stderr=subprocess.DEVNULL
                ).strip().decode()
                return {"status": "running", "pid": pid_out}
            except Exception:
                return {"status": "running"}

        # Restart it
        import os
        log_path = STATE_DIR / "soup.log"
        log_fh = open(log_path, "a")
        proc = subprocess.Popen(
            [PYTHON3, str(META_SOUP), "--run"],
            stdout=log_fh, stderr=log_fh,
            cwd=str(META_SOUP.parent),
        )
        return {
            "status": "restarted",
            "pid": proc.pid,
            "message": f"Meta-soup GA restarted with PID {proc.pid}"
        }

    else:
        return {"error": f"Unknown tool: {name}"}

# ── MCP stdio loop ────────────────────────────────────────────────────────────

def main():
    for raw_line in sys.stdin:
        raw_line = raw_line.strip()
        if not raw_line:
            continue
        try:
            req = json.loads(raw_line)
        except json.JSONDecodeError:
            continue

        rid    = req.get("id")
        method = req.get("method", "")
        params = req.get("params", {})

        if method == "initialize":
            resp = {
                "jsonrpc": "2.0", "id": rid,
                "result": {
                    "protocolVersion": "2024-11-05",
                    "capabilities": {"tools": {}},
                    "serverInfo": {"name": "ski-meta-soup", "version": "1.0"}
                }
            }
        elif method == "notifications/initialized":
            continue
        elif method == "tools/list":
            resp = {"jsonrpc": "2.0", "id": rid, "result": {"tools": TOOLS}}
        elif method == "tools/call":
            tool_name = params.get("name", "")
            tool_args = params.get("arguments", {})
            try:
                result = handle_tool(tool_name, tool_args)
                resp = {
                    "jsonrpc": "2.0", "id": rid,
                    "result": {
                        "content": [{"type": "text", "text": json.dumps(result, indent=2)}]
                    }
                }
            except Exception as e:
                resp = {
                    "jsonrpc": "2.0", "id": rid,
                    "result": {
                        "content": [{"type": "text", "text": json.dumps({"error": str(e)})}],
                        "isError": True
                    }
                }
        else:
            resp = {
                "jsonrpc": "2.0", "id": rid,
                "error": {"code": -32601, "message": f"Method not found: {method}"}
            }

        print(json.dumps(resp), flush=True)

if __name__ == "__main__":
    main()
