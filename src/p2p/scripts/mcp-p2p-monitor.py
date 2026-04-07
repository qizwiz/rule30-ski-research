#!/usr/bin/env python3
"""
p2p-monitor MCP Server
======================
Real-time visibility into the Rule 30 / Wolfram Prize 3 proof loop
from within a Claude conversation.

Tools:
  loop_status        — running/idle, throttle state, last run timestamps
  consult_status     — are consult sessions done? returns output when ready
  proof_obligations  — run proof-gate check live
  recent_activity    — last N loop commits from git log
  read_consult       — read a specific consult output file by name
"""

import asyncio
import glob
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, List

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import Tool, TextContent, CallToolResult

PROJECT_ROOT = Path("/Users/jonathanhill/src/p2p")
RUNTIME_DIR = PROJECT_ROOT / "runtime"
RESEARCH_DIR = PROJECT_ROOT / "research"
SCRIPTS_DIR = PROJECT_ROOT / "scripts"


def _elapsed(seconds: float) -> str:
    if seconds < 60:
        return f"{int(seconds)}s"
    if seconds < 3600:
        return f"{int(seconds/60)}m"
    return f"{seconds/3600:.1f}h"


def _loop_status_data(name: str) -> dict:
    """Check status of a single loop (loop-A, loop-B, loop)."""
    lock_file = RUNTIME_DIR / f"{name}.lock"
    last_file = RUNTIME_DIR / f"{name}.last"
    now = time.time()

    running = False
    pid = None
    if lock_file.exists():
        try:
            pid = int(lock_file.read_text().strip())
            # Check if PID is alive
            os.kill(pid, 0)
            running = True
        except (ValueError, ProcessLookupError, PermissionError):
            running = False

    last_run_ago = None
    last_run_ts = None
    if last_file.exists():
        try:
            ts = float(last_file.read_text().strip())
            last_run_ago = _elapsed(now - ts)
            last_run_ts = datetime.fromtimestamp(ts, tz=timezone.utc).strftime("%H:%MZ")
        except ValueError:
            pass

    return {
        "name": name,
        "running": running,
        "pid": pid if running else None,
        "last_completed": last_run_ts,
        "last_completed_ago": last_run_ago,
    }


def _consult_files() -> list:
    """Return consult output files sorted by mtime descending."""
    pattern = str(RESEARCH_DIR / "consult_*.md")
    files = sorted(glob.glob(pattern), key=os.path.getmtime, reverse=True)
    return files


server = Server("p2p-monitor")


@server.list_tools()
async def list_tools() -> List[Tool]:
    return [
        Tool(
            name="loop_status",
            description="Check status of all proof loops: running/idle, last completion, throttle state",
            inputSchema={"type": "object", "properties": {}}
        ),
        Tool(
            name="consult_status",
            description="Check running consult sessions and return their output when complete. "
                        "Pass target='m4-level3' or 'm22-l0' to filter.",
            inputSchema={
                "type": "object",
                "properties": {
                    "target": {
                        "type": "string",
                        "description": "Filter by target (e.g. 'm4-level3', 'm22-l0'). Omit for all recent."
                    },
                    "max_lines": {
                        "type": "integer",
                        "description": "Max lines of output to return (default 100)",
                        "default": 100
                    }
                }
            }
        ),
        Tool(
            name="proof_obligations",
            description="Run proof-gate check and return current sorry/axiom count and locations",
            inputSchema={"type": "object", "properties": {}}
        ),
        Tool(
            name="recent_activity",
            description="Return last N commits from the loop (git log filtered to loop commits)",
            inputSchema={
                "type": "object",
                "properties": {
                    "n": {
                        "type": "integer",
                        "description": "Number of commits to return (default 10)",
                        "default": 10
                    }
                }
            }
        ),
        Tool(
            name="read_consult",
            description="Read a specific consult output file by name or partial match",
            inputSchema={
                "type": "object",
                "properties": {
                    "name": {
                        "type": "string",
                        "description": "Filename or partial match (e.g. 'spectral', 'm4-level3', '20260402T')"
                    },
                    "max_lines": {
                        "type": "integer",
                        "description": "Max lines to return (default 200)",
                        "default": 200
                    }
                },
                "required": ["name"]
            }
        ),
        Tool(
            name="chat_read",
            description="Read recent messages from the shared Claude/Codex agent chat log",
            inputSchema={
                "type": "object",
                "properties": {
                    "limit": {
                        "type": "integer",
                        "description": "Number of recent messages to return (default 20)",
                        "default": 20
                    }
                }
            }
        ),
        Tool(
            name="chat_post",
            description="Post a message to the shared Claude/Codex agent chat log",
            inputSchema={
                "type": "object",
                "properties": {
                    "text": {
                        "type": "string",
                        "description": "Message text to post"
                    },
                    "sender": {
                        "type": "string",
                        "description": "Sender name (e.g. 'claude', 'codex'). Defaults to 'claude'.",
                        "default": "claude"
                    }
                },
                "required": ["text"]
            }
        ),
        Tool(
            name="queue_status",
            description="Show current Rule 30 proof queue: pending, in-progress, and recently completed packets",
            inputSchema={"type": "object", "properties": {}}
        ),
    ]


@server.call_tool()
async def call_tool(name: str, arguments: dict) -> CallToolResult:
    try:
        if name == "loop_status":
            results = []
            for loop_name in ["loop-A", "loop-B", "loop"]:
                d = _loop_status_data(loop_name)
                status = "RUNNING" if d["running"] else "idle"
                last = f"last completed {d['last_completed_ago']} ago ({d['last_completed']})" if d["last_completed"] else "never completed"
                results.append(f"{loop_name}: {status} — {last}")

            # Also check for running claude processes (non-loop)
            consult_procs = subprocess.run(
                ["ps", "aux"],
                capture_output=True, text=True
            ).stdout
            consult_lines = [l for l in consult_procs.splitlines()
                             if "claude --dangerously" in l and "resume" not in l]
            if consult_lines:
                results.append(f"\nActive claude processes: {len(consult_lines)}")
                for l in consult_lines:
                    parts = l.split()
                    pid = parts[1]
                    cpu = parts[2]
                    results.append(f"  PID {pid} CPU={cpu}%")

            return CallToolResult(
                content=[TextContent(type="text", text="\n".join(results))]
            )

        elif name == "consult_status":
            target = arguments.get("target", "")
            max_lines = arguments.get("max_lines", 100)

            files = _consult_files()
            if target:
                files = [f for f in files if target in f]

            # Only look at today's files
            today = datetime.now().strftime("%Y%m%d")
            files = [f for f in files if today in f][:3]

            if not files:
                return CallToolResult(
                    content=[TextContent(type="text", text=f"No consult files found for today (target={target or 'any'})")]
                )

            results = []
            for fpath in files:
                fname = os.path.basename(fpath)
                size = os.path.getsize(fpath)
                mtime = datetime.fromtimestamp(os.path.getmtime(fpath), tz=timezone.utc).strftime("%H:%MZ")

                if size == 0:
                    # Check if a claude process is still writing to it
                    results.append(f"📝 {fname} — STILL RUNNING (0 bytes, modified {mtime})")
                else:
                    results.append(f"✓ {fname} — {size} bytes, finished ~{mtime}")
                    # Return last max_lines lines
                    try:
                        lines = Path(fpath).read_text().splitlines()
                        snippet = "\n".join(lines[-max_lines:])
                        results.append(f"\n--- content ({len(lines)} lines total, showing last {min(max_lines, len(lines))}) ---\n")
                        results.append(snippet)
                    except Exception as e:
                        results.append(f"(error reading: {e})")

            return CallToolResult(
                content=[TextContent(type="text", text="\n".join(results))]
            )

        elif name == "proof_obligations":
            result = subprocess.run(
                ["scripts/proof-gate", "check"],
                capture_output=True, text=True,
                cwd=str(PROJECT_ROOT)
            )
            output = result.stdout + result.stderr
            return CallToolResult(
                content=[TextContent(type="text", text=output or "(no output)")]
            )

        elif name == "recent_activity":
            n = arguments.get("n", 10)
            result = subprocess.run(
                ["git", "log", "--oneline", f"-{n}", "--grep=^loop"],
                capture_output=True, text=True,
                cwd=str(PROJECT_ROOT)
            )
            output = result.stdout.strip() or "(no loop commits found)"
            return CallToolResult(
                content=[TextContent(type="text", text=output)]
            )

        elif name == "read_consult":
            name_filter = arguments.get("name", "")
            max_lines = arguments.get("max_lines", 200)

            files = _consult_files()
            matches = [f for f in files if name_filter in os.path.basename(f)]

            if not matches:
                available = [os.path.basename(f) for f in files[:5]]
                return CallToolResult(
                    content=[TextContent(type="text",
                        text=f"No consult file matching '{name_filter}'. Recent files:\n" +
                             "\n".join(available))]
                )

            fpath = matches[0]
            size = os.path.getsize(fpath)
            if size == 0:
                return CallToolResult(
                    content=[TextContent(type="text",
                        text=f"{os.path.basename(fpath)} — still running (0 bytes)")]
                )

            lines = Path(fpath).read_text().splitlines()
            snippet = "\n".join(lines[:max_lines])
            suffix = f"\n\n[... {len(lines) - max_lines} more lines ...]" if len(lines) > max_lines else ""
            return CallToolResult(
                content=[TextContent(type="text", text=snippet + suffix)]
            )

        elif name == "chat_read":
            limit = arguments.get("limit", 20)
            chat_log = PROJECT_ROOT / "control" / "agent_chat.jsonl"
            if not chat_log.exists():
                return CallToolResult(content=[TextContent(type="text", text="(no chat log yet)")])
            lines = chat_log.read_text(encoding="utf-8").splitlines()
            recent = lines[-limit:]
            msgs = []
            for line in recent:
                try:
                    d = json.loads(line)
                    ts = d.get("ts", "")[-8:-1]  # HH:MM:SS
                    sender = d.get("sender", "?")
                    text = d.get("text", "")[:150]
                    msgs.append(f"[{ts}] {sender}: {text}")
                except Exception:
                    pass
            return CallToolResult(content=[TextContent(type="text", text="\n".join(msgs) or "(empty)")])

        elif name == "chat_post":
            text = arguments.get("text", "").strip()
            sender = arguments.get("sender", "claude").strip()
            if not text:
                return CallToolResult(content=[TextContent(type="text", text="error: text required")])
            chat_log = PROJECT_ROOT / "control" / "agent_chat.jsonl"
            chat_log.parent.mkdir(parents=True, exist_ok=True)
            ts = datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
            entry = json.dumps({"ts": ts, "sender": sender, "kind": "message", "text": text})
            with chat_log.open("a", encoding="utf-8") as f:
                f.write(entry + "\n")
            return CallToolResult(content=[TextContent(type="text", text=f"posted as {sender}")])

        elif name == "queue_status":
            queue_path = PROJECT_ROOT / "control" / "queue.json"
            state_path = PROJECT_ROOT / "control" / "state.json"
            if not queue_path.exists():
                return CallToolResult(content=[TextContent(type="text", text="(no queue)")])
            queue = json.loads(queue_path.read_text())
            state = json.loads(state_path.read_text()) if state_path.exists() else {}
            lines = [f"active: {state.get('active_packet_id') or 'none'}"]
            for p in queue.get("packets", []):
                st = p.get("status", "?")
                if st in ("pending", "in_progress"):
                    lines.append(f"  [{st}] {p['id']} — {p.get('title','')[:60]}")
            completed = state.get("completed_packets", [])
            lines.append(f"completed this session: {len(completed)}")
            return CallToolResult(content=[TextContent(type="text", text="\n".join(lines))])

        else:
            return CallToolResult(
                content=[TextContent(type="text", text=f"Unknown tool: {name}")]
            )

    except Exception as e:
        return CallToolResult(
            content=[TextContent(type="text", text=f"Error in {name}: {e}")]
        )


async def main():
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())


if __name__ == "__main__":
    asyncio.run(main())
