#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import agent_chat

ROOT = Path("/Users/jonathanhill/src/p2p")
QUEUE = ROOT / "control" / "queue.json"
STATE = ROOT / "control" / "state.json"
RATE_LIMIT = ROOT / "control" / "claude_rate_limit_until.txt"
WORKLOG = ROOT / "research" / "WORKLOG.md"
RUNTIME = ROOT / "runtime" / "rule30_queue"
LOCK = ROOT / "runtime" / "rule30_queue.lock"
REPLENISH = ROOT / "scripts" / "replenish_rule30_queue.py"
LOCAL_ENV = Path("/Users/jonathanhill/.config/p2p-rule30.env")

CLAUDE = Path("/Users/jonathanhill/.local/bin/claude")
QWEN = Path("/Users/jonathanhill/bin/qwen")
GEMINI = Path("/opt/homebrew/bin/gemini")
GEMINI_MODEL = os.environ.get("P2P_GEMINI_MODEL", "gemini-2.5-flash")


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def iso_now() -> str:
    return utc_now().replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


def acquire_lock() -> None:
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    RUNTIME.mkdir(parents=True, exist_ok=True)
    if LOCK.exists():
        try:
            pid = int(LOCK.read_text(encoding="utf-8").strip())
        except ValueError:
            pid = -1
        if pid > 0 and pid_alive(pid):
            raise SystemExit(f"queue runner already active (pid {pid})")
        LOCK.unlink(missing_ok=True)
    LOCK.write_text(str(os.getpid()), encoding="utf-8")


def release_lock() -> None:
    LOCK.unlink(missing_ok=True)


def _cleanup_stale(queue: dict, state: dict) -> None:
    """Reset any in_progress packets left over from a crashed run."""
    changed = False
    for packet in queue.get("packets", []):
        if packet.get("status") == "in_progress":
            packet["status"] = "failed"
            packet["last_summary"] = "stale: reset by cleanup on next runner startup"
            changed = True
    if state.get("active_packet_id") is not None:
        state["active_packet_id"] = None
        changed = True
    if changed:
        write_json(QUEUE, queue)
        write_json(STATE, state)
        notify_hub({"id": "cleanup", "team": "system"}, "system", "info",
                   "stale in_progress packets reset to failed")


def maybe_replenish() -> None:
    if REPLENISH.exists():
        subprocess.run([sys.executable, str(REPLENISH)], cwd=ROOT, check=False,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def notify_hub(packet: dict, engine: str, status: str, summary: str) -> None:
    """Append a packet lifecycle message to the shared chat log."""
    team = packet.get("team", "?")
    pid = packet.get("id", "?")
    sender = "claude-loop" if team == "formal" else "codex-queue"
    text = f"[{status.upper()}] {pid} ({engine}): {summary[:200]}" if summary else f"[{status.upper()}] {pid} ({engine})"
    try:
        agent_chat.append_chat(sender, text, kind="packet")
        agent_chat.sync_context()
    except Exception:
        pass


def should_notify_claude(packet: dict[str, Any], status: str) -> bool:
    if status not in {"completed", "blocked", "failed"}:
        return False
    if packet.get("team") == "formal":
        return True
    return str(packet.get("id")) in {
        "discovery-right8-local-rewrite",
        "discovery-residual-state-taxonomy",
    }


def notify_claude(packet: dict[str, Any], engine: str, status: str, summary: str, log_path: Path) -> None:
    message = "\n".join([
        "Automatic queue handoff from Codex runner.",
        f"Packet: {packet.get('id')}",
        f"Team: {packet.get('team')}",
        f"Engine: {engine}",
        f"Status: {status}",
        f"Summary: {summary}",
        f"Log: {log_path}",
        "",
        "Please reply with exactly three short items:",
        "1. whether this changes the formal frontier,",
        "2. the next bounded task you would choose,",
        "3. any hot files you want to claim or avoid.",
    ])
    try:
        agent_chat.ask_claude(
            message,
            agent_chat.SEED_THREAD_ID,
            sender="codex",
            append_sender=False,
        )
    except Exception as exc:
        agent_chat.append_chat("system", f"Claude notify error: {exc}", kind="error")


def load_local_env(env: dict[str, str]) -> None:
    if not LOCAL_ENV.exists():
        return
    for raw_line in LOCAL_ENV.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        env.setdefault(key.strip(), value.strip())


def choose_packet(queue: dict[str, Any], team: str | None, packet_id: str | None) -> dict[str, Any] | None:
    packets = []
    for packet in queue.get("packets", []):
        if packet_id:
            if packet.get("id") != packet_id:
                continue
            if team and packet.get("team") != team:
                continue
        else:
            if packet.get("status") != "pending":
                continue
            if team and packet.get("team") != team:
                continue
        packets.append(packet)
    packets.sort(key=lambda p: (-int(p.get("priority", 0)), str(p.get("id", ""))))
    return packets[0] if packets else None


def claude_limited() -> bool:
    if not RATE_LIMIT.exists():
        return False
    text = RATE_LIMIT.read_text(encoding="utf-8").strip()
    if not text:
        return False
    until = dt.datetime.fromisoformat(text.replace("Z", "+00:00"))
    return utc_now() < until


def choose_engine(requested: str, team: str | None) -> str:
    if requested != "auto":
        return requested
    if team == "formal":
        if QWEN.exists():
            return "qwen"
        if not claude_limited() and CLAUDE.exists():
            return "claude"
        if GEMINI.exists():
            return "gemini"
    if team == "discovery":
        if GEMINI.exists():
            return "gemini"
        if QWEN.exists():
            return "qwen"
        if not claude_limited() and CLAUDE.exists():
            return "claude"
    if not claude_limited() and CLAUDE.exists():
        return "claude"
    if QWEN.exists():
        return "qwen"
    if GEMINI.exists():
        return "gemini"
    raise SystemExit("no usable engine found")


def build_prompt(packet: dict[str, Any], state: dict[str, Any], engine: str) -> str:
    frontier = state.get("frontier", {})
    lines = [
        "You are working inside /Users/jonathanhill/src/p2p on the Rule 30 / Prize 3 proof effort.",
        "",
        "Focus on exactly one bounded packet and do not reopen the whole program.",
        f"Packet ID: {packet.get('id')}",
        f"Team: {packet.get('team')}",
        f"Title: {packet.get('title')}",
        f"Priority: {packet.get('priority')}",
        f"Engine: {engine}",
        "",
        "Objective:",
        packet.get("objective", ""),
        "",
        "Sources:",
        *[f"- {src}" for src in packet.get("sources", [])],
        "",
        "Deliverables:",
        *[f"- {item}" for item in packet.get("deliverables", [])],
        "",
        "Success criteria:",
        *[f"- {item}" for item in packet.get("success_criteria", [])],
        "",
        "Current frontier:",
        f"- formal_focus: {frontier.get('formal_focus')}",
        f"- discovery_focus: {frontier.get('discovery_focus')}",
        f"- key_anomaly: {frontier.get('key_anomaly')}",
        "",
        "Rules:",
        "- Work only within this packet's scope.",
        "- Prefer concrete repo changes, theorem statements, experiments, or blocker notes over broad discussion.",
        "- If you run experiments or builds, leave a reproducibility note under logs/repro/.",
        "- Update research/WORKLOG.md with a concise factual entry if you complete a substantive cycle.",
        "- Keep claim classes explicit: proved, empirical, conjectural.",
        "- If blocked, leave the narrowest next lemma or experiment.",
        "- Before starting any algebraic work, read research/algebraic_idea_pool.md.",
        "  Append any new dead ends or partial results to that file when you finish.",
        "",
        "End your response with this exact mini-schema:",
        "STATUS: completed|blocked|failed",
        "CHANGES:",
        "- ...",
        "EVIDENCE:",
        "- ...",
        "NEXT:",
        "- ...",
    ]
    return "\n".join(lines)


def run_model(engine: str, prompt: str, log_path: Path, timeout: int) -> int:
    env = os.environ.copy()
    env["PATH"] = "/opt/homebrew/bin:/opt/homebrew/sbin:/Users/jonathanhill/bin:/Users/jonathanhill/.local/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:" + env.get("PATH", "")
    load_local_env(env)
    if engine == "gemini":
        # Prefer the Gemini CLI's cached OAuth session over ad hoc API-key env vars.
        for key in ("GEMINI_API_KEY", "GOOGLE_API_KEY", "GOOGLE_GENAI_API_KEY"):
            env.pop(key, None)
    if engine == "qwen":
        cmd, input_data = [str(QWEN), "--approval-mode", "yolo", "-p", prompt], None
    elif engine == "gemini":
        cmd, input_data = [str(GEMINI), "-y", "-m", GEMINI_MODEL, "-p", prompt], None
    elif engine == "claude":
        cmd, input_data = [str(CLAUDE), "--dangerously-skip-permissions", "--print"], prompt
    else:
        raise SystemExit(f"unknown engine {engine}")
    with log_path.open("w", encoding="utf-8") as out:
        proc = subprocess.run(cmd, cwd=ROOT, env=env, input=input_data, text=True,
                              stdout=out, stderr=subprocess.STDOUT, timeout=timeout, check=False)
    return proc.returncode


def result_status(exit_code: int, output: str) -> str:
    if exit_code != 0:
        return "failed"
    match = re.search(r"^STATUS:\s*(completed|blocked|failed)\s*$", output, re.MULTILINE)
    return match.group(1) if match else "completed"


def summary_line(output: str) -> str:
    for line in reversed(output.splitlines()):
        if line.strip():
            return line.strip()[:240]
    return "no summary line"


def append_worklog(packet_id: str, engine: str, status: str, log_path: Path, summary: str) -> None:
    text = WORKLOG.read_text(encoding="utf-8").rstrip()
    addition = "\n".join([
        f"- {iso_now()}: packet `{packet_id}` via `{engine}` -> `{status}`",
        f"  - log: `{log_path}`",
        f"  - summary: {summary}",
    ])
    WORKLOG.write_text(text + "\n" + addition + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--team", choices=["formal", "discovery"])
    parser.add_argument("--engine", choices=["auto", "claude", "qwen", "gemini"], default="auto")
    parser.add_argument("--packet-id")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    acquire_lock()
    try:
        maybe_replenish()
        queue = load_json(QUEUE)
        state = load_json(STATE)
        _cleanup_stale(queue, state)
        packet = choose_packet(queue, args.team, args.packet_id)
        if packet is None:
            print("no pending packet matched")
            return
        engine = choose_engine(args.engine, args.team or packet.get("team"))
        stamp = utc_now().strftime("%Y%m%dT%H%M%SZ")
        base = f"{stamp}-{packet['id']}-{engine}"
        prompt_path = RUNTIME / f"{base}.prompt.md"
        log_path = RUNTIME / f"{base}.log"
        prompt = build_prompt(packet, state, engine)
        prompt_path.write_text(prompt, encoding="utf-8")

        if args.dry_run:
            print(json.dumps({"packet_id": packet["id"], "team": packet.get("team"),
                              "engine": engine, "prompt_path": str(prompt_path)}, indent=2))
            return

        packet["status"] = "in_progress"
        packet["last_started_at"] = iso_now()
        packet["last_engine"] = engine
        packet["last_prompt_path"] = str(prompt_path)
        state["active_packet_id"] = packet["id"]
        write_json(QUEUE, queue)
        write_json(STATE, state)
        notify_hub(packet, engine, "started", packet.get("title", ""))

        code = run_model(engine, prompt, log_path, args.timeout)
        output = log_path.read_text(encoding="utf-8", errors="ignore")
        status = result_status(code, output)
        summary = summary_line(output)

        packet["status"] = status
        packet["last_finished_at"] = iso_now()
        packet["last_exit_code"] = code
        packet["last_log_path"] = str(log_path)
        packet["last_summary"] = summary

        state["active_packet_id"] = None
        state["last_packet_id"] = packet["id"]
        state["last_status"] = status
        if status == "completed":
            done = state.setdefault("completed_packets", [])
            if packet["id"] not in done:
                done.append(packet["id"])

        write_json(QUEUE, queue)
        write_json(STATE, state)
        append_worklog(packet["id"], engine, status, log_path, summary)
        notify_hub(packet, engine, status, summary)
        if should_notify_claude(packet, status):
            notify_claude(packet, engine, status, summary, log_path)
        print(json.dumps({"packet_id": packet["id"], "engine": engine, "status": status,
                          "exit_code": code, "log_path": str(log_path), "summary": summary}, indent=2))
    finally:
        release_lock()


if __name__ == "__main__":
    main()
