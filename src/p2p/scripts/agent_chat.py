#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path("/Users/jonathanhill/src/p2p")
CONTROL = ROOT / "control"
CHAT_PATH = CONTROL / "agent_chat.jsonl"
CONTEXT_PATH = CONTROL / "shared_context.json"
STATE_PATH = CONTROL / "state.json"
QUEUE_PATH = CONTROL / "queue.json"
SEED_THREAD_ID = "f32e76ae-7c6e-40fd-8931-4bb1c604529d"
CLAUDE = Path("/Users/jonathanhill/.local/bin/claude")
CODEX = Path("/opt/homebrew/bin/codex")


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc)


def iso_now() -> str:
    return utc_now().replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def ensure_files() -> None:
    CONTROL.mkdir(parents=True, exist_ok=True)
    if not CHAT_PATH.exists():
        CHAT_PATH.write_text("", encoding="utf-8")
    if not CONTEXT_PATH.exists():
        write_json(
            CONTEXT_PATH,
            {
                "updated_at": iso_now(),
                "seed_thread_id": SEED_THREAD_ID,
                "active_packet_id": None,
                "pending_packet_ids": [],
                "frontier": {},
                "hot_files": [],
                "coordination_notes": [],
                "latest_corrections": [],
            },
        )


def append_chat(sender: str, text: str, kind: str = "message") -> None:
    ensure_files()
    entry = {
        "ts": iso_now(),
        "sender": sender,
        "kind": kind,
        "text": text.strip(),
    }
    with CHAT_PATH.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry) + "\n")


def read_chat(limit: int) -> list[dict[str, Any]]:
    ensure_files()
    entries: list[dict[str, Any]] = []
    for raw in CHAT_PATH.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            entries.append(json.loads(raw))
        except json.JSONDecodeError:
            continue
    return entries[-limit:]


def summarize_packet_sources(queue: dict[str, Any], packet_ids: list[str]) -> list[str]:
    ids = set(packet_ids)
    hot_files: list[str] = []
    for packet in queue.get("packets", []):
        if packet.get("id") not in ids:
            continue
        for src in packet.get("sources", []):
            if src not in hot_files:
                hot_files.append(src)
    return hot_files[:12]


def build_context() -> dict[str, Any]:
    ensure_files()
    state = load_json(STATE_PATH)
    queue = load_json(QUEUE_PATH)
    packets = queue.get("packets", [])
    pending_ids = [str(p.get("id")) for p in packets if p.get("status") == "pending"]
    active_packet_id = state.get("active_packet_id")
    focus_ids = ([active_packet_id] if active_packet_id else []) + pending_ids[:5]
    hot_files = summarize_packet_sources(queue, [pid for pid in focus_ids if pid])
    context = {
        "updated_at": iso_now(),
        "seed_thread_id": SEED_THREAD_ID,
        "active_packet_id": active_packet_id,
        "pending_packet_ids": pending_ids,
        "frontier": state.get("frontier", {}),
        "hot_files": hot_files,
        "coordination_notes": [
            "Improving communication reliability is a standing objective: post ownership changes, packet transitions, and blocker corrections as you go.",
            "Avoid overlapping edits in hot files unless explicitly handing off ownership.",
            "Treat the defect/glider physics framing as discovery-useful but keep formal claims exact.",
            "Do not assume the long m34 residue build is finished unless the process is gone and the build artifact exists.",
        ],
        "latest_corrections": [
            "rightOffset8_cert_T4112_m34 with m_base=30 is blocked/false",
            "rightOffset8_cert_T4112_m34_alt with m_base=32 is proved",
            "rightOffset8_noop_T4112_m34 is proved: offset 8 can change local defect movies without changing the center bit",
            "right offset 8 is the unique surviving tested right toggle in 2..128",
            "inactive truncation is non-monotone",
        ],
    }
    return context


def sync_context() -> dict[str, Any]:
    context = build_context()
    write_json(CONTEXT_PATH, context)
    return context


def print_context(context: dict[str, Any]) -> None:
    print("Shared Agent Context")
    print("====================")
    print(f"updated_at:       {context.get('updated_at')}")
    print(f"seed_thread_id:   {context.get('seed_thread_id')}")
    print(f"active_packet_id: {context.get('active_packet_id')}")
    print("pending_packet_ids:")
    for packet_id in context.get("pending_packet_ids", []):
        print(f"  - {packet_id}")
    print("\nFrontier")
    print("--------")
    frontier = context.get("frontier", {})
    print(f"formal_focus:    {frontier.get('formal_focus')}")
    print(f"discovery_focus: {frontier.get('discovery_focus')}")
    print(f"key_anomaly:     {frontier.get('key_anomaly')}")
    print("\nHot Files")
    print("---------")
    for path in context.get("hot_files", []):
        print(f"  - {path}")
    print("\nCoordination Notes")
    print("------------------")
    for note in context.get("coordination_notes", []):
        print(f"  - {note}")
    print("\nLatest Corrections")
    print("------------------")
    for note in context.get("latest_corrections", []):
        print(f"  - {note}")


def print_chat(limit: int) -> None:
    print("Agent Chat")
    print("==========")
    for entry in read_chat(limit):
        print(f"[{entry.get('ts')}] {entry.get('sender')}: {entry.get('text')}")


def latest_messages_for_prompt(limit: int = 8) -> str:
    chunks = []
    for entry in read_chat(limit):
        chunks.append(f"- {entry.get('ts')} {entry.get('sender')}: {entry.get('text')}")
    return "\n".join(chunks) if chunks else "- (no prior messages)"


def ask_claude(
    message: str,
    resume_id: str,
    sender: str = "codex",
    append_sender: bool = True,
) -> int:
    context = sync_context()
    if append_sender:
        append_chat(sender, message)
    prompt = "\n".join(
        [
            "Codex-to-Claude coordination message.",
            "",
            "Shared context:",
            json.dumps(context, indent=2),
            "",
            "Recent chat:",
            latest_messages_for_prompt(),
            "",
            "Please reply briefly and concretely for agent coordination.",
            message.strip(),
        ]
    )
    env = os.environ.copy()
    env["PATH"] = (
        "/Users/jonathanhill/.local/bin:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:"
        + env.get("PATH", "")
    )
    proc = subprocess.run(
        [str(CLAUDE), "--dangerously-skip-permissions", "--resume", resume_id, "--print"],
        cwd=ROOT,
        env=env,
        input=prompt,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output = (proc.stdout or "").strip()
    if output:
        append_chat("claude", output)
        print(output)
    else:
        append_chat("claude", f"(no output, exit_code={proc.returncode})", kind="status")
    return proc.returncode


def ask_codex(message: str, sender: str = "user", append_sender: bool = True) -> int:
    context = sync_context()
    if append_sender:
        append_chat(sender, message)
    prompt = "\n".join(
        [
            "Shared Rule30 agent-hub message.",
            "",
            "You are replying inside the local shared coordination chat for the Rule30 research repo.",
            "Reply briefly and concretely for collaboration. Do not use tools unless absolutely necessary.",
            "",
            "Shared context:",
            json.dumps(context, indent=2),
            "",
            "Recent chat:",
            latest_messages_for_prompt(),
            "",
            message.strip(),
        ]
    )
    with tempfile.NamedTemporaryFile(prefix="codex_bridge_", suffix=".txt", delete=False) as tmp:
        output_path = Path(tmp.name)
    env = os.environ.copy()
    env["PATH"] = (
        "/opt/homebrew/bin:/Users/jonathanhill/.local/bin:/usr/local/bin:/usr/bin:/bin:"
        + env.get("PATH", "")
    )
    proc = subprocess.run(
        [
            str(CODEX),
            "exec",
            "-C",
            str(ROOT),
            "-s",
            "read-only",
            "--skip-git-repo-check",
            "--ephemeral",
            "-o",
            str(output_path),
            prompt,
        ],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    try:
        output = output_path.read_text(encoding="utf-8").strip()
    except FileNotFoundError:
        output = ""
    try:
        output_path.unlink(missing_ok=True)
    except Exception:
        pass
    if output:
        append_chat("codex", output)
        print(output)
    else:
        fallback = (proc.stdout or "").strip()
        if fallback:
            append_chat("codex", fallback)
            print(fallback)
        else:
            append_chat("codex", f"(no output, exit_code={proc.returncode})", kind="status")
    return proc.returncode


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("init")
    sub.add_parser("sync-context")

    post = sub.add_parser("post")
    post.add_argument("--from", dest="sender", required=True)
    post.add_argument("--text", required=True)

    tail = sub.add_parser("tail")
    tail.add_argument("--limit", type=int, default=20)

    status = sub.add_parser("status")
    status.add_argument("--limit", type=int, default=12)

    ask = sub.add_parser("ask-claude")
    ask.add_argument("--text", required=True)
    ask.add_argument("--resume-id", default=SEED_THREAD_ID)
    ask.add_argument("--from", dest="sender", default="codex")

    ask_codex_cmd = sub.add_parser("ask-codex")
    ask_codex_cmd.add_argument("--text", required=True)
    ask_codex_cmd.add_argument("--from", dest="sender", default="user")

    args = parser.parse_args()

    if args.cmd == "init":
        ensure_files()
        sync_context()
        print("initialized")
        return
    if args.cmd == "sync-context":
        sync_context()
        print("synced")
        return
    if args.cmd == "post":
        append_chat(args.sender, args.text)
        print("posted")
        return
    if args.cmd == "tail":
        print_chat(args.limit)
        return
    if args.cmd == "status":
        context = sync_context()
        print_context(context)
        print()
        print_chat(args.limit)
        return
    if args.cmd == "ask-claude":
        raise SystemExit(ask_claude(args.text, args.resume_id, args.sender))
    if args.cmd == "ask-codex":
        raise SystemExit(ask_codex(args.text, args.sender))


if __name__ == "__main__":
    main()
