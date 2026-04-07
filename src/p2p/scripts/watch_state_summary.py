#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path("/Users/jonathanhill/src/p2p")
STATE = ROOT / "control" / "state.json"
QUEUE = ROOT / "control" / "queue.json"


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    state = load_json(STATE)
    queue = load_json(QUEUE)
    packets = queue.get("packets", [])
    pending = [p for p in packets if p.get("status") == "pending"]
    completed = [p for p in packets if p.get("status") == "completed"]
    failed = [p for p in packets if p.get("status") == "failed"]

    print("Rule30 Queue State")
    print("==================")
    print(f"active_packet_id: {state.get('active_packet_id')}")
    print(f"last_packet_id:   {state.get('last_packet_id')}")
    print(f"last_status:      {state.get('last_status')}")
    print(
        "counts:           "
        f"pending={len(pending)} completed={len(completed)} failed={len(failed)} total={len(packets)}"
    )

    frontier = state.get("frontier", {})
    print("\nFrontier")
    print("--------")
    print(f"formal_focus:    {frontier.get('formal_focus')}")
    print(f"discovery_focus: {frontier.get('discovery_focus')}")
    print(f"key_anomaly:     {frontier.get('key_anomaly')}")

    if pending:
        print("\nPending Packets")
        print("---------------")
        for packet in sorted(pending, key=lambda p: (-int(p.get("priority", 0)), str(p.get("id", "")))):
            print(
                f"{packet.get('priority', 0):>3}  "
                f"{packet.get('team', '?'):<9}  "
                f"{packet.get('id', '?')}"
            )

    recent = sorted(
        [p for p in packets if p.get("last_finished_at")],
        key=lambda p: str(p.get("last_finished_at")),
        reverse=True,
    )[:5]
    if recent:
        print("\nRecent Packet Results")
        print("---------------------")
        for packet in recent:
            print(
                f"{packet.get('last_finished_at')}  "
                f"{packet.get('status', '?'):<9}  "
                f"{packet.get('id', '?')}"
            )


if __name__ == "__main__":
    main()
