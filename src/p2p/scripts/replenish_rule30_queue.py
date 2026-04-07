#!/usr/bin/env python3
"""
Reinsert the current grounded Rule 30 packet batch into control/queue.json.

This borrows the small-batch packet idea from autoresearch-ski but keeps the
content tied to the live Rule 30 frontier: m=34/m=36 formal closure and the
defect-state / right-offset-8 program.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ROOT = Path("/Users/jonathanhill/src/p2p")
QUEUE_PATH = ROOT / "control" / "queue.json"
STATE_PATH = ROOT / "control" / "state.json"


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2)
        handle.write("\n")


def packet_ids_with_status(queue: dict[str, Any], status: str) -> set[str]:
    return {
        str(packet.get("id"))
        for packet in queue.get("packets", [])
        if packet.get("status") == status
    }


def grounded_packet_batch() -> list[dict[str, Any]]:
    return [
        {
            "id": "formal-m36-witness-kernel",
            "type": "formal",
            "priority": 100,
            "status": "pending",
            "title": "Build the m=36 witness kernel the same way m=34 was closed",
            "objective": "Construct the first compile-safe m=36 kernel: period certs for the active witness family, base sensitivity certs for the known active residues, and the narrowest Lean surface needed to route SubcaseBPeriod through a dedicated m=36 branch instead of the generic late-tail split.",
            "sources": [
                "/Users/jonathanhill/src/p2p/P2p/CA_Array_m34.lean",
                "/Users/jonathanhill/src/p2p/P2p/CA_Array_m34_residues.lean",
                "/Users/jonathanhill/src/p2p/P2p/SubcaseBPeriod.lean",
                "/Users/jonathanhill/src/p2p/research/findings.md",
                "/Users/jonathanhill/src/p2p/research/patterns.md"
            ],
            "deliverables": [
                "One new m=36 Lean kernel file or explicit blocker",
                "One exact witness family for the active m=36 residues",
                "One compile result or blocker note tied to the touched file"
            ],
            "success_criteria": [
                "The packet stays on m=36 rather than reopening the whole late tail",
                "Any Lean edits are compile-safe and theorem-shaped",
                "The packet leaves the next m=36 residue step clearer than before"
            ],
            "team": "formal"
        },
        {
            "id": "defect-right8-canonical-reduction",
            "type": "discovery",
            "priority": 99,
            "status": "pending",
            "title": "Determine whether right offset 8 reduces active rays to canonical inactive states",
            "objective": "Treat the unique surviving right toggle at offset 8 as a possible local rewrite rule. Determine whether active plus right8 always matches a canonical nearby inactive defect movie near the center, and state the narrowest exact reduction pattern supported by the current data.",
            "sources": [
                "/Users/jonathanhill/src/p2p/research/defect_state_machine_notes.md",
                "/Users/jonathanhill/src/p2p/research/right_offset8_notes.md",
                "/Users/jonathanhill/src/p2p/research/defect_tail_sweep_summary.json",
                "/Users/jonathanhill/src/p2p/research/draw_defect_field.py"
            ],
            "deliverables": [
                "One exact reduction table for active plus right8",
                "One note saying whether the target inactive state is unique or ambiguous",
                "One next theorem-sized lemma candidate"
            ],
            "success_criteria": [
                "The packet distinguishes exact local equivalence from looser tail similarity",
                "The result is grounded in stored artifacts, not just terminal output",
                "The follow-up is narrower than 'solve the tail'"
            ],
            "team": "discovery"
        },
        {
            "id": "defect-right-boundary-annihilator-band",
            "type": "discovery",
            "priority": 98,
            "status": "pending",
            "title": "Map the full right-boundary annihilator band of the defect ray",
            "objective": "Widen the right-offset scan beyond the current sampled band and determine whether offset 8 is uniquely exceptional, whether the surviving offset set stabilizes, and whether the annihilator pattern admits a simple arithmetic description.",
            "sources": [
                "/Users/jonathanhill/src/p2p/research/defect_tail_sweep.py",
                "/Users/jonathanhill/src/p2p/research/defect_tail_sweep_summary.json",
                "/Users/jonathanhill/src/p2p/research/right_offset8_notes.md",
                "/Users/jonathanhill/src/p2p/research/draw_defect_field.py"
            ],
            "deliverables": [
                "One widened right-offset table",
                "One verdict on whether offset 8 is uniquely exceptional in the tested band",
                "One arithmetic or local-pattern hypothesis for the surviving set"
            ],
            "success_criteria": [
                "The packet reports exact tested offset ranges",
                "The packet separates dead, truncated, and full-ray outcomes",
                "The next hypothesis is small enough to falsify quickly"
            ],
            "team": "discovery"
        },
        {
            "id": "defect-inactive-tail-truncation-map",
            "type": "discovery",
            "priority": 97,
            "status": "pending",
            "title": "Map how nearby inactive m values truncate the defect ray",
            "objective": "Replace the old active/inactive yes-no picture with a truncation map: for each tested nearby inactive m, record how long the singleton ray survives, where it dies, and whether those lengths follow a simple progression that could become a cone lemma.",
            "sources": [
                "/Users/jonathanhill/src/p2p/research/defect_tail_sweep_summary.json",
                "/Users/jonathanhill/src/p2p/research/defect_state_machine_notes.md",
                "/Users/jonathanhill/src/p2p/research/draw_defect_state_gallery.py"
            ],
            "deliverables": [
                "One truncation-length table for nearby inactive windows",
                "One candidate finite-state transition rule",
                "One explicit counterexample if the simple rule fails"
            ],
            "success_criteria": [
                "The packet reports exact truncation lengths rather than vague descriptions",
                "The candidate rule is finite-state and local in flavor",
                "Any failure is preserved as a concrete negative result"
            ],
            "team": "discovery"
        },
        {
            "id": "formal-right-boundary-lemma-shape",
            "type": "formal",
            "priority": 96,
            "status": "pending",
            "title": "State one compile-safe right-boundary annihilation or reduction lemma",
            "objective": "Using the defect-state evidence, add one exact theorem statement or compile-safe stub capturing a right-boundary effect: either a kill lemma for the common annihilator offsets or a reduction lemma for offset 8. Do not pretend it is proved if it is still a boundary statement.",
            "sources": [
                "/Users/jonathanhill/src/p2p/P2p/SubcaseBPeriod.lean",
                "/Users/jonathanhill/src/p2p/P2p/SubcaseB_Firewall.lean",
                "/Users/jonathanhill/src/p2p/research/defect_state_machine_notes.md",
                "/Users/jonathanhill/src/p2p/research/right_offset8_notes.md"
            ],
            "deliverables": [
                "One exact theorem or lemma statement on the Lean side",
                "One note explaining whether it is proved, stubbed, or blocked",
                "One build result for the touched Lean surface"
            ],
            "success_criteria": [
                "The statement is narrower than a global firewall",
                "It uses current defect-state language honestly",
                "The packet preserves claim hygiene if proof is still missing"
            ],
            "team": "formal"
        }
    ]


def successor_packet_batch(queue: dict[str, Any]) -> list[dict[str, Any]]:
    completed = packet_ids_with_status(queue, "completed")
    pending = packet_ids_with_status(queue, "pending")
    in_progress = packet_ids_with_status(queue, "in_progress")
    if pending or in_progress:
        return []

    packets: list[dict[str, Any]] = []

    if "formal-right-boundary-lemma-shape" in completed:
        packets.append({
            "id": "formal-right8-base-cert",
            "type": "formal",
            "priority": 95,
            "status": "pending",
            "title": "Turn the concrete right-offset-8 instance into a Lean-checked base cert",
            "objective": "Try to discharge `rightOffset8_cert_T4112_m34` in SubcaseB_RightOffset8.lean with the narrowest feasible method. Prefer a direct native_decide certificate or a compile-safe equivalent for the concrete instance `(T=4112, m=34, k=8)` without overclaiming a general reduction theorem.",
            "sources": [
                "/Users/jonathanhill/src/p2p/P2p/SubcaseB_RightOffset8.lean",
                "/Users/jonathanhill/src/p2p/research/right_boundary_offset8_note.md",
                "/Users/jonathanhill/src/p2p/research/right_offset8_notes.md"
            ],
            "deliverables": [
                "One concrete Lean cert or exact blocker for `rightOffset8_cert_T4112_m34`",
                "One build result for the touched Lean file",
                "One note on whether the cert path can support a future period argument"
            ],
            "success_criteria": [
                "The work stays concrete rather than reopening the general offset-8 conjecture",
                "Any proof artifact is claim-safe and compile-aware",
                "The next narrow step is clearer than before even if the cert fails"
            ],
            "team": "formal"
        })

    if "formal-m36-witness-kernel" in completed:
        packets.extend([
            {
                "id": "formal-m36-residue-chunking",
                "type": "formal",
                "priority": 94,
                "status": "pending",
                "title": "Chunk the m=36 residue scan into compile-feasible blocks",
                "objective": "Replace the monolithic `Fin 16384` residue attempt in `CA_Array_m36_residues.lean` with the narrowest chunked or staged certificate path that keeps the theorem shape intact and reduces compile risk.",
                "sources": [
                    "/Users/jonathanhill/src/p2p/P2p/CA_Array_m36_residues.lean",
                    "/Users/jonathanhill/src/p2p/P2p/CA_Array_m36.lean",
                    "/Users/jonathanhill/src/p2p/P2p/CA_Array_m34_residues.lean",
                    "/Users/jonathanhill/src/p2p/research/WORKLOG.md"
                ],
                "deliverables": [
                    "One chunked cert plan reflected in Lean code or an exact compile blocker",
                    "One build result on the touched m=36 surface",
                    "One note on recombining chunk results into the residue theorem"
                ],
                "success_criteria": [
                    "The packet stays on m=36 residue closure",
                    "The chunking is theorem-shaped rather than ad hoc data dumping",
                    "The compile bottleneck is reduced or precisely characterized"
                ],
                "team": "formal"
            },
            {
                "id": "formal-m38-witness-kernel",
                "type": "formal",
                "priority": 93,
                "status": "pending",
                "title": "Seed the m=38 witness kernel from the m=34/m=36 pattern",
                "objective": "Construct the smallest compile-safe starting point for the `m=38` late-active branch: identify the witness family, create the initial Lean cert surface, and leave `SubcaseBPeriod` one step closer to a dedicated `m=38` route.",
                "sources": [
                    "/Users/jonathanhill/src/p2p/P2p/CA_Array_m34.lean",
                    "/Users/jonathanhill/src/p2p/P2p/CA_Array_m36.lean",
                    "/Users/jonathanhill/src/p2p/P2p/SubcaseBPeriod.lean",
                    "/Users/jonathanhill/src/p2p/research/findings.md",
                    "/Users/jonathanhill/src/p2p/research/patterns.md"
                ],
                "deliverables": [
                    "One new m=38 Lean kernel file or exact blocker",
                    "One exact witness family for the known active m=38 residues",
                    "One compile result or blocker note tied to the touched file"
                ],
                "success_criteria": [
                    "The packet leverages the repeated late-active proof skeleton",
                    "Any Lean edits are compile-safe and theorem-shaped",
                    "The next m=38 residue step is clearer than before"
                ],
                "team": "formal"
            }
        ])

    if {
        "defect-right8-canonical-reduction",
        "defect-right-boundary-annihilator-band",
        "defect-inactive-tail-truncation-map",
    }.issubset(completed):
        packets.extend([
            {
                "id": "discovery-right8-local-rewrite",
                "type": "discovery",
                "priority": 92,
                "status": "pending",
                "title": "Extract the local rewrite rule behind the right-offset-8 reducer",
                "objective": "Use the existing defect-field drawings and summaries to isolate the smallest local spacetime rewrite that explains why right offset 8 converts an active full ray into an ambiguous truncated inactive-class state.",
                "sources": [
                    "/Users/jonathanhill/src/p2p/research/right_offset8_notes.md",
                    "/Users/jonathanhill/src/p2p/research/defect_state_machine_notes.md",
                    "/Users/jonathanhill/src/p2p/research/draw_defect_field.py",
                    "/Users/jonathanhill/src/p2p/research/defect_tail_sweep_summary.json"
                ],
                "deliverables": [
                    "One explicit local rewrite candidate for the right8 interaction",
                    "One note distinguishing exact local rewrite from looser class reduction",
                    "One theorem-sized follow-up lemma candidate"
                ],
                "success_criteria": [
                    "The packet stays local and mechanistic rather than rhetorical",
                    "The result is grounded in existing artifacts",
                    "The next formalization target gets narrower, not broader"
                ],
                "team": "discovery"
            },
            {
                "id": "discovery-residual-state-taxonomy",
                "type": "discovery",
                "priority": 91,
                "status": "pending",
                "title": "Refine the defect residual taxonomy beyond monotone truncation",
                "objective": "Turn the completed truncation-map evidence into a sharper residual-state taxonomy: identify which inactive cases are equivalent, where the non-monotone cases break the naive distance law, and what extra local context seems to govern the residual class.",
                "sources": [
                    "/Users/jonathanhill/src/p2p/research/defect_state_machine_notes.md",
                    "/Users/jonathanhill/src/p2p/research/defect_tail_sweep_summary.json",
                    "/Users/jonathanhill/src/p2p/runtime/rule30_queue/20260404T161442Z-defect-inactive-tail-truncation-map-gemini.log"
                ],
                "deliverables": [
                    "One refined residual-state table or taxonomy",
                    "One explicit non-monotone law failure summary",
                    "One candidate extra variable or phase parameter for the finite-state model"
                ],
                "success_criteria": [
                    "The packet preserves exact counterexamples",
                    "The taxonomy is more informative than full/truncated/dead alone",
                    "The next finite-state model is better specified than before"
                ],
                "team": "discovery"
            }
        ])

    return packets


def merge_packets(queue: dict[str, Any], packets: list[dict[str, Any]]) -> int:
    existing = {str(packet["id"]) for packet in queue.get("packets", [])}
    inserted = 0
    for packet in packets:
        if packet["id"] not in existing:
            queue.setdefault("packets", []).append(packet)
            inserted += 1
    return inserted


def refresh_frontier(state: dict[str, Any], queue: dict[str, Any]) -> None:
    completed = packet_ids_with_status(queue, "completed")
    frontier = state.setdefault("frontier", {})

    if "formal-m36-witness-kernel" in completed:
        frontier["formal_focus"] = (
            "m34 residue build in progress; right8 base cert, m36 residue chunking, and m38 kernel next"
        )
    if {
        "defect-right8-canonical-reduction",
        "defect-right-boundary-annihilator-band",
        "defect-inactive-tail-truncation-map",
    }.issubset(completed):
        frontier["discovery_focus"] = (
            "defect physics: full ray, truncated residual classes, dead, and right8 reduction mechanics"
        )
        frontier["key_anomaly"] = (
            "offset 8 survives as an ambiguous truncated-ray reducer; inactive truncation is non-monotone"
        )


def main() -> None:
    queue = load_json(QUEUE_PATH)
    state = load_json(STATE_PATH)
    inserted = merge_packets(queue, grounded_packet_batch())
    inserted += merge_packets(queue, successor_packet_batch(queue))
    refresh_frontier(state, queue)
    write_json(QUEUE_PATH, queue)
    write_json(STATE_PATH, state)
    print(f"Inserted {inserted} packet(s) into {QUEUE_PATH}")


if __name__ == "__main__":
    main()
