#!/usr/bin/env python3
"""
mcp-shadow — MCP Server for Rule 30 shadow region analysis.

Tools:
  shadow_query     — query shadow status at (n, j)
  shadow_scan      — scan all shadows at level n
  spike_test       — test if spike@x witnesses Essential(n+1, j)
  rule30_evolve    — ASCII triangle of Rule 30 evolution
  coverage_check   — verify {rightmost, x=1, x=6} cover all shadows
  dchain_query     — raw dChain(t, k) value
"""

import asyncio
import json
import sys
from pathlib import Path
from typing import List

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "research"))

import shadow_api

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import Tool, TextContent, CallToolResult

server = Server("shadow")


def _text_result(text: str) -> CallToolResult:
    return CallToolResult(content=[TextContent(type="text", text=text)])


def _json_result(data) -> CallToolResult:
    return _text_result(json.dumps(data))


@server.list_tools()
async def list_tools() -> List[Tool]:
    return [
        Tool(
            name="shadow_query",
            description="Query shadow status at (n, j). Returns dChain values and witnesses if shadow.",
            inputSchema={
                "type": "object",
                "properties": {
                    "n": {"type": "integer", "description": "Level n"},
                    "j": {"type": "integer", "description": "Position j"},
                },
                "required": ["n", "j"],
            },
        ),
        Tool(
            name="shadow_scan",
            description="Scan all shadows at level n. Returns list of shadow positions with witnesses.",
            inputSchema={
                "type": "object",
                "properties": {
                    "n": {"type": "integer", "description": "Level n"},
                },
                "required": ["n"],
            },
        ),
        Tool(
            name="spike_test",
            description="Test if spike@x witnesses Essential(n+1, j). Returns witness status and function values.",
            inputSchema={
                "type": "object",
                "properties": {
                    "n": {"type": "integer", "description": "Level n"},
                    "j": {"type": "integer", "description": "Position j"},
                    "x": {"type": "integer", "description": "Spike position x"},
                },
                "required": ["n", "j", "x"],
            },
        ),
        Tool(
            name="rule30_evolve",
            description="ASCII triangle of Rule 30 evolution from spike at position x for n steps.",
            inputSchema={
                "type": "object",
                "properties": {
                    "n": {"type": "integer", "description": "Number of evolution steps"},
                    "x": {"type": "integer", "description": "Spike position x"},
                },
                "required": ["n", "x"],
            },
        ),
        Tool(
            name="coverage_check",
            description="Verify that {rightmost, x=1, x=6} cover all shadows for n in 0..n_max.",
            inputSchema={
                "type": "object",
                "properties": {
                    "n_max": {"type": "integer", "description": "Maximum level to check"},
                },
                "required": ["n_max"],
            },
        ),
        Tool(
            name="dchain_query",
            description="Raw dChain(t, k) value from the diagonal recurrence.",
            inputSchema={
                "type": "object",
                "properties": {
                    "t": {"type": "integer", "description": "Time step t"},
                    "k": {"type": "integer", "description": "Position k"},
                },
                "required": ["t", "k"],
            },
        ),
    ]


@server.call_tool()
async def call_tool(name: str, arguments: dict) -> CallToolResult:
    try:
        if name == "shadow_query":
            return _json_result(shadow_api.query_shadow(arguments["n"], arguments["j"]))

        elif name == "shadow_scan":
            return _json_result(shadow_api.scan_shadows(arguments["n"]))

        elif name == "spike_test":
            return _json_result(shadow_api.test_spike(arguments["n"], arguments["j"], arguments["x"]))

        elif name == "rule30_evolve":
            return _text_result(shadow_api.evolve_ascii(arguments["n"], arguments["x"]))

        elif name == "coverage_check":
            return _json_result(shadow_api.verify_coverage(arguments["n_max"]))

        elif name == "dchain_query":
            value = shadow_api.dchain_value(arguments["t"], arguments["k"])
            return _json_result({"t": arguments["t"], "k": arguments["k"], "value": value})

        else:
            return _text_result(f"Unknown tool: {name}")

    except Exception as e:
        return _text_result(f"Error in {name}: {e}")


async def main():
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())


if __name__ == "__main__":
    asyncio.run(main())
