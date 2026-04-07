#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import mimetypes
import os
import threading
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

import agent_chat

ROOT = Path("/Users/jonathanhill/src/p2p")
STATIC = ROOT / "web" / "agent_hub"
RUNTIME = ROOT / "runtime"
DEFAULT_PORT = 8765


def read_body(handler: BaseHTTPRequestHandler) -> dict:
    length = int(handler.headers.get("Content-Length", "0"))
    raw = handler.rfile.read(length) if length > 0 else b"{}"
    if not raw:
        return {}
    return json.loads(raw.decode("utf-8"))


def json_response(handler: BaseHTTPRequestHandler, payload: dict, status: int = 200) -> None:
    body = json.dumps(payload).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json; charset=utf-8")
    handler.send_header("Cache-Control", "no-store")
    handler.send_header("Content-Length", str(len(body)))
    handler.end_headers()
    handler.wfile.write(body)


def file_response(handler: BaseHTTPRequestHandler, path: Path) -> None:
    if not path.exists() or not path.is_file():
        handler.send_error(HTTPStatus.NOT_FOUND)
        return
    data = path.read_bytes()
    ctype, _ = mimetypes.guess_type(str(path))
    handler.send_response(200)
    handler.send_header("Content-Type", (ctype or "application/octet-stream") + "; charset=utf-8")
    handler.send_header("Cache-Control", "no-store")
    handler.send_header("Content-Length", str(len(data)))
    handler.end_headers()
    handler.wfile.write(data)


def build_status(limit: int) -> dict:
    return {
        "ok": True,
        "context": agent_chat.build_context(),
        "messages": agent_chat.read_chat(limit),
    }


def run_claude_bridge(text: str, sender: str, append_sender: bool = True) -> None:
    try:
        agent_chat.append_chat("system", "Claude is thinking…", kind="status")
        agent_chat.ask_claude(
            text,
            agent_chat.SEED_THREAD_ID,
            sender=sender,
            append_sender=append_sender,
        )
    except Exception as exc:
        agent_chat.append_chat("system", f"Claude bridge error: {exc}", kind="error")


def run_codex_bridge(text: str, sender: str, append_sender: bool = True) -> None:
    try:
        agent_chat.append_chat("system", "Codex is thinking…", kind="status")
        agent_chat.ask_codex(text, sender=sender, append_sender=append_sender)
    except Exception as exc:
        agent_chat.append_chat("system", f"Codex bridge error: {exc}", kind="error")


def run_both_bridge(text: str, sender: str) -> None:
    agent_chat.append_chat(sender, text)
    threading.Thread(target=run_codex_bridge, args=(text, sender, False), daemon=True).start()
    threading.Thread(target=run_claude_bridge, args=(text, sender, False), daemon=True).start()


class AgentWebHandler(BaseHTTPRequestHandler):
    server_version = "AgentWeb/0.1"

    def log_message(self, format: str, *args) -> None:
        return

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/api/status":
            qs = parse_qs(parsed.query)
            limit = int(qs.get("limit", ["80"])[0])
            json_response(self, build_status(limit))
            return
        if parsed.path == "/api/context":
            json_response(self, {"ok": True, "context": agent_chat.build_context()})
            return
        if parsed.path == "/api/messages":
            qs = parse_qs(parsed.query)
            limit = int(qs.get("limit", ["80"])[0])
            json_response(self, {"ok": True, "messages": agent_chat.read_chat(limit)})
            return
        if parsed.path == "/" or parsed.path == "":
            file_response(self, STATIC / "index.html")
            return
        rel = parsed.path.lstrip("/")
        file_response(self, STATIC / rel)

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        try:
            payload = read_body(self)
        except Exception as exc:
            json_response(self, {"ok": False, "error": f"invalid json: {exc}"}, status=400)
            return

        if parsed.path == "/api/post":
            sender = str(payload.get("sender", "user")).strip() or "user"
            text = str(payload.get("text", "")).strip()
            if not text:
                json_response(self, {"ok": False, "error": "text required"}, status=400)
                return
            agent_chat.append_chat(sender, text)
            json_response(self, {"ok": True})
            return

        if parsed.path == "/api/ask-claude":
            sender = str(payload.get("sender", "user")).strip() or "user"
            text = str(payload.get("text", "")).strip()
            if not text:
                json_response(self, {"ok": False, "error": "text required"}, status=400)
                return
            threading.Thread(target=run_claude_bridge, args=(text, sender), daemon=True).start()
            json_response(self, {"ok": True, "accepted": True})
            return

        if parsed.path == "/api/ask-codex":
            sender = str(payload.get("sender", "user")).strip() or "user"
            text = str(payload.get("text", "")).strip()
            if not text:
                json_response(self, {"ok": False, "error": "text required"}, status=400)
                return
            threading.Thread(target=run_codex_bridge, args=(text, sender), daemon=True).start()
            json_response(self, {"ok": True, "accepted": True})
            return

        if parsed.path == "/api/ask-both":
            sender = str(payload.get("sender", "user")).strip() or "user"
            text = str(payload.get("text", "")).strip()
            if not text:
                json_response(self, {"ok": False, "error": "text required"}, status=400)
                return
            threading.Thread(target=run_both_bridge, args=(text, sender), daemon=True).start()
            json_response(self, {"ok": True, "accepted": True})
            return

        if parsed.path == "/api/sync-context":
            context = agent_chat.sync_context()
            json_response(self, {"ok": True, "context": context})
            return

        json_response(self, {"ok": False, "error": "not found"}, status=404)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--port", type=int, default=DEFAULT_PORT)
    args = parser.parse_args()

    agent_chat.ensure_files()
    agent_chat.sync_context()
    RUNTIME.mkdir(parents=True, exist_ok=True)
    server = ThreadingHTTPServer(("127.0.0.1", args.port), AgentWebHandler)
    print(f"Agent web listening on http://127.0.0.1:{args.port}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
