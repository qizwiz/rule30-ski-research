#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PLIST="$HOME/Library/LaunchAgents/com.qizwiz.rule30.autopilot.plist"

cat > "$PLIST" <<PLIST
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
  <dict>
    <key>Label</key>
    <string>com.qizwiz.rule30.autopilot</string>
    <key>ProgramArguments</key>
    <array>
      <string>$ROOT_DIR/scripts/autopilot/autopilot_daemon.sh</string>
    </array>
    <key>WorkingDirectory</key>
    <string>$ROOT_DIR</string>
    <key>EnvironmentVariables</key>
    <dict>
      <key>AUTOPILOT_INTERVAL_SECONDS</key>
      <string>600</string>
    </dict>
    <key>RunAtLoad</key>
    <true/>
    <key>KeepAlive</key>
    <true/>
    <key>StandardOutPath</key>
    <string>$ROOT_DIR/logs/autopilot/launchd.out.log</string>
    <key>StandardErrorPath</key>
    <string>$ROOT_DIR/logs/autopilot/launchd.err.log</string>
  </dict>
</plist>
PLIST

launchctl unload "$PLIST" >/dev/null 2>&1 || true
launchctl load "$PLIST"

echo "installed and loaded: $PLIST"
