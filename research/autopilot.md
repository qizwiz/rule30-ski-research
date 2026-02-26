# Autopilot Orchestrator (External Runner)

This repository includes an external loop that can keep work moving without active chat interaction.

## What it does
- Runs periodic cycles using `codex exec`.
- Uses a lockfile to avoid overlapping cycles.
- Uses a kill switch to stop safely.
- Appends cycle updates to `research/WORKLOG.md`.
- Stores logs in `logs/autopilot/`.

## Files
- `scripts/autopilot/autopilot_cycle.sh`
- `scripts/autopilot/autopilot_daemon.sh`
- `scripts/autopilot/install_launchd.sh`
- `scripts/autopilot/install_cron.sh`
- `research/AUTOPILOT_PROMPT.md`

## Safety controls
- Enable file: `.autopilot_enabled`
- Stop file: `.autopilot_stop`
- Lock file: `logs/autopilot/.cycle.lock`

## Start (manual)
```bash
touch .autopilot_enabled
rm -f .autopilot_stop
scripts/autopilot/autopilot_daemon.sh
```

## Start (launchd, macOS)
```bash
touch .autopilot_enabled
rm -f .autopilot_stop
scripts/autopilot/install_launchd.sh
```

## Start (cron)
```bash
touch .autopilot_enabled
rm -f .autopilot_stop
scripts/autopilot/install_cron.sh
```

## Stop
```bash
touch .autopilot_stop
```

For launchd stop:
```bash
launchctl unload "$HOME/Library/LaunchAgents/com.qizwiz.rule30.autopilot.plist"
```

## Notes
- This is an external orchestrator. It is not a built-in persistent Codex daemon.
- External authenticated actions (for example final arXiv submission) should remain manual.
