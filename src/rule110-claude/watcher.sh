#!/bin/bash
# watcher.sh - Background watcher that updates status.txt every 30 seconds
# Usage: nohup ./watcher.sh &

cd /Users/jonathanhill/src/rule110-claude

echo "Watcher started at $(date)"
echo "Updating status.txt every 30 seconds..."
echo "Kill with: pkill -f watcher.sh"

while true; do
    ./status.sh > /dev/null 2>&1
    sleep 30
done
