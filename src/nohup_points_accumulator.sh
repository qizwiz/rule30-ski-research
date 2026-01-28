#!/bin/bash
#
# Nohup script to continuously run the points accumulator
# This script will run the points accumulation process in the background

# Create a timestamp for the log file
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
LOG_FILE="/tmp/points_accumulator_${TIMESTAMP}.log"

echo "Starting points accumulator script at $(date)" | tee "$LOG_FILE"

# Navigate to the points-mcp directory
cd /Users/jonathanhill/src/points-mcp || { echo "Failed to navigate to points-mcp directory"; exit 1; }

# Run the accumulate_points.py script
echo "Running accumulate_points.py..." | tee -a "$LOG_FILE"
python3 accumulate_points.py >> "$LOG_FILE" 2>&1 &

# Get the PID of the background process
ACCUMULATOR_PID=$!

echo "Points accumulator started with PID: $ACCUMULATOR_PID" | tee -a "$LOG_FILE"

# Also start the MCP server in the background if it's not already running
SERVER_LOG="/tmp/points_mcp_server_${TIMESTAMP}.log"
echo "Starting MCP server in background..." | tee -a "$LOG_FILE"

# Check if server is already running
if ! pgrep -f "points_mcp_server.py" > /dev/null; then
    python3 points_mcp_server.py > "$SERVER_LOG" 2>&1 &
    SERVER_PID=$!
    echo "MCP Server started with PID: $SERVER_PID" | tee -a "$LOG_FILE"
else
    echo "MCP Server appears to be already running" | tee -a "$LOG_FILE"
fi

# Function to handle script termination
cleanup() {
    echo "Stopping points accumulator script at $(date)" | tee -a "$LOG_FILE"
    if [ ! -z "$ACCUMULATOR_PID" ]; then
        kill $ACCUMULATOR_PID 2>/dev/null
    fi
    exit 0
}

# Set up signal traps for graceful shutdown
trap cleanup SIGTERM SIGINT

# Wait for the accumulator process to complete
wait $ACCUMULATOR_PID

echo "Points accumulator completed at $(date)" | tee -a "$LOG_FILE"

# Keep the script running for monitoring purposes
while true; do
    # Check if the goal has been reached
    CURRENT_POINTS=$(python3 -c "
import json
try:
    with open('/tmp/points_tracker.json', 'r') as f:
        data = json.load(f)
        print(data.get('points', 0))
except:
    print(0)
")
    
    if [ "$CURRENT_POINTS" -ge 10000 ]; then
        echo "Goal of 10,000 points reached! Current: $CURRENT_POINTS" | tee -a "$LOG_FILE"
        break
    fi
    
    sleep 60  # Check every minute
done

echo "Script completed at $(date)" | tee -a "$LOG_FILE"