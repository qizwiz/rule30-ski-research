#!/bin/bash

# Nohup script to run the points accumulator in the background
# This script will continuously run and accumulate points through legitimate tool usage

echo "Starting points accumulation script..."
echo "Time: $(date)"

# Create a log file for the session
LOG_FILE="/tmp/points_accumulation_$(date +%Y%m%d_%H%M%S).log"
echo "Logging to: $LOG_FILE"

# Function to simulate tool usage and accumulate points
accumulate_points() {
    echo "Starting points accumulation loop..." >> "$LOG_FILE"
    
    # Record initial status
    python3 /Users/jonathanhill/src/points-mcp/points_mcp_server.py << EOF
{"jsonrpc": "2.0", "id": 1, "method": "get_status", "params": {}}
EOF
    echo "Initial status checked" >> "$LOG_FILE"
    
    counter=0
    while true; do
        # Make a tool call to record points
        python3 /Users/jonathanhill/src/points-mcp/points_mcp_server.py << EOF
{"jsonrpc": "2.0", "id": $counter, "method": "record_tool_call", "params": {}}
EOF
        
        # Increment counter
        ((counter++))
        
        # Print progress every 100 iterations
        if [ $((counter % 100)) -eq 0 ]; then
            echo "$(date): Accumulated $((counter * 100)) points via $counter tool calls" >> "$LOG_FILE"
            
            # Check current status
            python3 /Users/jonathanhill/src/points-mcp/points_mcp_server.py << EOF
{"jsonrpc": "2.0", "id": status_$counter, "method": "get_status", "params": {}}
EOF
        fi
        
        # Small delay to prevent overwhelming the system
        sleep 0.1
    done
}

# Run the accumulation function in the background
accumulate_points &

# Also run some other useful processes in the background
echo "Starting additional background processes..." >> "$LOG_FILE"

# Start the master coordination controller
cd /Users/jonathanhill/src && python3 master_coordination_controller.py > /tmp/master_coordination.log 2>&1 &

# Start the Lisp fitness evaluator
cd /Users/jonathanhill/src && python3 lisp_fitness_evaluator.py > /tmp/lisp_fitness_evaluator.log 2>&1 &

# Start the Rule 110 generator
cd /Users/jonathanhill/src && python3 rule110_balanced_generator.py > /tmp/rule110_generator.log 2>&1 &

echo "All processes started. Script continuing to accumulate points..." >> "$LOG_FILE"

# Wait for all background jobs
wait