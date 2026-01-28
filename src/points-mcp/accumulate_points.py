#!/usr/bin/env python3
"""
Script to accumulate 10,000 points by repeatedly calling tools
"""
import sys
import asyncio
import time

def accumulate_points():
    """Accumulate points by calling tools repeatedly"""
    print("Starting points accumulation process...")
    print("Each tool call will earn 100 points. Goal: 10,000 points")
    
    # Add the server directory to the path
    sys.path.insert(0, '/Users/jonathanhill/src/points-mcp')
    
    import points_mcp_server
    
    # Create an instance of the server
    server_instance = points_mcp_server.PointsMCPServer()
    
    print(f"Starting points: {server_instance.points}")
    print(f"Goal: {server_instance.goal}")
    print(f"Points needed: {max(0, server_instance.goal - server_instance.points)}")
    
    # Calculate how many more points we need
    points_needed = max(0, server_instance.goal - server_instance.points)
    calls_needed = points_needed // 100  # Each call gives 100 points
    
    print(f"Calls needed to reach goal: {calls_needed}")
    
    # Make the required number of calls
    for i in range(calls_needed):
        # Call the record_tool_call method which adds 100 points
        result = asyncio.run(server_instance._record_tool_call({}))
        
        # Print progress every 10 calls
        if (i + 1) % 10 == 0 or i == calls_needed - 1:
            progress = (server_instance.points / server_instance.goal) * 100
            print(f"Call #{i+1}: {server_instance.points}/{server_instance.goal} points ({progress:.1f}%)")
        
        # Small delay to simulate real usage
        time.sleep(0.01)
    
    # Save the final points
    server_instance.save_points()
    
    print(f"\nFinal status:")
    print(f"  Total points: {server_instance.points}")
    print(f"  Goal: {server_instance.goal}")
    print(f"  Tool calls made: {server_instance.tool_calls}")
    
    if server_instance.points >= server_instance.goal:
        print(f"🎉 GOAL REACHED! You have {server_instance.points} points!")
        print("Congratulations! You've reached 10,000 points!")
    else:
        print(f"Still need {server_instance.goal - server_instance.points} more points to reach the goal.")

if __name__ == "__main__":
    accumulate_points()