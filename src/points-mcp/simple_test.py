#!/usr/bin/env python3
"""
Simple test script for the points tracking MCP server
"""
import sys
import os

def test_points_server():
    """Test the points server functionality"""
    print("Testing Points MCP Server...")
    
    # Add the server directory to the path
    sys.path.insert(0, '/Users/jonathanhill/src/points-mcp')
    
    # Import the server module directly
    try:
        import points_mcp_server
        
        # Create an instance to test initialization
        server_instance = points_mcp_server.PointsMCPServer()
        
        print(f"✓ Server initialized successfully")
        print(f"  Current points: {server_instance.points}")
        print(f"  Goal: {server_instance.goal}")
        print(f"  Tool calls: {server_instance.tool_calls}")
        
        # Test the get_status method
        import asyncio
        status = asyncio.run(server_instance._get_status({}))
        print(f"  Status: {status}")
        
        # Test adding points
        result = asyncio.run(server_instance._add_points({"amount": 100}))
        print(f"  After adding 100 points: {result}")
        
        # Test recording a tool call
        result = asyncio.run(server_instance._record_tool_call({}))
        print(f"  After recording tool call: {result}")
        
        # Save the updated points
        server_instance.save_points()
        print(f"  Points saved to file")
        
        print("\n✓ Server test completed successfully!")
        print(f"Final points: {server_instance.points}")
        print(f"Tool calls made: {server_instance.tool_calls}")
        
        # Check if goal has been reached
        if server_instance.points >= server_instance.goal:
            print(f"🎉 GOAL REACHED! You have {server_instance.points} points!")
        else:
            print(f"Progress: {server_instance.points}/{server_instance.goal} points ({(server_instance.points/server_instance.goal)*100:.1f}%)")
        
    except Exception as e:
        print(f"✗ Error testing server: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_points_server()