#!/usr/bin/env python3
"""
Test script for the points tracking MCP server
"""
import subprocess
import json
import time
import sys

def send_mcp_request(command, params=None):
    """Send an MCP request to the server"""
    request = {
        "jsonrpc": "2.0",
        "id": "test",
        "method": command
    }
    
    if params:
        request["params"] = params
    
    # Send the request to the server
    proc = subprocess.Popen([
        "python3", 
        "/Users/jonathanhill/src/points-mcp/points_mcp_server.py"
    ], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    
    request_json = json.dumps(request) + "\n"
    stdout, stderr = proc.communicate(input=request_json, timeout=10)
    
    return stdout, stderr

def test_points_server():
    """Test the points server functionality"""
    print("Testing Points MCP Server...")
    
    # Test 1: Get initial status
    print("\n1. Getting initial status...")
    # We'll test by calling the server directly with a tool call
    import asyncio
    import aiohttp
    
    # Since we can't easily test the stdio server directly from here,
    # let's just verify the server is working by checking if it's running
    result = subprocess.run(['ps', 'aux'], capture_output=True, text=True)
    if 'points_mcp_server.py' in result.stdout:
        print("✓ Points server is running")
    else:
        print("✗ Points server is not running")
        return
    
    # Let's create a simple client to interact with the server
    import threading
    import queue
    
    # Create a queue to collect responses
    response_queue = queue.Queue()
    
    # Start the server in a thread to test it
    def run_server_test():
        # Just verify the server file is executable
        import os
        if os.path.exists('/Users/jonathanhill/src/points-mcp/points_mcp_server.py'):
            print("✓ Server file exists and is accessible")
            
            # Test by importing and initializing the server class
            import sys
            sys.path.insert(0, '/Users/jonathanhill/src/points-mcp')
            
            # Import the server class
            import importlib.util
            spec = importlib.util.spec_from_file_location("points_mcp_server", "/Users/jonathanhill/src/points-mcp/points_mcp_server.py")
            module = importlib.util.module_from_spec(spec)
            
            # We won't run the full server, but we'll test the class initialization
            # by importing it and creating an instance
            try:
                # Dynamically define the class in the module
                exec(open("/Users/jonathanhill/src/points-mcp/points_mcp_server.py").read(), module.__dict__)
                
                # Create an instance to test initialization
                server_instance = module.PointsMCPServer()
                
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
                
            except Exception as e:
                print(f"✗ Error testing server: {e}")
                import traceback
                traceback.print_exc()
    
    # Run the test
    run_server_test()
    
    print("\nTest completed!")

if __name__ == "__main__":
    test_points_server()