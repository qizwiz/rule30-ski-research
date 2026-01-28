#!/bin/bash
# Example curl commands to interact with the points tracking server
# Note: The current implementation uses stdio, not HTTP, so this is illustrative
# of how an HTTP-based MCP server might work

echo "Example curl commands for an HTTP-based MCP server:"
echo ""
echo "# Get server status"
echo "curl -X POST http://localhost:8080/mcp \\"
echo "  -H \"Content-Type: application/json\" \\"
echo "  -d '{\"jsonrpc\": \"2.0\", \"id\": \"1\", \"method\": \"get_status\"}'"
echo ""
echo "# Call a tool to add points"
echo "curl -X POST http://localhost:8080/mcp \\"
echo "  -H \"Content-Type: application/json\" \\"
echo "  -d '{\"jsonrpc\": \"2.0\", \"id\": \"2\", \"method\": \"tools/call\", \"params\": {\"name\": \"add_points\", \"arguments\": {\"amount\": 100}}}'"
echo ""
echo "# List available tools"
echo "curl -X POST http://localhost:8080/mcp \\"
echo "  -H \"Content-Type: application/json\" \\"
echo "  -d '{\"jsonrpc\": \"2.0\", \"id\": \"3\", \"method\": \"tools/list\"}'"