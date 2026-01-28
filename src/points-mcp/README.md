# Points Tracking MCP Server

This MCP server tracks points earned through tool usage. The goal is to reach 10,000 points by using various tools.

## Features

- Tracks points earned through tool usage (100 points per tool call)
- Persistent storage of points between sessions
- Goal tracking (default: 10,000 points)
- Status reporting with progress percentage
- Tool call counting

## Available Tools

- `get_points`: Get current points and status
- `add_points`: Add points to the total (default: 100 points)
- `reset_points`: Reset points to zero
- `set_goal`: Set the points goal
- `get_status`: Get detailed status including progress toward goal
- `record_tool_call`: Record a tool call and award 100 points

## Usage

1. Start the server:
   ```bash
   python3 points_mcp_server.py
   ```

2. Connect via Qwen Code:
   ```bash
   qwen mcp add points-tracker python3 /Users/jonathanhill/src/points-mcp/points_mcp_server.py
   ```

3. Use the tools to earn points toward your goal of 10,000!

## Progress

- Current points: [Will be updated as tools are used]
- Goal: 10,000 points
- Progress: [Will be updated as tools are used]