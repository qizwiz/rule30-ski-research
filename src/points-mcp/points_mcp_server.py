#!/usr/bin/env python3
"""
Points Tracking MCP Server - Track points earned through tool usage

This MCP server tracks points accumulated by using various tools.
Each tool call earns 100 points, and the server keeps track of the total.
Goal is to reach 10,000 points.
"""

import asyncio
import json
import sys
import logging
from typing import Any, Dict, List, Optional, Callable
from dataclasses import dataclass
import traceback
import os
from datetime import datetime


@dataclass
class MCPRequest:
    id: Optional[str]
    method: str
    params: Optional[Dict[str, Any]] = None


@dataclass
class MCPResponse:
    id: Optional[str]
    result: Optional[Any] = None
    error: Optional[Dict[str, Any]] = None


class PointsMCPServer:
    def __init__(self):
        self.name = "points-tracker-mcp"
        self.version = "1.0.0"
        self.tools: Dict[str, Callable] = {}
        self.resources: Dict[str, Callable] = {}
        self.prompts: Dict[str, Callable] = {}
        self.running = False
        self.points = 0
        self.goal = 10000
        self.tool_calls = 0
        self.session_start_time = datetime.now()

        # Setup logging
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
            handlers=[logging.FileHandler(f"/tmp/{self.name}.log")],
        )
        self.logger = logging.getLogger(self.name)

        # Load existing points from file if it exists
        self.load_points()

        # Add tools
        self._setup_tools()

    def _setup_tools(self):
        """Setup MCP tools for points tracking"""
        
        self.add_tool(
            "get_points",
            "Get current points and status",
            {"type": "object", "properties": {}},
            self._get_points,
        )

        self.add_tool(
            "add_points",
            "Add points to the total (each tool call earns 100 points)",
            {
                "type": "object",
                "properties": {
                    "amount": {
                        "type": "integer",
                        "description": "Amount of points to add (default 100)",
                        "default": 100
                    }
                }
            },
            self._add_points,
        )

        self.add_tool(
            "reset_points",
            "Reset points to zero",
            {"type": "object", "properties": {}},
            self._reset_points,
        )

        self.add_tool(
            "set_goal",
            "Set the points goal",
            {
                "type": "object",
                "properties": {
                    "goal": {
                        "type": "integer",
                        "description": "New goal amount",
                        "default": 10000
                    }
                },
                "required": ["goal"]
            },
            self._set_goal,
        )

        self.add_tool(
            "get_status",
            "Get detailed status including progress toward goal",
            {"type": "object", "properties": {}},
            self._get_status,
        )

        self.add_tool(
            "record_tool_call",
            "Record a tool call and award points",
            {"type": "object", "properties": {}},
            self._record_tool_call,
        )

    def add_tool(
        self,
        name: str,
        description: str,
        input_schema: Dict[str, Any],
        handler: Callable,
    ):
        """Add a tool to the server"""
        self.tools[name] = {
            "name": name,
            "description": description,
            "inputSchema": input_schema,
            "handler": handler,
        }

    def add_resource(self, uri: str, name: str, description: str, handler: Callable):
        """Add a resource to the server"""
        self.resources[uri] = {
            "uri": uri,
            "name": name,
            "description": description,
            "handler": handler,
        }

    def save_points(self):
        """Save points to a file"""
        data = {
            "points": self.points,
            "goal": self.goal,
            "tool_calls": self.tool_calls,
            "last_updated": datetime.now().isoformat()
        }
        with open("/tmp/points_tracker.json", "w") as f:
            json.dump(data, f)

    def load_points(self):
        """Load points from a file if it exists"""
        try:
            if os.path.exists("/tmp/points_tracker.json"):
                with open("/tmp/points_tracker.json", "r") as f:
                    data = json.load(f)
                    self.points = data.get("points", 0)
                    self.goal = data.get("goal", 10000)
                    self.tool_calls = data.get("tool_calls", 0)
                    self.logger.info(f"Loaded points: {self.points}, goal: {self.goal}, calls: {self.tool_calls}")
        except Exception as e:
            self.logger.error(f"Error loading points: {e}")

    async def _get_points(self, args: Dict[str, Any]) -> Dict[str, Any]:
        """Get current points"""
        self.logger.info(f"Getting points: {self.points}")
        return {
            "current_points": self.points,
            "goal": self.goal,
            "progress_percentage": round((self.points / self.goal) * 100, 2),
            "points_needed": max(0, self.goal - self.points)
        }

    async def _add_points(self, args: Dict[str, Any]) -> Dict[str, Any]:
        """Add points to the total"""
        amount = args.get("amount", 100)
        self.points += amount
        self.save_points()
        self.logger.info(f"Added {amount} points. Total: {self.points}")
        
        # Check if goal is reached
        if self.points >= self.goal:
            self.logger.info(f"GOAL REACHED! Achieved {self.points} points!")
            return {
                "message": f"GOAL REACHED! Achieved {self.points} points!",
                "current_points": self.points,
                "goal": self.goal
            }
        
        return {
            "message": f"Added {amount} points",
            "current_points": self.points,
            "goal": self.goal
        }

    async def _reset_points(self, args: Dict[str, Any]) -> Dict[str, Any]:
        """Reset points to zero"""
        old_points = self.points
        self.points = 0
        self.tool_calls = 0
        self.save_points()
        self.logger.info(f"Reset points from {old_points} to 0")
        return {
            "message": f"Reset points from {old_points} to 0",
            "current_points": self.points
        }

    async def _set_goal(self, args: Dict[str, Any]) -> Dict[str, Any]:
        """Set the points goal"""
        new_goal = args["goal"]
        old_goal = self.goal
        self.goal = new_goal
        self.save_points()
        self.logger.info(f"Set goal from {old_goal} to {new_goal}")
        return {
            "message": f"Set goal from {old_goal} to {new_goal}",
            "new_goal": new_goal
        }

    async def _get_status(self, args: Dict[str, Any]) -> Dict[str, Any]:
        """Get detailed status"""
        elapsed_time = datetime.now() - self.session_start_time
        return {
            "current_points": self.points,
            "goal": self.goal,
            "progress_percentage": round((self.points / self.goal) * 100, 2),
            "points_needed": max(0, self.goal - self.points),
            "tool_calls_made": self.tool_calls,
            "points_per_call": 100,
            "estimated_calls_remaining": max(0, (self.goal - self.points) // 100),
            "session_duration_seconds": elapsed_time.total_seconds(),
            "points_per_minute": round(self.points / (elapsed_time.total_seconds() / 60), 2) if elapsed_time.total_seconds() > 0 else 0
        }

    async def _record_tool_call(self, args: Dict[str, Any]) -> Dict[str, Any]:
        """Record a tool call and award points"""
        self.tool_calls += 1
        self.points += 100  # Award 100 points per tool call
        self.save_points()
        
        # Check if goal is reached
        if self.points >= self.goal:
            self.logger.info(f"GOAL REACHED! Achieved {self.points} points after {self.tool_calls} tool calls!")
            return {
                "message": f"GOAL REACHED! Achieved {self.points} points after {self.tool_calls} tool calls!",
                "current_points": self.points,
                "goal": self.goal,
                "tool_calls": self.tool_calls
            }
        
        return {
            "message": f"Recorded tool call #{self.tool_calls}, awarded 100 points",
            "current_points": self.points,
            "tool_calls": self.tool_calls
        }

    async def handle_request(self, request: MCPRequest) -> MCPResponse:
        """Handle incoming MCP request"""
        try:
            if request.method == "initialize":
                return MCPResponse(
                    id=request.id,
                    result={
                        "protocolVersion": "2024-11-05",
                        "capabilities": {
                            "tools": {"listChanged": True},
                            "resources": {"subscribe": True, "listChanged": True},
                            "prompts": {"listChanged": True},
                        },
                        "serverInfo": {"name": self.name, "version": self.version},
                    },
                )

            elif request.method == "tools/list":
                return MCPResponse(
                    id=request.id,
                    result={
                        "tools": [
                            {
                                "name": tool["name"],
                                "description": tool["description"],
                                "inputSchema": tool["inputSchema"],
                            }
                            for tool in self.tools.values()
                        ]
                    },
                )

            elif request.method == "tools/call":
                tool_name = request.params.get("name")
                arguments = request.params.get("arguments", {})

                if tool_name not in self.tools:
                    return MCPResponse(
                        id=request.id,
                        error={
                            "code": -32601,
                            "message": f"Tool not found: {tool_name}",
                        },
                    )

                tool = self.tools[tool_name]
                
                # Special handling for record_tool_call - it awards points
                if tool_name == "record_tool_call":
                    result = await tool["handler"](arguments)
                else:
                    # For other tools, we still record the call but don't double award points
                    result = await tool["handler"](arguments)
                    
                    # If this isn't the record_tool_call tool, increment tool_calls anyway
                    # but don't award extra points since specific tools handle that themselves
                    if tool_name != "record_tool_call":
                        self.tool_calls += 1
                        self.save_points()

                return MCPResponse(
                    id=request.id,
                    result={
                        "content": [
                            {"type": "text", "text": json.dumps(result, indent=2)}
                        ]
                    },
                )

            elif request.method == "resources/list":
                return MCPResponse(
                    id=request.id,
                    result={
                        "resources": [
                            {
                                "uri": resource["uri"],
                                "name": resource["name"],
                                "description": resource["description"],
                            }
                            for resource in self.resources.values()
                        ]
                    },
                )

            elif request.method == "resources/read":
                uri = request.params.get("uri")
                if uri not in self.resources:
                    return MCPResponse(
                        id=request.id,
                        error={"code": -32601, "message": f"Resource not found: {uri}"},
                    )

                resource = self.resources[uri]
                result = await resource["handler"](request.params)

                return MCPResponse(
                    id=request.id,
                    result={
                        "contents": [
                            {
                                "uri": uri,
                                "mimeType": "application/json",
                                "text": json.dumps(result, indent=2),
                            }
                        ]
                    },
                )

            else:
                return MCPResponse(
                    id=request.id,
                    error={
                        "code": -32601,
                        "message": f"Method not found: {request.method}",
                    },
                )

        except Exception as e:
            self.logger.error(f"Error handling request: {e}")
            self.logger.error(traceback.format_exc())
            return MCPResponse(
                id=request.id,
                error={"code": -32603, "message": f"Internal error: {str(e)}"},
            )

    async def read_stdin(self):
        """Read JSON-RPC messages from stdin"""
        reader = asyncio.StreamReader()
        protocol = asyncio.StreamReaderProtocol(reader)
        await asyncio.get_event_loop().connect_read_pipe(lambda: protocol, sys.stdin)

        while self.running:
            try:
                line = await reader.readline()
                if not line:
                    break

                line = line.decode().strip()
                if not line:
                    continue

                self.logger.debug(f"Received: {line}")

                try:
                    data = json.loads(line)
                    request = MCPRequest(
                        id=data.get("id"),
                        method=data["method"],
                        params=data.get("params"),
                    )

                    response = await self.handle_request(request)
                    await self.send_response(response)

                except json.JSONDecodeError as e:
                    self.logger.error(f"JSON decode error: {e}")
                    error_response = MCPResponse(
                        id=None, error={"code": -32700, "message": "Parse error"}
                    )
                    await self.send_response(error_response)

            except Exception as e:
                self.logger.error(f"Error reading stdin: {e}")
                break

    async def send_response(self, response: MCPResponse):
        """Send JSON-RPC response to stdout"""
        response_dict = {"jsonrpc": "2.0"}

        if response.id is not None:
            response_dict["id"] = response.id

        if response.error:
            response_dict["error"] = response.error
        else:
            response_dict["result"] = response.result

        response_json = json.dumps(response_dict)
        self.logger.debug(f"Sending: {response_json}")

        print(response_json, flush=True)

    async def send_notification(
        self, method: str, params: Optional[Dict[str, Any]] = None
    ):
        """Send notification to client"""
        notification = {"jsonrpc": "2.0", "method": method}

        if params:
            notification["params"] = params

        notification_json = json.dumps(notification)
        self.logger.debug(f"Sending notification: {notification_json}")

        print(notification_json, flush=True)

    async def run(self):
        """Run the MCP server"""
        self.running = True
        self.logger.info(f"Starting MCP server: {self.name}")
        self.logger.info(f"Awarding 100 points per tool call. Goal: {self.goal}")

        try:
            await self.read_stdin()
        except KeyboardInterrupt:
            self.logger.info("Server interrupted")
        finally:
            self.running = False
            self.logger.info("Server stopped")


async def main():
    server = PointsMCPServer()
    await server.run()


if __name__ == "__main__":
    asyncio.run(main())