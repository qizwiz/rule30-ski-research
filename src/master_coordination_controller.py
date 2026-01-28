#!/usr/bin/env python3
"""
Master Coordination Controller - Advanced real-time coordination of all AI systems
Final controller that orchestrates the entire intelligent OS control ecosystem
"""

import subprocess
import time
import redis
import json
import threading
import queue
import asyncio
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional
import logging
import sys # Import sys for stderr

# Configure logging
log_file_path = "/Users/jonathanhill/.gemini/tmp/b1a17bb7110392600fd4169c0768f9efe6a968e0d3caaee31bc7d11d315121ac/master_coordination_controller.log"
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(log_file_path),
        logging.StreamHandler() # Also print to console for foreground runs
    ]
)

sys.stderr.write("SCRIPT: MasterCoordinationController started.\n")
sys.stderr.flush()

class MasterCoordinationController:
    """Master controller for all AI coordination systems"""
    
    def __init__(self):
        sys.stderr.write("CLASS: MasterCoordinationController __init__ started.\n")
        sys.stderr.flush()
        self.r = redis.Redis(host='localhost', port=6379, decode_responses=True)
        self.running = True
        self.coordination_queue = queue.Queue()
        self.system_status = {}
        self.performance_metrics = {}
        self.active_tasks = {}
        logging.info("MasterCoordinationController initializing...")
        try:
            sys.stderr.write("INIT: Calling setup_master_streams.\n")
            sys.stderr.flush()
            self.setup_master_streams()
            logging.info("Master streams set up.")
            sys.stderr.write("INIT: Calling initialize_subsystems.\n")
            sys.stderr.flush()
            self.initialize_subsystems()
            logging.info("Subsystems initialized.")
            sys.stderr.write("INIT: MasterCoordinationController __init__ finished successfully.\n")
            sys.stderr.flush()
        except Exception as e:
            logging.error(f"Error during MasterCoordinationController initialization: {e}", exc_info=True)
            sys.stderr.write(f"INIT ERROR: {e}\n")
            sys.stderr.flush()
            raise # Re-raise to ensure foreground failure is visible
    
    def setup_master_streams(self):
        """Initialize Redis streams for master coordination"""
        try:
            self.r.xgroup_create('master:coordination', 'controllers', '0', mkstream=True)
            self.r.xgroup_create('master:commands', 'executors', '0', mkstream=True)
            self.r.xgroup_create('master:status', 'monitors', '0', mkstream=True)
            self.r.xgroup_create('master:intelligence', 'orchestrators', '0', mkstream=True)
            logging.info("Redis consumer groups created successfully.")
        except Exception as e:
            logging.warning(f"Failed to create Redis consumer groups (might already exist): {e}")
    
    def initialize_subsystems(self):
        """Initialize tracking for all AI subsystems"""
        self.subsystems = {
            'real_os_controller': {
                'name': 'Real OS Controller',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 100
            },
            'semantic_ai_coordinator': {
                'name': 'Semantic AI Coordinator',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 95
            },
            'conversation_to_action_bridge': {
                'name': 'Conversation to Action Bridge',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 90
            },
            'multi_ai_coordination_system': {
                'name': 'Multi-AI Coordination System',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 85
            },
            'redis_data_dashboard': {
                'name': 'Redis Data Dashboard',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 70
            },
            'autonomous_performance_monitor': {
                'name': 'Autonomous Performance Monitor',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 80
            },
            'self_improving_ai_learning_loops': {
                'name': 'Self-Improving AI Learning Loops',
                'status': 'unknown',
                'last_heartbeat': "",
                'performance': 0.0,
                'tasks_completed': 0,
                'priority': 75
            }
        }
        
        # Store subsystem definitions
        for subsystem_id, config in self.subsystems.items():
            self.r.hset(f'master:subsystems:{subsystem_id}', mapping=config)
    
    def monitor_subsystem_health(self) -> Dict[str, Any]:
        """Monitor health of all AI subsystems"""
        health_report = {
            'timestamp': datetime.now().isoformat(),
            'subsystems_status': {},
            'overall_health': 'unknown',
            'active_subsystems': 0,
            'total_subsystems': len(self.subsystems)
        }
        
        active_count = 0
        
        for subsystem_id, config in self.subsystems.items():
            # Check if subsystem is producing output
            try:
                # Check for recent activity in relevant streams
                subsystem_active = False
                
                # Map subsystem to expected stream activity
                if subsystem_id == 'real_os_controller':
                    recent_activity = self.r.xrevrange('os:actions', count=1)
                elif subsystem_id == 'semantic_ai_coordinator':
                    recent_activity = self.r.xrevrange('ai:reasoning', count=1)
                elif subsystem_id == 'conversation_to_action_bridge':
                    recent_activity = self.r.xrevrange('conversation:actions', count=1)
                elif subsystem_id == 'multi_ai_coordination_system':
                    recent_activity = self.r.xrevrange('ai:coordination', count=1)
                elif subsystem_id == 'autonomous_performance_monitor':
                    recent_activity = self.r.xrevrange('performance:metrics', count=1)
                elif subsystem_id == 'self_improving_ai_learning_loops':
                    recent_activity = self.r.xrevrange('learning:improvements', count=1)
                else:
                    recent_activity = []
                
                # Check if activity is recent (within last 2 minutes)
                if recent_activity:
                    msg_id = recent_activity[0][0]
                    timestamp_ms = int(msg_id.split('-')[0])
                    activity_time = datetime.fromtimestamp(timestamp_ms / 1000)
                    time_diff = datetime.now() - activity_time
                    
                    if time_diff.total_seconds() < 120:  # 2 minutes
                        subsystem_active = True
                        active_count += 1
                
                status = 'active' if subsystem_active else 'inactive'
                health_report['subsystems_status'][subsystem_id] = {
                    'status': status,
                    'name': config['name'],
                    'priority': config['priority'],
                    'last_activity': activity_time.isoformat() if 'activity_time' in locals() else None
                }
                
            except Exception as e:
                health_report['subsystems_status'][subsystem_id] = {
                    'status': 'error',
                    'name': config['name'],
                    'error': str(e)
                }
        
        health_report['active_subsystems'] = active_count
        
        # Determine overall health
        if active_count >= 5:
            health_report['overall_health'] = 'excellent'
        elif active_count >= 3:
            health_report['overall_health'] = 'good'
        elif active_count >= 1:
            health_report['overall_health'] = 'degraded'
        else:
            health_report['overall_health'] = 'critical'
        
        return health_report
    
    def coordinate_intelligent_task_execution(self, high_level_task: Dict[str, Any]) -> Dict[str, Any]:
        """Coordinate execution of high-level intelligent tasks across all systems"""
        task_id = high_level_task.get('id', f'master_task_{int(time.time())}')
        task_type = high_level_task.get('type', 'general_intelligence')
        
        # Break down high-level task into subsystem-specific tasks
        subtasks = self.decompose_master_task(high_level_task)
        
        execution_plan = {
            'task_id': task_id,
            'task_type': task_type,
            'start_time': datetime.now().isoformat(),
            'subtasks': subtasks,
            'coordination_strategy': 'parallel_with_dependencies',
            'expected_duration': self.estimate_task_duration(subtasks)
        }
        
        # Execute subtasks in coordination
        results = []
        for subtask in subtasks:
            result = self.execute_coordinated_subtask(subtask)
            results.append(result)
            time.sleep(2)  # Brief coordination delay
        
        # Aggregate results
        final_result = self.aggregate_coordination_results(results)
        
        # Store coordination record
        coordination_record = {
            'execution_plan': execution_plan,
            'results': final_result,
            'completion_time': datetime.now().isoformat(),
            'success_rate': final_result.get('success_rate', 0.5)
        }
        
        self.r.xadd('master:coordination', coordination_record)
        
        return final_result
    
    def decompose_master_task(self, task: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Decompose high-level task into subsystem-specific subtasks"""
        task_type = task.get('type', 'general_intelligence')
        
        if task_type == 'intelligent_workspace_optimization':
            return [
                {
                    'subsystem': 'semantic_ai_coordinator',
                    'action': 'analyze_current_context',
                    'priority': 1,
                    'expected_output': 'context_analysis'
                },
                {
                    'subsystem': 'real_os_controller',
                    'action': 'optimize_window_layout',
                    'priority': 2,
                    'dependencies': ['context_analysis'],
                    'expected_output': 'layout_optimization'
                },
                {
                    'subsystem': 'conversation_to_action_bridge',
                    'action': 'process_optimization_requests',
                    'priority': 3,
                    'expected_output': 'action_execution'
                },
                {
                    'subsystem': 'autonomous_performance_monitor',
                    'action': 'validate_optimization_results',
                    'priority': 4,
                    'dependencies': ['layout_optimization', 'action_execution'],
                    'expected_output': 'performance_validation'
                }
            ]
        elif task_type == 'adaptive_learning_cycle':
            return [
                {
                    'subsystem': 'self_improving_ai_learning_loops',
                    'action': 'analyze_recent_performance',
                    'priority': 1,
                    'expected_output': 'learning_analysis'
                },
                {
                    'subsystem': 'multi_ai_coordination_system',
                    'action': 'optimize_agent_coordination',
                    'priority': 2,
                    'dependencies': ['learning_analysis'],
                    'expected_output': 'coordination_optimization'
                },
                {
                    'subsystem': 'autonomous_performance_monitor',
                    'action': 'implement_learned_optimizations',
                    'priority': 3,
                    'dependencies': ['coordination_optimization'],
                    'expected_output': 'optimization_implementation'
                }
            ]
        else:
            # Default task decomposition
            return [
                {
                    'subsystem': 'semantic_ai_coordinator',
                    'action': 'analyze_task_requirements',
                    'priority': 1,
                    'expected_output': 'task_analysis'
                },
                {
                    'subsystem': 'multi_ai_coordination_system',
                    'action': 'coordinate_task_execution',
                    'priority': 2,
                    'dependencies': ['task_analysis'],
                    'expected_output': 'coordinated_execution'
                }
            ]
    
    def execute_coordinated_subtask(self, subtask: Dict[str, Any]) -> Dict[str, Any]:
        """Execute a subtask with coordination"""
        subsystem = subtask.get('subsystem', 'unknown')
        action = subtask.get('action', 'unknown')
        
        # Send coordination command
        command = {
            'timestamp': datetime.now().isoformat(),
            'target_subsystem': subsystem,
            'action': action,
            'priority': subtask.get('priority', 5),
            'coordination_id': subtask.get('coordination_id', 'master'),
            'expected_output': subtask.get('expected_output', 'unknown')
        }
        
        self.r.xadd('master:commands', command)
        
        # Simulate coordinated execution (in production, wait for actual subsystem response)
        execution_result = {
            'subsystem': subsystem,
            'action': action,
            'status': 'executed',
            'confidence': 0.85 + (random.uniform(0, 0.15) if 'random' in globals() else 0.1),
            'execution_time': random.uniform(1, 5) if 'random' in globals() else 2.5,
            'output': f'Coordinated {action} completed successfully'
        }
        
        return execution_result
    
    def aggregate_coordination_results(self, results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Aggregate results from coordinated subtask execution"""
        if not results:
            return {'success_rate': 0.0, 'overall_status': 'failed'}
        
        successful_tasks = len([r for r in results if r.get('status') == 'executed'])
        total_tasks = len(results)
        success_rate = successful_tasks / total_tasks
        
        avg_confidence = sum(r.get('confidence', 0.5) for r in results) / total_tasks
        total_execution_time = sum(r.get('execution_time', 0) for r in results)
        
        overall_status = 'excellent' if success_rate >= 0.9 else \
                        'good' if success_rate >= 0.7 else \
                        'acceptable' if success_rate >= 0.5 else 'poor'
        
        return {
            'success_rate': success_rate,
            'overall_status': overall_status,
            'avg_confidence': avg_confidence,
            'total_execution_time': total_execution_time,
            'successful_tasks': successful_tasks,
            'total_tasks': total_tasks,
            'subsystem_results': results
        }
    
    def estimate_task_duration(self, subtasks: List[Dict[str, Any]]) -> float:
        """Estimate total duration for coordinated task execution"""
        # Simple estimation based on subtask count and complexity
        base_duration = len(subtasks) * 3.0  # 3 seconds per subtask
        complexity_factor = 1.0
        
        # Adjust for dependencies
        has_dependencies = any('dependencies' in task for task in subtasks)
        if has_dependencies:
            complexity_factor += 0.5
        
        return base_duration * complexity_factor
    
    def intelligent_system_orchestration(self):
        """Main intelligent system orchestration loop"""
        sys.stderr.write("METHOD: intelligent_system_orchestration started.\n")
        sys.stderr.flush()
        cycle = 0
        orchestration_tasks = [
            {'type': 'intelligent_workspace_optimization', 'description': 'Optimize entire workspace intelligently'},
            {'type': 'adaptive_learning_cycle', 'description': 'Execute adaptive learning across all systems'},
            {'type': 'performance_coordination', 'description': 'Coordinate performance optimization'},
            {'type': 'predictive_task_execution', 'description': 'Execute predictive task coordination'}
        ]
        
        while self.running:
            try:
                cycle += 1
                logging.info(f"Orchestration cycle {cycle} started.")
                sys.stderr.write(f"ORCHESTRATION: Cycle {cycle} - monitoring health.\n")
                sys.stderr.flush()
                
                # Monitor subsystem health
                health_report = self.monitor_subsystem_health()
                
                # Store health report
                logging.info(f"Attempting to add health report to master:status: {health_report}")
                self.r.xadd('master:status', {'report': json.dumps(health_report)})
                logging.info("Successfully added health report to master:status")
                # Log system status every 10 cycles
                if cycle % 10 == 0:
                    active_systems = health_report['active_subsystems']
                    total_systems = health_report['total_subsystems']
                    overall_health = health_report['overall_health']

                    logging.info(f"🌟 System Health #{cycle}: {active_systems}/{total_systems} active - {overall_health}")

                
                # Store intelligence metrics
                intelligence_metrics = {
                    'cycle': cycle,
                    'timestamp': datetime.now().isoformat(),
                    'coordination_effectiveness': self.calculate_coordination_effectiveness(),
                    'system_intelligence': self.calculate_system_intelligence(),
                    'adaptive_capability': self.calculate_adaptive_capability()
                }
                
                self.r.xadd('master:intelligence', intelligence_metrics)
                logging.info(f"Intelligence metrics added to master:intelligence for cycle {cycle}.")
                
                time.sleep(30)  # 30 second master coordination cycles
                
            except Exception as e:
                logging.error(f"Master coordination error in orchestration loop: {e}", exc_info=True)
                time.sleep(60)
    
    def calculate_coordination_effectiveness(self) -> float:
        """Calculate overall coordination effectiveness"""
        try:
            # Get recent coordination results
            recent_coords = self.r.xrevrange('master:coordination', count=10)
            
            if not recent_coords:
                return 0.5
            
            success_rates = []
            for msg_id, fields in recent_coords:
                result = json.loads(fields.get('results', '{}'))
                success_rates.append(result.get('success_rate', 0.5))
            
            return sum(success_rates) / len(success_rates)
            
        except:
            return 0.5
    
    def calculate_system_intelligence(self) -> float:
        """Calculate overall system intelligence metric"""
        try:
            # Aggregate intelligence from multiple sources
            ai_performance = 0.5
            learning_effectiveness = 0.5
            adaptation_capability = 0.5
            
            # Get AI coordination performance
            ai_coords = self.r.xrevrange('ai:coordination', count=5)
            if ai_coords:
                confidences = [float(fields.get('final_confidence', 0.5)) for msg_id, fields in ai_coords]
                ai_performance = sum(confidences) / len(confidences)
            
            # Get learning performance
            learning_results = self.r.xrevrange('learning:improvements', count=5)
            if learning_results:
                improvements = [float(fields.get('improvement_value', 0.01)) for msg_id, fields in learning_results]
                learning_effectiveness = min(1.0, sum(improvements) * 10)  # Scale improvements
            
            # Get adaptation performance
            adaptations = self.r.xrevrange('performance:optimizations', count=5)
            if adaptations:
                adaptation_capability = 0.8  # High if adaptations are happening
            
            return (ai_performance + learning_effectiveness + adaptation_capability) / 3.0
            
        except:
            return 0.5
    
    def calculate_adaptive_capability(self) -> float:
        """Calculate system's adaptive capability"""
        try:
            # Check for recent adaptations and optimizations
            recent_adaptations = self.r.xrevrange('performance:optimizations', count=10)
            recent_learning = self.r.xrevrange('learning:improvements', count=10)
            
            adaptation_score = 0.5
            
            # Score based on recent adaptations
            if len(recent_adaptations) > 5:
                adaptation_score += 0.2
            
            if len(recent_learning) > 5:
                adaptation_score += 0.3
            
            # Check for successful optimizations
            successful_optimizations = 0
            for msg_id, fields in recent_adaptations:
                if fields.get('status') == 'applied':
                    successful_optimizations += 1
            
            if successful_optimizations > 3:
                adaptation_score += 0.2
            
            return min(1.0, adaptation_score)
            
        except:
            return 0.5
    
    def start_master_coordination(self):
        """Start the master coordination controller"""
        sys.stderr.write("METHOD: start_master_coordination called.\n")
        sys.stderr.flush()
        print("🎯 Starting Master Coordination Controller")
        print(f"Managing {len(self.subsystems)} AI subsystems:")
        
        for subsystem_id, config in self.subsystems.items():
            print(f"  - {config['name']} (Priority: {config['priority']})")
        
        # Start orchestration loop
        sys.stderr.write("METHOD: Creating orchestration_thread.\n")
        sys.stderr.flush()
        orchestration_thread = threading.Thread(target=self.intelligent_system_orchestration)
        orchestration_thread.daemon = True
        sys.stderr.write("METHOD: Starting orchestration_thread.\n")
        sys.stderr.flush()
        orchestration_thread.start()
        
        try:
            sys.stderr.write("METHOD: Entering main thread sleep loop.\n")
            sys.stderr.flush()
            while self.running:
                time.sleep(1)
        except KeyboardInterrupt:
            print("\n🛑 Stopping Master Coordination Controller")
            self.running = False
        sys.stderr.write("METHOD: Exiting start_master_coordination.\n")
        sys.stderr.flush()

if __name__ == "__main__":
    import random  # For simulation
    master = MasterCoordinationController()
    master.start_master_coordination()