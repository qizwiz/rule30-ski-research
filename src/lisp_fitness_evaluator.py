#!/usr/bin/env python3
"""
Lisp Fitness Evaluator - Evaluates the quality of generated Lisp expressions
"""

import redis
import ast
import traceback
from typing import Dict, List, Tuple, Optional
import time
import re


class LispFitnessEvaluator:
    """Evaluates the fitness of generated Lisp expressions"""
    
    def __init__(self):
        self.redis_client = redis.Redis(decode_responses=True)
        
    def is_balanced_parens(self, expr: str) -> bool:
        """Check if parentheses are balanced"""
        depth = 0
        for char in expr:
            if char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
                if depth < 0:
                    return False
        return depth == 0
        
    def has_meaningful_content(self, expr: str) -> bool:
        """Check if expression has more than just parentheses and spaces"""
        # Remove parentheses and whitespace
        content = re.sub(r'[()]|\s', '', expr)
        return len(content) > 0
        
    def calculate_syntactic_complexity(self, expr: str) -> float:
        """Calculate complexity based on nesting depth and length"""
        max_depth = 0
        current_depth = 0
        for char in expr:
            if char == '(':
                current_depth += 1
                max_depth = max(max_depth, current_depth)
            elif char == ')':
                current_depth -= 1
        
        # Normalize by length to prevent favoring very long expressions
        length_factor = min(len(expr) / 10.0, 5.0)  # Cap at 5
        return max_depth * 0.5 + length_factor * 0.3
        
    def evaluate_fitness(self, expr: str) -> Dict[str, float]:
        """Evaluate the fitness of a Lisp expression"""
        fitness_scores = {
            'balanced': 0.0,
            'meaningful': 0.0,
            'complexity': 0.0,
            'total': 0.0
        }
        
        # Check if parentheses are balanced (crucial)
        if self.is_balanced_parens(expr):
            fitness_scores['balanced'] = 1.0
        else:
            # Even if not balanced, we might still want to partially evaluate
            fitness_scores['balanced'] = 0.0
            
        # Check if expression has meaningful content
        if self.has_meaningful_content(expr):
            fitness_scores['meaningful'] = 1.0
            
        # Calculate syntactic complexity
        fitness_scores['complexity'] = min(self.calculate_syntactic_complexity(expr), 10.0) / 10.0
        
        # Calculate total fitness (weighted sum)
        fitness_scores['total'] = (
            fitness_scores['balanced'] * 0.5 +
            fitness_scores['meaningful'] * 0.2 +
            fitness_scores['complexity'] * 0.3
        )
        
        return fitness_scores
        
    def process_candidates(self, batch_size: int = 10) -> int:
        """Process a batch of Lisp candidates from Redis queue"""
        processed = 0
        
        for _ in range(batch_size):
            # Get next candidate from queue
            candidate_data = self.redis_client.lpop('lisp-candidates-queue')
            
            if candidate_data is None:
                # Queue is empty
                break
                
            # Evaluate fitness
            fitness_scores = self.evaluate_fitness(candidate_data)
            
            # Store results in Redis with expiration (cleanup old entries)
            candidate_id = f"candidate:{time.time()}"
            self.redis_client.hset(candidate_id, mapping={
                'expression': candidate_data,
                'balanced_score': fitness_scores['balanced'],
                'meaningful_score': fitness_scores['meaningful'],
                'complexity_score': fitness_scores['complexity'],
                'total_score': fitness_scores['total'],
                'timestamp': time.time()
            })
            # Expire after 1 hour
            self.redis_client.expire(candidate_id, 3600)
            
            # Add to sorted set for ranking
            self.redis_client.zadd('lisp-candidates-ranked', {candidate_id: fitness_scores['total']})
            
            processed += 1
            
        return processed


def run_fitness_evaluation():
    """Main function to run the fitness evaluation continuously"""
    print("=== Lisp Fitness Evaluator Starting ===")
    
    evaluator = LispFitnessEvaluator()
    
    while True:
        processed_count = evaluator.process_candidates(batch_size=5)
        
        if processed_count > 0:
            print(f"Processed {processed_count} candidates")
            
            # Show top candidates periodically
            top_candidates = evaluator.redis_client.zrevrange('lisp-candidates-ranked', 0, 4, withscores=True)
            if top_candidates:
                print("Top 5 candidates:")
                for i, (cid, score) in enumerate(top_candidates):
                    expr = evaluator.redis_client.hget(cid, 'expression')
                    print(f"  {i+1}. Score: {score:.3f} | {expr[:60]}{'...' if len(expr) > 60 else ''}")
        else:
            # No candidates to process, sleep a bit
            time.sleep(0.5)


if __name__ == "__main__":
    run_fitness_evaluation()