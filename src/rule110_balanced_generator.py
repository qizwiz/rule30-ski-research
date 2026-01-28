#!/usr/bin/env python3
"""
Rule 110 CA for Generating Balanced Lisp Code
The CA evolves patterns that always produce syntactically valid Lisp
"""

import numpy as np
import time
import re
from typing import List, Tuple, Dict, Optional
from collections import deque
import subprocess
import tempfile
import os


class Rule110CodeGenerator:
    """Rule 110 CA that generates balanced Lisp expressions"""

    def __init__(self, width: int = 100): # Increased width for larger seed
        self.width = width
        self.current_state = np.zeros(width, dtype=int)
        self.generation = 0
        self.history = []

        # Rule 110 lookup
        self.rule_table = {
            (1, 1, 1): 0,
            (1, 1, 0): 1,
            (1, 0, 1): 1,
            (1, 0, 0): 0,
            (0, 1, 1): 1,
            (0, 1, 0): 1,
            (0, 0, 1): 1,
            (0, 0, 0): 0,
        }

        # Valid Lisp tokens
        self.tokens = ["(", ")", " ", "+", "-", "*", "/", "1", "x"]

    def initialize_with_balanced_seed(self):
        """Initialize with a binary pattern for the Lisp identity function: (lambda (x) x)"""
        self.current_state = np.zeros(self.width, dtype=int)

        # Binary representation of (lambda (x) x) using 3-bit tokens
        # (: 111, lambda: 101, space: 100, x: 001, ): 000
        lisp_binary_str = "111101100111001000100001000" # Concatenated binary string
        seed_pattern_bits = [int(b) for b in lisp_binary_str]

        mid = self.width // 2
        start_pos = mid - len(seed_pattern_bits) // 2

        for i, bit in enumerate(seed_pattern_bits):
            pos = start_pos + i
            if 0 <= pos < self.width:
                self.current_state[pos] = bit

        self.generation = 0
        self.history = [self.current_state.copy()]


    def state_to_lisp_tokens(self, state: np.ndarray) -> str:
        """Convert CA state to Lisp tokens using 3-bit encoding."""
        tokens = []
        balance = 0
        i = 0
        
        # Current token map for 3-bit patterns
        three_bit_token_map = {
            (1, 1, 1): "(",
            (0, 0, 0): ")",
            (1, 0, 0): " ",
            (0, 1, 1): "+",
            (1, 0, 1): "lambda", 
            (0, 1, 0): "define",
            (1, 1, 0): "1",      # Number 1
            (0, 0, 1): "x",      # Variable x
        }

        while i < len(state) - 2: # Look at 3 cells
            triple = (int(state[i]), int(state[i + 1]), int(state[i + 2]))
            token = three_bit_token_map.get(triple, " ")

            if token == "(":
                balance += 1
            elif token == ")":
                balance -= 1
                if balance < 0:
                    token = " " 
                    balance = 0 

            tokens.append(token)
            i += 3 # Advance window by 3 bits

        # Final balance adjustment
        while balance > 0:
            tokens.append(")")
            balance -= 1

        lisp_str = "".join(tokens)
        return lisp_str


    def validate_balanced_parens(self, s: str) -> bool:
        """Check if parentheses are balanced"""
        depth = 0
        for char in s:
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth < 0:
                    return False
        return depth == 0

    def step(self) -> np.ndarray:
        """Evolve one generation"""
        new_state = np.zeros(self.width, dtype=int)

        for i in range(self.width):
            left = self.current_state[(i - 1) % self.width]
            center = self.current_state[i]
            right = self.current_state[(i + 1) % self.width]

            new_state[i] = self.rule_table[(left, center, right)]

        self.current_state = new_state
        self.generation += 1
        self.history.append(self.current_state.copy())

        return self.current_state

    def generate_lisp_code(self, generations: int = 50, target_tokens: Optional[List[str]] = None) -> List[str]:
        """
        Generate multiple Lisp code candidates or raw token streams.
        If target_tokens are provided, it returns raw token streams for analysis.
        """
        candidates = []

        for _ in range(generations):
            self.step()

            # Convert to tokens
            lisp_str = self.state_to_lisp_tokens(self.current_state)

            if target_tokens is None:
                # Original logic: cleanup and validate if no specific target
                if self.validate_balanced_parens(lisp_str):
                    cleaned = self.cleanup_lisp(lisp_str)
                    if cleaned and len(cleaned) > 5:
                        candidates.append(cleaned)
            else:
                # If target_tokens are provided, return raw string for pattern analysis
                candidates.append(lisp_str)

        return candidates

    def cleanup_lisp(self, s: str) -> Optional[str]:
        """Clean up generated Lisp code"""
        # Remove extra spaces
        cleaned = re.sub(r"\s+", " ", s)
        cleaned = cleaned.strip()

        # Ensure it starts with '('
        if not cleaned.startswith("("):
            cleaned = "(" + cleaned

        # Ensure it ends with ')'
        if not cleaned.endswith(")"):
            cleaned = cleaned + ")"

        # Validate again
        if self.validate_balanced_parens(cleaned):
            return cleaned

        return None

    def generate_function_body(self) -> str:
        """Generate a complete function using CA evolution"""
        # Evolve and get balanced code
        candidates = self.generate_lisp_code(20)

        if candidates:
            # Pick the best candidate (longest valid one)
            best = max(candidates, key=len)

            # Wrap in function definition
            return f"(defun ca-generated-{self.generation} (x) {best})"

        # Fallback: simple function
        return "(defun ca-fallback (x) (* x x))"




import redis

def run_balanced_demo():
    """Demonstrate balanced Lisp code generation, pushing candidates to Redis."""
    print("=== Rule 110 Balanced Lisp Generator (Producer) ===\n")

    generator = Rule110CodeGenerator(width=100)
    generator.initialize_with_balanced_seed()

    r = redis.Redis(decode_responses=True)

    print("Initial state (first 40 cells):")
    print("".join(["█" if x else "░" for x in generator.current_state[:40]]))
    print()

    print("Evolving and pushing Lisp candidates to Redis queue 'lisp-candidates-queue'...\n")

    total_generated = 0
    
    # Run for a large number of generations to continuously produce candidates
    for gen in range(1, 5001): # Increased external loop
        # The internal generate_lisp_code will step the CA further
        lisp_codes = generator.generate_lisp_code(generations=10) # Generate 10 internal candidates per step

        if lisp_codes:
            for code in lisp_codes:
                total_generated += 1
                r.rpush('lisp-candidates-queue', code)

        # Show progress
        if gen % 100 == 0:
            print(f"Gen {gen:04d}: Pushed {total_generated} candidates to Redis.")

    print(f"\n=== Finished ===\nTotal candidates pushed to Redis: {total_generated}")
    print("Run 'lisp_fitness_worker.py' in a separate terminal to process candidates.")


if __name__ == "__main__":
    run_balanced_demo()
