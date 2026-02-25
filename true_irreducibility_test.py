import sys

# We need a clean, naive environment to prove the difference between
# the "Blueprint" (Static Circuit) and the "Witness" (Dynamic Data).

# --- NAIVE AST EVALUATOR (No Hash Consing) ---
# We literally compute the math step-by-step.
def eval_chi_naive(p_val, q_val, r_val):
    # Chi: p XOR (NOT q AND r)
    not_q = not q_val
    and_val = not_q and r_val
    return p_val ^ and_val

def compute_naive_grid(rounds, initial_state):
    # To avoid edge-effect artifacts, we pad the grid
    # For R rounds, we need at least R padding on each side.
    pad = rounds + 2
    grid = [0]*pad + initial_state + [0]*pad
    
    total_evaluations = 0
    
    print(f"\n--- NAIVE DYNAMIC EVALUATION (The 'Witness') ---")
    print(f"Gen 0: {''.join(str(x) for x in grid)}")
    
    for r in range(1, rounds + 1):
        next_grid = [0] * len(grid)
        # We only compute the interior where we have valid parents
        for i in range(2, len(grid) - 2):
            p = grid[i-2]
            q = grid[i-1]
            r_val = grid[i]
            next_grid[i-1] = eval_chi_naive(p, q, r_val)
            total_evaluations += 1
        grid = next_grid
        print(f"Gen {r}: {''.join(str(x) for x in grid)}")
        
    print(f"\nTotal Naive Dynamic Evaluations: {total_evaluations}")

# 1. The Highly Symmetrical Case (Rule 30 Prize Style)
print("\n=== TEST 1: PERFECT SYMMETRY ===")
initial_symmetric = [1]
compute_naive_grid(5, initial_symmetric)

# 2. The Chaotic Cryptographic Case (Real SHA-3 Data)
print("\n=== TEST 2: HIGH ENTROPY (CHAOS) ===")
# A random string of bits
initial_chaotic = [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1]
compute_naive_grid(5, initial_chaotic)

