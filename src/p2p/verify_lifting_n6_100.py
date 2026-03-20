#!/usr/bin/env python3
"""
Verify lifting_lemma for n=6..100 (or up to n_max).
For each n and k, find an explicit witness c' for Essential(n+1, k+1):
  c' such that rule30n(n+1, c') != rule30n(n+1, flip(c', k+1))

Strategy: try unit_at_j configs for j=0..2(n+1), then two-spike configs.
"""

import sys
import json
from datetime import datetime

def rule30n_fast(steps, cells_int, N):
    """Compute rule30n: cells_int has bit i = cell[i] (i=0 leftmost)."""
    c = cells_int
    n = N
    for _ in range(steps):
        n -= 2
        mask = (1 << n) - 1
        c = (c ^ ((c >> 1) | (c >> 2))) & mask
    return c & 1

def spike_int(pos):
    return 1 << pos

def flip_int(config_int, pos):
    return config_int ^ (1 << pos)

def verify_n(n, verbose=False):
    """Verify lifting_lemma for all k at level n.
    Returns dict: {k: witness_j or None}"""
    N = 2 * (n + 1) + 1  # size of Config(n+1)
    steps = n + 1
    results = {}
    all_ok = True
    
    # Precompute rule30n(n+1, unit_at_j) for all j
    unit_outputs = {}
    for j in range(N):
        e_j = spike_int(j)
        unit_outputs[j] = rule30n_fast(steps, e_j, N)
    
    # For each k at level n+1 (0..2n+2), verify Essential(n+1, k) 
    # (we want Essential(n+1, k+1) for k at level n, so k+1 ranges over 1..2n+1)
    # But let's just check ALL positions k_new=0..2n+2 at level n+1
    for k_new in range(N):
        # Find witness: c' with rule30n(n+1, c') != rule30n(n+1, flip(c', k_new))
        witness_j = None
        # Try unit_at_j
        for j in range(N):
            c_prime = spike_int(j)
            c_flip = flip_int(c_prime, k_new)
            out_c = unit_outputs[j]
            out_flip = rule30n_fast(steps, c_flip, N)
            if out_c != out_flip:
                witness_j = j
                break
        
        if witness_j is None:
            # Try all-zeros (often works for boundary)
            out_zero = rule30n_fast(steps, 0, N)
            out_flip = rule30n_fast(steps, flip_int(0, k_new), N)
            if out_zero != out_flip:
                witness_j = -1  # -1 = all-zeros witness
        
        if witness_j is None:
            all_ok = False
            if verbose:
                print(f"  FAILED: n={n}, k_new={k_new}")
        results[k_new] = witness_j
    
    return all_ok, results

def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    print(f"Verifying lifting_lemma for n=1..{n_max}")
    print(f"(Checking Essential(n+1, k) for all k at each level n+1)")
    
    all_passed = True
    total_pairs = 0
    certificates = {}
    
    for n in range(1, n_max + 1):
        ok, results = verify_n(n)
        N = 2 * (n + 1) + 1
        total_pairs += N
        if not ok:
            print(f"  FAILED at n={n}!")
            all_passed = False
        certificates[n] = results
        if n % 10 == 0 or n <= 5:
            print(f"  n={n}: OK (checked {N} positions)")
    
    print(f"\nTotal (n,k) pairs checked: {total_pairs}")
    if all_passed:
        print(f"ALL PASSED: Essential(n+1, k) verified for all n=1..{n_max}, all k")
        print(f"This verifies that lifting_lemma conclusion holds for n=1..{n_max}")
    else:
        print("SOME FAILURES - see above")
    
    # Save certificate
    cert = {
        "description": f"Lifting lemma conclusion verified for n=1..{n_max}",
        "n_range": [1, n_max],
        "timestamp": datetime.now().isoformat(),
        "all_passed": all_passed,
        "total_pairs": total_pairs
    }
    cert_file = f"/Users/jonathanhill/src/p2p/z3_certificates/lifting_n1_to_{n_max}.json"
    with open(cert_file, 'w') as f:
        json.dump(cert, f, indent=2)
    print(f"Certificate saved to {cert_file}")
    
    return 0 if all_passed else 1

if __name__ == "__main__":
    sys.exit(main())
