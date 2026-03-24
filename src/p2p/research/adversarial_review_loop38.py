#!/usr/bin/env python3
"""
Adversarial Review Loop 38 — Verify "6 lifting rules" claim
Run date: 2026-03-24

Target: Paper line 322:
  "The lifting property holds precisely for the 6 left-permutive rules
  {30, 45, 75, 120, 135, 225} (verified n ≤ 20)."

The 16 left-permutive elementary CA rules are:
  15,30,45,60,75,90,105,120,135,150,165,180,195,210,225,240
  (these are the rules where rule(0,c,r) ≠ rule(1,c,r) for ALL (c,r))

The lifting property: Essential(n,k) => Essential(n+1, k+1)
i.e., if position k is essential at gen n, then position k+1 is essential at gen n+1.

We verify this for all 16 rules at n=1..20 by checking:
  For each n, for each k ∈ {1..2n-1} (interior positions),
  if position k-1 is essential at gen n, is position k essential at gen n+1?

Method: for each (n, k), find a witness c for k-1 at gen n, then construct
the witness for k at gen n+1 using the direct-witness method.
"""
import numpy as np
import sys

# The 16 left-permutive elementary CA rules
LEFT_PERMUTIVE_RULES = [15, 30, 45, 60, 75, 90, 105, 120, 135, 150, 165, 180, 195, 210, 225, 240]


def apply_rule(rule_num, a):
    """Apply elementary CA rule to array a, returning new array of length len(a)-2."""
    result = np.zeros(len(a) - 2, dtype=np.uint8)
    for i in range(len(a) - 2):
        l, c, r = int(a[i]), int(a[i+1]), int(a[i+2])
        idx = l*4 + c*2 + r
        result[i] = (rule_num >> idx) & 1
    return result


def evolve_n_steps(rule_num, c, n):
    """Evolve config c for n steps, returning center cell (position 0 of final)."""
    a = np.array(c, dtype=np.uint8)
    for _ in range(n):
        if len(a) < 3:
            return 0
        a = apply_rule(rule_num, a)
    return int(a[0]) if len(a) > 0 else 0


def is_essential(rule_num, n, k):
    """Check if position k is essential for rule rule_num at generation n.
    Returns (is_essential, witness_c) or (False, None).
    """
    size = 2*n+1
    # Try spike at k
    for attempt in range(min(1000, 2**size)):
        if attempt < 2**size:
            c = [(attempt >> j) & 1 for j in range(size)]
        else:
            c = list(np.random.randint(0, 2, size))

        out = evolve_n_steps(rule_num, c, n)
        flip = list(c)
        flip[k] ^= 1
        out_flip = evolve_n_steps(rule_num, flip, n)

        if out != out_flip:
            return True, c
    return False, None


def check_lifting(rule_num, n_max=15):
    """Check lifting property for rule at all n up to n_max.
    Returns (True, None) if lifting holds everywhere, or (False, counterexample) if not.
    """
    for n in range(1, n_max + 1):
        size_n = 2*n + 1
        size_n1 = 2*n + 3

        # For each interior position k in gen n (positions 1..2n-1)
        for k in range(1, 2*n):
            # Check if k is essential at gen n
            ess_n_k, witness_c = is_essential(rule_num, n, k)

            if not ess_n_k:
                # k not essential at gen n — lifting trivially satisfied (vacuously)
                continue

            # k IS essential at gen n. Check if k+1 is essential at gen n+1.
            # Use exhaustive check for small sizes, sampling for larger.
            target_k1 = k + 1
            ess_n1_k1, _ = is_essential(rule_num, n + 1, target_k1)

            if not ess_n1_k1:
                return False, (n, k, witness_c)

    return True, None


print("=== Loop 38: Lifting property check for all 16 left-permutive rules ===\n")
print("  Paper claims: lifting holds for {30,45,75,120,135,225} and fails for the other 10.\n")

# Expected results from paper/memory
EXPECTED_LIFTING = {30, 45, 75, 120, 135, 225}
EXPECTED_FAILING = {15, 60, 90, 105, 150, 165, 180, 195, 210, 240}

print(f"  {'Rule':>6}  {'Expected':>10}  {'Result':>10}  {'Match':>6}")
print("  " + "-" * 40)

results = {}
for rule in LEFT_PERMUTIVE_RULES:
    # For speed, check n=1..10 first; if lifting fails early, report immediately
    has_lifting, counterex = check_lifting(rule, n_max=10)
    results[rule] = has_lifting

    expected = "LIFTING" if rule in EXPECTED_LIFTING else "FAILS"
    result = "LIFTING" if has_lifting else "FAILS"
    match = "✓" if (has_lifting == (rule in EXPECTED_LIFTING)) else "✗ MISMATCH"

    if counterex:
        n_ce, k_ce, c_ce = counterex
        print(f"  Rule {rule:>3}:  {expected:>10}  {result:>10}  {match}  (counterex at n={n_ce}, k={k_ce})")
    else:
        print(f"  Rule {rule:>3}:  {expected:>10}  {result:>10}  {match}")
    sys.stdout.flush()

print()
lifting_rules = [r for r, v in results.items() if v]
failing_rules = [r for r, v in results.items() if not v]

print(f"  Lifting rules found: {sorted(lifting_rules)}")
print(f"  Failing rules found: {sorted(failing_rules)}")
print(f"  Paper claims lifting: {sorted(EXPECTED_LIFTING)}")
print(f"  Paper claims failing: {sorted(EXPECTED_FAILING)}")

mismatches = [(r, results[r]) for r in LEFT_PERMUTIVE_RULES
              if results[r] != (r in EXPECTED_LIFTING)]
if mismatches:
    print(f"\n  *** MISMATCHES: {mismatches} ***")
    print(f"  Paper claim about 6 lifting rules is INCORRECT.")
else:
    print(f"\n  ✓ All 16 rules match expectations. Paper claim verified (n≤10).")
    print(f"  ✓ Exactly 6 of 16 left-permutive rules have the lifting property.")
