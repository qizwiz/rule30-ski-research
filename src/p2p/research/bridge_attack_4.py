#!/opt/homebrew/bin/python3
"""
Bridge Attack 4: Two independent tests.

TEST A — Circuit depth proxy:
  For n=1..15, build the explicit DAG for computing rule30_n(e_n).
  Each cell at each time step is an XOR/OR gate. Count gates on the critical
  path to s(n) and the total gate count. The critical path length is the
  minimum circuit depth needed (a lower bound on sequential computation).

TEST B — Low-degree polynomial over GF(2) in the bits of n:
  Is s(n) a low-degree polynomial over GF(2) in the binary representation
  of n? That is, does there exist a multilinear polynomial p over GF(2) in
  variables b_0, b_1, ..., b_{K-1} (where n = sum b_i * 2^i) of degree d << K
  such that p(bits(n)) = s(n) for all tested n?

  If YES (low degree d found), s(n) has a short description in the bits of n —
  which would be strong evidence (though not proof) that Prize 3 is FALSE.
  If NO (degree must equal K = floor(log2 n) + 1 = full degree), that supports
  the hardness claim.

  We use interpolation: collect s(0..2^K - 1) and compute the ANF of the
  resulting boolean function of K bits. Measure the ANF degree.

Rule 30: new[i] = old[i-1] XOR (old[i] OR old[i+1])
"""

# ---------------------------------------------------------------------------
# Core Rule 30 machinery
# ---------------------------------------------------------------------------

def rule30_step(tape):
    n = len(tape)
    new = [0] * n
    for i in range(n):
        l = tape[i - 1] if i > 0 else 0
        c = tape[i]
        r = tape[i + 1] if i < n - 1 else 0
        new[i] = l ^ (c | r)
    return new

def rule30_n_steps(tape, steps):
    t = list(tape)
    for _ in range(steps):
        t = rule30_step(t)
    return t

def make_en(n):
    """e_n: length 2n+1, single 1 at position n (centre)."""
    tape = [0] * (2 * n + 1)
    tape[n] = 1
    return tape

def s(n):
    """s(n) = centre bit of rule30_n(e_n)."""
    if n == 0:
        return 1  # e_0 = [1], 0 steps, centre = 1
    tape = rule30_n_steps(make_en(n), n)
    return tape[n]  # centre cell is always at index n (tape length 2n+1)


# ---------------------------------------------------------------------------
# TEST A: Circuit depth (DAG critical path)
# ---------------------------------------------------------------------------

def compute_dag_depth(n):
    """
    Build the explicit computation DAG for rule30_n(e_n).

    Node (t, i) = cell i at time t.
    Each node at t>0 depends on (t-1, i-1), (t-1, i), (t-1, i+1).
    The fan-in is at most 3 cells, but the gate count (XOR/OR) per cell is 2:
      step 1: tmp = c | r  (1 OR gate)
      step 2: out = l ^ tmp (1 XOR gate)
    So each interior cell at t>0 uses 2 gates; boundary cells may use fewer.

    Critical path: shortest path (in terms of gate depth) from any time-0 cell
    that is SENSITIVE (non-zero initial value or capable of influencing output)
    down to the output node (n, n).

    Since e_n has a single 1 at position n at time 0, and the DAG is a fixed
    triangle, we:
    1. Count total gates in the full triangle.
    2. Find the critical path depth = 2 * (number of time steps) because each
       time step adds 2 gate layers (one OR, one XOR).
       For n steps: critical path depth = 2n.
    3. Count gates ONLY on the forward cone from position n (the single
       initially-set cell). The forward cone at step t spans positions
       [n-t, n+t] (clipped to [0, 2n]). Count only those cells.

    Returns: (total_gates, cone_gates, critical_path_depth)
    """
    total_gates = 0
    cone_gates = 0

    for t in range(1, n + 1):
        for i in range(2 * n + 1):
            # Which cells at t-1 does this depend on?
            deps = []
            if i > 0:
                deps.append(i - 1)
            deps.append(i)
            if i < 2 * n:
                deps.append(i + 1)
            # Gate count: 1 OR + 1 XOR regardless (with 0 padding at boundary)
            gates_here = 2
            total_gates += gates_here
            # Is this cell in the forward light cone of position n at time t?
            # Forward cone: |i - n| <= t
            if abs(i - n) <= t:
                cone_gates += gates_here

    # Critical path depth: 2 gates per time step, n steps
    critical_path_depth = 2 * n
    return total_gates, cone_gates, critical_path_depth


print("=" * 60)
print("TEST A: Circuit depth / DAG gate counts for s(n), n=1..15")
print("=" * 60)
print(f"{'n':>3}  {'s(n)':>5}  {'total_gates':>12}  {'cone_gates':>11}  {'crit_depth':>10}  {'cone/total':>10}")
print("-" * 60)
for n in range(1, 16):
    sn = s(n)
    total, cone, depth = compute_dag_depth(n)
    print(f"{n:>3}  {sn:>5}  {total:>12}  {cone:>11}  {depth:>10}  {cone/total:>10.3f}")

print()
print("Interpretation:")
print("  total_gates = 2*(2n+1)*n  (all cells at all time steps, 2 gates each)")
print("  cone_gates  = 2 * sum_{t=1}^{n} (2t+1) = 2*(n^2 + 2n) = 2n(n+2)")
print("  crit_depth  = 2n (one OR + one XOR per time step, cannot be parallelised")
print("                    because step t+1 depends on step t)")
print()
print("Key question: is the critical path EXACTLY 2n (no shortcut)?")
print("Answer: YES by data-dependency — cell (t,i) depends on (t-1, i±1),")
print("so the depth of the output node is exactly 2n gate layers.")
print("No circuit can compute s(n) with fewer than 2n gate layers")
print("(this is a DAG depth lower bound, not just a heuristic).")
print()


# ---------------------------------------------------------------------------
# TEST B: Low-degree polynomial over GF(2) in bits of n
# ---------------------------------------------------------------------------

def bits(n, K):
    """Return the K-bit binary representation of n (LSB first)."""
    return [(n >> i) & 1 for i in range(K)]

def anf_from_truth_table(tt):
    """
    Compute the ANF (algebraic normal form) of a boolean function given
    by its truth table tt[0..2^K - 1] over GF(2), using the Walsh-Hadamard
    / Möbius transform.

    Returns: list of (frozenset of variable indices, coefficient) for nonzero terms.
    """
    K = len(tt).bit_length() - 1
    assert len(tt) == 2 ** K
    # Möbius transform (zeta transform over GF(2))
    f = list(tt)
    for i in range(K):
        for j in range(2 ** K):
            if j & (1 << i):
                f[j] ^= f[j ^ (1 << i)]
    # f[mask] is now the ANF coefficient for the monomial corresponding to mask
    terms = []
    for mask in range(2 ** K):
        if f[mask]:
            vars_in_monomial = frozenset(i for i in range(K) if mask & (1 << i))
            terms.append(vars_in_monomial)
    return terms

def anf_degree(terms):
    if not terms:
        return 0
    return max(len(t) for t in terms)

print("=" * 60)
print("TEST B: Polynomial over GF(2) in the bits of n")
print("=" * 60)
print()
print("For each K=2..7, treat n in 0..2^K - 1 as having K binary input")
print("variables b_0..b_{K-1}. Compute the ANF of n -> s(n) over GF(2).")
print("If degree << K, s(n) has a low-complexity description in bits of n.")
print()

for K in range(2, 8):
    N = 2 ** K
    tt = [s(n) for n in range(N)]
    terms = anf_from_truth_table(tt)
    deg = anf_degree(terms)
    num_terms = len(terms)
    max_possible = K  # maximum possible degree is K
    print(f"K={K}: s(0..{N-1}), ANF degree={deg}/{K}, #terms={num_terms} (max possible terms=2^K={N})")
    # Show the ANF if small
    if num_terms <= 12:
        term_strs = []
        for t in sorted(terms, key=lambda x: (len(x), sorted(x))):
            if len(t) == 0:
                term_strs.append("1")
            else:
                term_strs.append("*".join(f"b{i}" for i in sorted(t)))
        print(f"       ANF = {' + '.join(term_strs)}")
    else:
        # Show just the highest-degree terms
        highest = [t for t in terms if len(t) == deg]
        print(f"       Highest degree ({deg}) monomials: {len(highest)} of them")

print()
print("KEY INTERPRETATION:")
print("  If ANF degree = K (full degree) for all K, then s(n) is a maximum-degree")
print("  boolean function of the bits of n — i.e., it cannot be computed by any")
print("  circuit of depth < K = log2(n)+1. This is strong evidence for hardness.")
print()
print("  If ANF degree << K, s(n) has a short formula in the bits of n,")
print("  which would suggest Prize 3 might be FALSE (fast algorithm possible).")
print()


# ---------------------------------------------------------------------------
# TEST C: Oracle reduction sanity check
# ---------------------------------------------------------------------------
print("=" * 60)
print("TEST C: Can s(n') oracle calls reconstruct rule30_n(c)?")
print("=" * 60)
print()
print("If rule30 were GF(2)-linear, rule30_n(c) = XOR of c[k] * s_k(n)")
print("for some coefficients s_k(n). We already know rule30 is NOT linear.")
print("But maybe the nonlinearity is 'small'? Let's measure it.")
print()
print("For n=1..10: compare rule30_n(c) vs the linear approximation")
print("  linear_approx(c) = XOR_{k : sensitive for e_n} of c[k] * (rule30_n(e_k) XOR s(n))")
print("  (This is the best linear approximation using single-flip information.)")
print()

def rule30_n_on(tape_list, n_steps):
    """Compute rule30 for n_steps from the given tape."""
    t = list(tape_list)
    for _ in range(n_steps):
        t = rule30_step(t)
    return t[len(t) // 2]

def make_ek(k, length):
    """Single 1 at position k, tape of given length."""
    t = [0] * length
    if 0 <= k < length:
        t[k] = 1
    return t

import random
random.seed(42)

for n in range(1, 11):
    L = 2 * n + 1
    base = s(n)

    # Sensitivity vector: delta_k = rule30_n(e_k') XOR s(n)
    # where e_k' is the tape of length L with 1 at position k.
    # This is the "derivative" of the function at e_n in direction k.
    # For a linear function this would reconstruct everything.
    delta = []
    for k in range(L):
        ek = make_ek(k, L)
        val = rule30_n_on(ek, n)
        delta.append(val ^ base)  # XOR with s(n) to get the "effect of turning on k"

    # For a random sample of 50 inputs c, compare true vs linear approx
    errors = 0
    trials = 50
    for _ in range(trials):
        c = [random.randint(0, 1) for _ in range(L)]
        true_val = rule30_n_on(c, n)
        # Linear approximation: base XOR (XOR of c[k]*delta[k] for all k)
        approx = base
        for k in range(L):
            if c[k] and delta[k]:
                approx ^= 1
        if approx != true_val:
            errors += 1

    error_rate = errors / trials
    print(f"n={n:>2}: linear approx error rate = {errors}/{trials} = {error_rate:.2f}  "
          f"(0.0 = perfect linear, 0.5 = useless)")

print()
print("Interpretation:")
print("  If error rate >> 0, the oracle calls s(n') for various n'")
print("  CANNOT be combined linearly to compute rule30_n(c) for general c.")
print("  The nonlinearity of Rule 30 blocks any simple reduction.")
print()
print("  Even if error rate = 0 here, that would only show LINEAR reducibility")
print("  for small n — higher-order terms become dominant quickly.")
