"""
Symbolic K-firing experiment: run Rule 30 with FREE VARIABLE inputs.

With concrete T/F inputs, K never fires on free vars — but trivially so
(no free vars exist after substitution).

The more revealing test: apply compiled Rule30_ski to *symbolic atoms*
p, q, r (irreducible free variables) and see:
  1. What does the stuck normal form look like?
  2. Does it contain ALL THREE of p, q, r?
  3. How many reduction steps until stuck?
  4. What structural insights does the normal form reveal?
"""

def atom(n):  return ('atom', n)
def app(l,r): return ('app', l, r)
def is_atom(t): return t[0] == 'atom'
def is_app(t):  return t[0] == 'app'

def unparse(t):
    if is_atom(t): return t[1]
    l = unparse(t[1]); r = unparse(t[2])
    if is_app(t[2]): r = f'({r})'
    return f'{l}{r}'

def free_vars(t):
    if is_atom(t):
        n = t[1]
        return {n} if n.islower() else set()
    return free_vars(t[1]) | free_vars(t[2])

def occurs_free(var, t):
    return var in free_vars(t)

def BA(var, t):
    if is_atom(t):
        if t[1] == var: return atom('I')
        else: return app(atom('K'), t)
    if not occurs_free(var, t):
        return app(atom('K'), t)
    return app(app(atom('S'), BA(var, t[1])), BA(var, t[2]))

# Build Rule30 compiled form (same as before)
p = atom('p'); q = atom('q'); r = atom('r')
K = atom('K'); I = atom('I'); KI = app(K, I)

OR_qr = app(app(q, K), r)
NOT_OR_qr = app(app(OR_qr, KI), K)
body = app(app(p, NOT_OR_qr), OR_qr)

rule30_r  = BA('r', body)
rule30_qr = BA('q', rule30_r)
rule30    = BA('p', rule30_qr)

# ─── Reduction with SYMBOLIC free variables ────────────────────────────────
# p, q, r are atoms that are NOT K, I, or S — so they cannot reduce.
# The engine will get "stuck" when it hits them in head position.

P = atom('p')  # symbolic free variable — lowercase, won't reduce
Q = atom('q')
R = atom('r')

def reduce_step(t):
    """Standard leftmost-outermost; free vars are just atoms, can't reduce."""
    if is_atom(t): return None
    l, r2 = t[1], t[2]

    # I x → x
    if is_atom(l) and l[1] == 'I':
        return r2, 'I'
    if is_app(l):
        ll, lr = l[1], l[2]
        # K x y → x
        if is_atom(ll) and ll[1] == 'K':
            return lr, 'K'
        if is_app(ll):
            lll, llr = ll[1], ll[2]
            # S x y z → xz(yz)
            if is_atom(lll) and lll[1] == 'S':
                return app(app(llr, r2), app(lr, r2)), 'S'

    res = reduce_step(l)
    if res: nl, rule = res; return app(nl, r2), rule
    res = reduce_step(r2)
    if res: nr, rule = res; return app(l, nr), rule
    return None

def full_reduce_symbolic(t, max_steps=2000):
    steps = 0
    rule_counts = {'I': 0, 'K': 0, 'S': 0}
    for _ in range(max_steps):
        res = reduce_step(t)
        if res is None:
            return t, steps, rule_counts, 'normal_form'
        t, rule = res
        rule_counts[rule] += 1
        steps += 1
    return t, steps, rule_counts, 'max_steps'

print("=" * 65)
print("SYMBOLIC REDUCTION: Rule30_ski p q r")
print("p, q, r are free variables (irreducible atoms)")
print("=" * 65)

# Apply compiled Rule30 to symbolic atoms
expr = app(app(app(rule30, P), Q), R)
print(f"Input expression size: {len(unparse(expr))} chars")
print()

nf, steps, counts, status = full_reduce_symbolic(expr)
nf_str = unparse(nf)

print(f"Status: {status}")
print(f"Steps: {steps}  (I:{counts['I']} K:{counts['K']} S:{counts['S']})")
print(f"Free vars in result: {free_vars(nf)}")
print(f"Normal form: {nf_str}")
print()

# Check if all three inputs appear
has_p = 'p' in free_vars(nf)
has_q = 'q' in free_vars(nf)
has_r = 'r' in free_vars(nf)
print(f"p present: {has_p}  q present: {has_q}  r present: {has_r}")
print()

# How many times does each appear?
def count_var(t, var):
    if is_atom(t): return 1 if t[1] == var else 0
    return count_var(t[1], var) + count_var(t[2], var)

print(f"p appears {count_var(nf, 'p')} time(s) in normal form")
print(f"q appears {count_var(nf, 'q')} time(s) in normal form")
print(f"r appears {count_var(nf, 'r')} time(s) in normal form")
print()

# Is the normal form what we expect?
# Body before compilation: p (OR_qr (KI) K) OR_qr  where OR_qr = q K r
expected_body = "p((qK(r))(KI)K)(qK(r))"
# Remove spaces for comparison
print(f"Expected conceptual form: p ((q K r)(KI)K) (q K r)")
print(f"Actual normal form:       {nf_str}")
print()

if all([has_p, has_q, has_r]):
    print("✓ All three inputs preserved in the stuck normal form.")
    print()
    print("INTERPRETATION:")
    print("  The SKI reduction of Rule30(p,q,r) with symbolic inputs")
    print("  produces a normal form containing p, q, AND r.")
    print("  No input variable is K-discarded during the symbolic reduction.")
    print()
    print("  This means the Rule 30 local rule is 'input-complete':")
    print("  every input appears in the residual computation after")
    print("  all combinator bookkeeping is resolved.")
    print()
    print("IMPLICATION FOR PRIZE #3 (indistinguishability):")
    print("  The stuck normal form p ((q K r)(KI)K) (q K r) represents")
    print("  the 'fully unfolded' Rule 30 formula, waiting for p/q/r.")
    print("  Its SIZE is O(1) for the single-step local rule.")
    print()
    print("  For the n-step computation, the analogous stuck normal form")
    print("  would be an expression of size O(n²) or O(2^n) containing")
    print("  all 2n+1 input atoms. If we can show the reduction to reach")
    print("  that stuck form takes Ω(n) steps, that's the lower bound.")

# ─── Structural insight: size of the stuck normal form ────────────────────────
def size(t):
    if is_atom(t): return 1
    return size(t[1]) + size(t[2])

print()
print("=" * 65)
print("NORMAL FORM STRUCTURAL ANALYSIS")
print("=" * 65)
print(f"Normal form atom count: {size(nf)}")
print(f"  Of which: p={count_var(nf,'p')} q={count_var(nf,'q')} r={count_var(nf,'r')}")
combinator_atoms = size(nf) - count_var(nf,'p') - count_var(nf,'q') - count_var(nf,'r')
print(f"  Combinator atoms (K,I): {combinator_atoms}")
print()
print("K-count in normal form:", count_var(nf, 'K'))
print("I-count in normal form:", count_var(nf, 'I'))
print()
print("Ratio combinator:input atoms =", combinator_atoms, ":", count_var(nf,'p')+count_var(nf,'q')+count_var(nf,'r'))
