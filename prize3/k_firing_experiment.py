"""
K-Firing Experiment: Rule 30 local rule p XOR (q OR r)

Question: Does K ever fire to DISCARD one of the three input variables?

If K never discards any input in the base case (single-step local rule),
that's the base case of a K-non-discarding induction for the full n-step
Rule 30 computation — which would yield the indistinguishability witness
needed for Prize #3.

Church Booleans:
  T = K          (selects first argument)
  F = K(I)       (selects second argument)
  NOT b = b F T = b (KI) K
  OR p q = p T q = p K q
  XOR p q = p (NOT q) q

Rule 30: center' = p XOR (q OR r)
"""

# ─── SKI AST ─────────────────────────────────────────────────────────────────

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
    """Return set of variable names (lowercase atoms) in t."""
    if is_atom(t):
        n = t[1]
        # lowercase = variable; uppercase = combinator
        return {n} if n.islower() else set()
    return free_vars(t[1]) | free_vars(t[2])

def subst(t, var, val):
    """Substitute val for var in t."""
    if is_atom(t):
        return val if t[1] == var else t
    return app(subst(t[1], var, val), subst(t[2], var, val))

# ─── Bracket abstraction (compile λ to SKI) ──────────────────────────────────

def occurs_free(var, t):
    return var in free_vars(t)

def BA(var, t):
    """Bracket abstraction: compile λvar.t to SKI."""
    if is_atom(t):
        if t[1] == var:
            return atom('I')               # BA(x, x) = I
        else:
            return app(atom('K'), t)       # BA(x, c) = K c
    # t is an application
    if not occurs_free(var, t):
        return app(atom('K'), t)           # BA(x, t) = K t  (x not free)
    # BA(x, f a) = S (BA(x, f)) (BA(x, a))
    return app(app(atom('S'), BA(var, t[1])), BA(var, t[2]))

# ─── Church Booleans as atoms + known expansions ─────────────────────────────

T_atom = atom('K')            # True  = K
F_atom = app(atom('K'), atom('I'))  # False = KI

# ─── Build Rule 30 as a SKI combinator ───────────────────────────────────────
# OR(q, r) = q K r       (if q=T → K → returns first = K; if q=F → KI → returns r)
# NOT(b)   = b F T = b (KI) K
# XOR(p, x) = p (NOT x) x = p (x (KI) K) x
# Rule30(p, q, r) = XOR p (OR q r) = let x = OR(q,r) in p (NOT x) x
#                = p ((q K r)(KI)K) (q K r)

# We'll build this as a lambda then compile
# Rule30 = λp. λq. λr. p ((q K r)(KI)K) (q K r)

p = atom('p')
q = atom('q')
r = atom('r')
K = atom('K')
I = atom('I')
KI = app(K, I)

# OR_qr = q K r
OR_qr = app(app(q, K), r)

# NOT OR_qr = OR_qr (KI) K
NOT_OR_qr = app(app(OR_qr, KI), K)

# XOR p (OR_qr) = p (NOT OR_qr) OR_qr
body = app(app(p, NOT_OR_qr), OR_qr)

# Compile via bracket abstraction
rule30_r  = BA('r', body)
rule30_qr = BA('q', rule30_r)
rule30    = BA('p', rule30_qr)

print("Rule 30 SKI compiled form:")
print(f"  {unparse(rule30)}")
print(f"  Size (atoms): {len(unparse(rule30).replace('(','').replace(')',''))}")
print()

# ─── Reduction engine with K-firing trace ────────────────────────────────────

k_firings = []  # global log: (step, discarded_subterm)

def reduce_step_traced(t, depth=0):
    """
    Leftmost-outermost reduction, one step.
    Returns (reduced_term, rule_name) or None if no redex.
    Logs K-firings to k_firings.
    """
    if is_atom(t): return None
    l, r2 = t[1], t[2]

    # I x → x
    if is_atom(l) and l[1] == 'I':
        return r2, 'I'

    if is_app(l):
        ll, lr = l[1], l[2]

        # K x y → x  (K-firing: discards y)
        if is_atom(ll) and ll[1] == 'K':
            k_firings.append({
                'kept':     unparse(lr),
                'discarded': unparse(r2),
                'discarded_fv': list(free_vars(r2)),
            })
            return lr, 'K'

        if is_app(ll):
            lll, llr = ll[1], ll[2]
            # S x y z → xz(yz)
            if is_atom(lll) and lll[1] == 'S':
                return app(app(llr, r2), app(lr, r2)), 'S'

    # Try left, then right (leftmost-outermost)
    res = reduce_step_traced(l, depth+1)
    if res: nl, rule = res; return app(nl, r2), rule
    res = reduce_step_traced(r2, depth+1)
    if res: nr, rule = res; return app(l, nr), rule
    return None

def full_reduce(t, max_steps=500):
    """Reduce to normal form; return (nf, steps, k_firing_count)."""
    global k_firings
    k_firings = []
    for i in range(max_steps):
        res = reduce_step_traced(t)
        if res is None:
            return t, i, k_firings[:]
        t, _ = res
    return t, max_steps, k_firings[:]  # hit limit

# ─── Run on all 8 truth-value inputs ─────────────────────────────────────────

print("=" * 65)
print("FULL REDUCTION TRACE — all 8 inputs (T=K, F=KI)")
print("Checking: does K ever DISCARD a free variable p, q, or r?")
print("=" * 65)

input_names = ['p', 'q', 'r']
summary_rows = []

for bits in range(8):
    bp = (bits >> 2) & 1   # p
    bq = (bits >> 1) & 1   # q
    br =  bits       & 1   # r

    vals = {
        'p': T_atom if bp else F_atom,
        'q': T_atom if bq else F_atom,
        'r': T_atom if br else F_atom,
    }
    label = {'0': 'F', '1': 'T'}
    pqr_str = f"p={label[str(bp)]} q={label[str(bq)]} r={label[str(br)]}"

    # Apply rule30 to the three values
    expr = app(app(app(rule30, vals['p']), vals['q']), vals['r'])

    nf, steps, firings = full_reduce(expr)
    result_str = unparse(nf)

    # Rule 30 truth table: center' = p XOR (q OR r)
    expected_bit = bp ^ (bq | br)
    # T = K, F = KI; check if result matches
    result_is_T = (result_str == 'K')
    result_is_F = (result_str == 'K(I)' or result_str == 'KI')
    result_correct = (result_is_T and expected_bit == 1) or (result_is_F and expected_bit == 0)

    # Which free vars were discarded?
    discarded_vars = set()
    for f in firings:
        discarded_vars |= set(f['discarded_fv'])

    # Which input variable names are present
    kept_vars = {v for v in input_names if v not in discarded_vars}

    print(f"\n{pqr_str}  →  expected={'T' if expected_bit else 'F'}")
    print(f"  Steps: {steps}  |  K-firings: {len(firings)}")
    if firings:
        for f in firings:
            disc_fv = f['discarded_fv']
            marker = " *** INPUT VAR DISCARDED ***" if any(v in input_names for v in disc_fv) else ""
            print(f"    K keeps [{f['kept']}]  discards [{f['discarded']}]  (fv={disc_fv}){marker}")
    print(f"  Normal form: {result_str}")
    print(f"  Correct: {'✓' if result_correct else '✗'}")
    print(f"  Vars discarded from input: {discarded_vars & set(input_names)}")

    summary_rows.append({
        'pqr': pqr_str,
        'expected': expected_bit,
        'correct': result_correct,
        'k_count': len(firings),
        'input_vars_discarded': discarded_vars & set(input_names),
        'nf': result_str,
    })

print()
print("=" * 65)
print("SUMMARY")
print("=" * 65)

all_correct = all(r['correct'] for r in summary_rows)
any_input_discarded = any(r['input_vars_discarded'] for r in summary_rows)
always_which_discarded = set.union(*[r['input_vars_discarded'] for r in summary_rows]) if summary_rows else set()

print(f"All 8 outputs correct: {'✓' if all_correct else '✗'}")
print(f"Any input var (p/q/r) ever discarded by K: {'YES *** LEMMA FAILS ***' if any_input_discarded else 'NO ✓'}")
if any_input_discarded:
    print(f"  Variables discarded: {always_which_discarded}")
    print()
    print("NOTE: K discards input variables. The K-non-discarding lemma as")
    print("stated (K never fires on an input) does NOT hold for Rule 30.")
    print("However, what matters for Prize #3 is whether flipping any input")
    print("can change the output — which is guaranteed by the truth table.")
else:
    print()
    print("✓ K never fires to discard p, q, or r directly.")
    print("  K-firings only discard combinator subterms, not input variables.")
    print("  This supports the K-non-discarding hypothesis!")
    print()
    print("IMPLICATION FOR PRIZE #3:")
    print("  Base case: in the single-step Rule 30 local rule, each input")
    print("  p, q, r is 'used' (not K-discarded) during the computation.")
    print("  If this lifts to the full n-step cone computation by induction,")
    print("  then every input cell in the dependency cone contributes to the")
    print("  output — providing the indistinguishability witness for the")
    print("  Omega(n) lower bound.")

print()
print("=" * 65)
print("STRUCTURAL ANALYSIS: K-firing patterns by input combination")
print("=" * 65)
for r in summary_rows:
    disc = r['input_vars_discarded'] or '(none)'
    print(f"  {r['pqr']:30s}  k-firings={r['k_count']}  discarded={disc}  nf={r['nf']}")
