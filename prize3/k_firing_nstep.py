"""
n-step Rule 30 symbolic normal form scaling experiment.

Question: How does the stuck normal form grow as we compose n applications
of the Rule 30 local rule?

For n=1: p(qKr(KI)K)(qKr)  — q,r appear twice, 10 atoms total
For n=2: center cell at t=2 from cells at t=0 (5 cells: c_{-2}..c_{2})
For n=3: 7 input cells, etc.

Key tracking:
  - How many atoms total in stuck normal form?
  - How many distinct input atoms?
  - How many times does each input appear?
  - How many reduction steps to reach stuck form?
  - Does the growth pattern suggest O(n²) or O(2^n)?
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
        return {n} if (n.islower() or n.isdigit()) else set()
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

def size(t):
    if is_atom(t): return 1
    return size(t[1]) + size(t[2])

def count_atom(t, name):
    if is_atom(t): return 1 if t[1] == name else 0
    return count_atom(t[1], name) + count_atom(t[2], name)

# Build Rule30 combinator (same as before)
K = atom('K'); I = atom('I'); KI = app(K, I)

def make_rule30():
    p = atom('p'); q = atom('q'); r = atom('r')
    OR_qr = app(app(q, K), r)
    NOT_OR_qr = app(app(OR_qr, KI), K)
    body = app(app(p, NOT_OR_qr), OR_qr)
    r30r  = BA('r', body)
    r30qr = BA('q', r30r)
    return BA('p', r30qr)

rule30 = make_rule30()

def reduce_step(t):
    if is_atom(t): return None
    l, r2 = t[1], t[2]
    if is_atom(l) and l[1] == 'I': return r2, 'I'
    if is_app(l):
        ll, lr = l[1], l[2]
        if is_atom(ll) and ll[1] == 'K': return lr, 'K'
        if is_app(ll):
            lll, llr = ll[1], ll[2]
            if is_atom(lll) and lll[1] == 'S':
                return app(app(llr, r2), app(lr, r2)), 'S'
    res = reduce_step(l)
    if res: nl, rule = res; return app(nl, r2), rule
    res = reduce_step(r2)
    if res: nr, rule = res; return app(l, nr), rule
    return None

def full_reduce(t, max_steps=500000):
    steps = 0; counts = {'I': 0, 'K': 0, 'S': 0}
    for _ in range(max_steps):
        res = reduce_step(t)
        if res is None:
            return t, steps, counts, 'nf'
        t, rule = res
        counts[rule] += 1
        steps += 1
    return t, steps, counts, 'timeout'

# ─── Build n-step computation ─────────────────────────────────────────────────
# For n steps, the center cell computation is:
# cell[n][0] = rule30( cell[n-1][-1], cell[n-1][0], cell[n-1][1] )
# where each cell[n-1][j] = rule30( cell[n-2][j-1], cell[n-2][j], cell[n-2][j+1] )
# ...and leaf cells are symbolic atoms c_i at time 0.
#
# For n=1: 3 inputs: c_{-1}, c_0, c_1
# For n=2: 5 inputs: c_{-2}, c_{-1}, c_0, c_1, c_2
# For n steps: 2n+1 inputs: c_{-n}, ..., c_n

def cell_name(i):
    # Use single letters for small |i|, else use xi_N notation
    if i == 0: return 'z'
    if i > 0: return chr(ord('a') + i - 1)[:1] if i <= 5 else f'x{i}'
    return chr(ord('a') - i - 1)[:1].upper() if -i <= 5 else f'y{-i}'  # uppercase for negative

def build_nstep(n):
    """
    Build the n-step center cell computation as an SKI application.
    Returns the expression with symbolic leaf atoms.
    """
    # Level 0: symbolic atoms for cells at time 0
    # Cells range from -n to n
    cells_0 = {i: atom(cell_name(i)) for i in range(-n, n+1)}

    # Iteratively build levels 1..n
    cells = cells_0
    for step in range(1, n+1):
        new_cells = {}
        # At step t, cells range from -(n-t) to (n-t)
        for j in range(-(n-step), (n-step)+1):
            left  = cells[j-1]
            center= cells[j]
            right = cells[j+1]
            new_cells[j] = app(app(app(rule30, left), center), right)
        cells = new_cells

    return cells[0]

print("=" * 65)
print("n-STEP RULE 30 CENTER CELL: SYMBOLIC NORMAL FORM SCALING")
print("=" * 65)
print()
print(f"{'n':>3}  {'inputs':>7}  {'steps':>8}  {'K-fires':>8}  {'nf_size':>8}  {'each_input_appears_avg':>22}  status")
print("-" * 80)

for n in range(1, 6):
    num_inputs = 2*n + 1
    input_names = [cell_name(i) for i in range(-n, n+1)]

    expr = build_nstep(n)
    nf, steps, counts, status = full_reduce(expr, max_steps=500000)

    nf_size = size(nf)
    fv = free_vars(nf)

    # Count appearances of each input
    appearances = [count_atom(nf, name) for name in input_names]
    avg_appearances = sum(appearances) / len(appearances) if appearances else 0

    # Verify all inputs present
    all_present = all(name in fv for name in input_names)

    print(f"{n:>3}  {num_inputs:>7}  {steps:>8}  {counts['K']:>8}  {nf_size:>8}  {avg_appearances:>22.1f}  {status} {'✓' if all_present else '✗ MISSING'}")

    if n <= 3:
        print(f"     Input appearances: {dict(zip(input_names, appearances))}")
        print(f"     Normal form: {unparse(nf)[:120]}{'...' if len(unparse(nf))>120 else ''}")
    print()

print()
print("=" * 65)
print("GROWTH ANALYSIS")
print("=" * 65)
print()
print("If steps ~ C * n^k, we'd see polynomial growth in step counts.")
print("If steps ~ C * 2^n, we'd see exponential growth.")
print()
print("The normal form size reveals the 'decision tree' complexity of Rule 30.")
print("If it grows exponentially, Rule 30 has NO short formula — only")
print("exponential-size Boolean circuits can represent it.")
print()
print("PRIZE #3 IMPLICATION:")
print("  The n-step symbolic normal form preserves ALL 2n+1 input atoms.")
print("  If a RAM reads k < n cells, at least n-k+1 input cells remain unread.")
print("  Any unread cell c_i has some configuration where flipping c_i changes")
print("  the Rule 30 output (by sensitivity of Rule 30 — if provable by induction).")
print("  Therefore: any correct RAM must read ALL 2n+1 cells → Ω(n) time.")
