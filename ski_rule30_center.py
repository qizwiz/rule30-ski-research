import sys
sys.setrecursionlimit(10000)

# --- SKI AST ---
class Expr: pass
class Comb(Expr):
    def __init__(self, name): self.name = name
    def __str__(self): return self.name
class Var(Expr):
    def __init__(self, name): self.name = name
    def __str__(self): return self.name
class App(Expr):
    def __init__(self, left, right):
        self.left = left
        self.right = right

def to_string(expr, is_right=False, basin_mode=False):
    if isinstance(expr, (Comb, Var)):
        return '*' if basin_mode else expr.name
    left_str = to_string(expr.left, False, basin_mode)
    right_str = to_string(expr.right, True, basin_mode)
    res = f"{left_str}{right_str}"
    if is_right:
        return f"({res})"
    return res

def basin(expr): return to_string(expr, basin_mode=True)
def depth(expr):
    if isinstance(expr, (Comb, Var)): return 0
    return 1 + max(depth(expr.left), depth(expr.right))

# --- Bracket Abstraction (Lambda -> SKI) ---
def free_vars(expr):
    if isinstance(expr, Comb): return set()
    if isinstance(expr, Var): return {expr.name}
    if isinstance(expr, App): return free_vars(expr.left) | free_vars(expr.right)

def BA(x, expr):
    if x not in free_vars(expr):
        return App(Comb('K'), expr)
    if isinstance(expr, Var) and expr.name == x:
        return Comb('I')
    if isinstance(expr, App):
        if isinstance(expr.right, Var) and expr.right.name == x and x not in free_vars(expr.left):
            return expr.left
        return App(App(Comb('S'), BA(x, expr.left)), BA(x, expr.right))

def L(x, expr): return BA(x, expr)
def A(e1, e2): return App(e1, e2)
def V(name): return Var(name)

# --- Reduction Engine (Leftmost-Outermost) ---
def rebuild_spine(spine, num_consumed, new_head, replace_arg=False):
    if replace_arg:
        idx = len(spine) - num_consumed
        curr = new_head
        for i in range(idx - 1, -1, -1):
            curr = App(curr, spine[i].right)
        return curr
    else:
        curr = new_head
        for i in range(len(spine) - num_consumed - 1, -1, -1):
            curr = App(curr, spine[i].right)
        return curr

def reduce_step(expr):
    spine = []
    curr = expr
    while isinstance(curr, App):
        spine.append(curr)
        curr = curr.left

    if isinstance(curr, Comb):
        n_args = len(spine)
        if curr.name == 'I' and n_args >= 1:
            return rebuild_spine(spine, 1, spine[-1].right), 'I'
        elif curr.name == 'K' and n_args >= 2:
            return rebuild_spine(spine, 2, spine[-1].right), 'K'
        elif curr.name == 'S' and n_args >= 3:
            arg1, arg2, arg3 = spine[-1].right, spine[-2].right, spine[-3].right
            new_node = App(App(arg1, arg3), App(arg2, arg3))
            return rebuild_spine(spine, 3, new_node), 'S'

    # Reduce inside arguments (left to right)
    for i in range(1, len(spine)+1):
        app_node = spine[-i]
        res, comb = reduce_step(app_node.right)
        if res is not None:
            new_app = App(app_node.left, res)
            return rebuild_spine(spine, i, new_app, replace_arg=True), comb
    return None, None

# --- Compile Rule 30 to SKI ---
K_c = Comb('K')
S_c = Comb('S')
I_c = Comb('I')

T = K_c
F = A(K_c, I_c)

p, q, r = V('p'), V('q'), V('r')
NOT = L('p', A(A(p, F), T))
OR = L('p', L('q', A(A(p, p), q)))
XOR = L('p', L('q', A(A(p, A(NOT, q)), q)))
Rule30 = L('p', L('q', L('r', A(A(XOR, p), A(A(OR, q), r)))))

# --- Global State Tree Builder ---
def get_cell_expr(gen, pos):
    """
    Recursively builds the exact SKI computation tree for the cell at (gen, pos).
    gen=0, pos=0 is the initial black cell (True).
    """
    if gen == 0:
        return T if pos == 0 else F
    left = get_cell_expr(gen - 1, pos - 1)
    center = get_cell_expr(gen - 1, pos)
    right = get_cell_expr(gen - 1, pos + 1)
    return A(A(A(Rule30, left), center), right)

print("--- Center Column Evolution Analysis ---")

for gen in range(1, 6):  # Test generations 1, 2, 3, 4, 5
    print(f"\\nEvaluating Center Cell at Generation {gen}...")
    expr = get_cell_expr(gen, 0)
    
    curr = expr
    steps = 0
    basins_visited = set()
    comb_counts = {'I': 0, 'K': 0, 'S': 0}
    depth_deltas = {'I': [], 'K': [], 'S': []}
    
    basins_visited.add(basin(curr))
    
    while True:
        nxt, comb = reduce_step(curr)
        if not nxt: break
        
        delta = depth(nxt) - depth(curr)
        b_new = basin(nxt)
        
        if b_new == basin(curr):
            print(f"CRITICAL: Intra-basin transition at step {steps}!")
            
        basins_visited.add(b_new)
        comb_counts[comb] += 1
        depth_deltas[comb].append(delta)
        
        curr = nxt
        steps += 1
        
        # Safety break for massive trees
        if steps > 500000:
            print("Reached 500,000 steps limit! Stopping early.")
            break

    res_val = "True (Black)" if to_string(curr) == "K" else "False (White)" if to_string(curr) == "K(I)" else to_string(curr)
    print(f"Result: {res_val}")
    print(f"Total Steps: {steps}")
    print(f"Unique Basins: {len(basins_visited)} (Verified Inter-Basin Theorem: {len(basins_visited) == steps + 1})")
    print(f"Final Depth: {depth(curr)}")
    
    print(f"Depth Asymmetry:")
    for c in ['I', 'K', 'S']:
        deltas = depth_deltas[c]
        if deltas:
            avg = sum(deltas) / len(deltas)
            print(f"  {c} fired {comb_counts[c]:>4} times. Mean ∆: {avg:+.2f} (Range: {min(deltas):+} to {max(deltas):+})")
        else:
            print(f"  {c} fired    0 times.")

