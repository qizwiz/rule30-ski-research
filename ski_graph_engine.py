import sys

# Global Hash Consing Table (The "Skin/Memory Foam")
# Maps a structural signature -> physical Node object
MEMO_POOL = {}

class Node:
    __slots__ = ['is_app', 'left', 'right', 'name', 'depth', '_hash', 'forward']
    
    def __init__(self, is_app, left=None, right=None, name=None):
        self.is_app = is_app
        self.left = left
        self.right = right
        self.name = name
        self.forward = None  # Used for in-place graph updates (indirection)
        
        if is_app:
            self.depth = 1 + max(self.left.depth, self.right.depth)
            self._hash = hash((True, id(self.left), id(self.right)))
        else:
            self.depth = 0
            self._hash = hash((False, self.name))

    def resolve(self):
        """Chase forwarding pointers to get the actual current state of this node."""
        curr = self
        while curr.forward is not None:
            curr = curr.forward
        return curr

def get_comb(name):
    sig = (False, name)
    if sig not in MEMO_POOL:
        MEMO_POOL[sig] = Node(False, name=name)
    return MEMO_POOL[sig]

def mk_app(left_node, right_node):
    left = left_node.resolve()
    right = right_node.resolve()
    sig = (True, id(left), id(right))
    if sig not in MEMO_POOL:
        MEMO_POOL[sig] = Node(True, left=left, right=right)
    return MEMO_POOL[sig]

# Combinator Primitives
K_c = get_comb('K')
S_c = get_comb('S')
I_c = get_comb('I')

# --- Graph Reduction (In-Place Mutation) ---
def reduce_graph(root):
    """
    Performs leftmost-outermost graph reduction.
    Mutates nodes in-place by setting 'forward' pointers.
    Returns True if a reduction occurred, False if in normal form.
    """
    spine = []
    curr = root.resolve()
    
    # Unwind the spine
    while curr.is_app:
        spine.append(curr)
        curr = curr.left.resolve()

    if not curr.is_app:
        n_args = len(spine)
        if curr.name == 'I' and n_args >= 1:
            app_node = spine[-1]
            arg = app_node.right.resolve()
            app_node.forward = arg # In-place update!
            return True
            
        elif curr.name == 'K' and n_args >= 2:
            app_node = spine[-2] # The node representing ((K x) y)
            arg_x = spine[-1].right.resolve()
            app_node.forward = arg_x # In-place delete of y!
            return True
            
        elif curr.name == 'S' and n_args >= 3:
            app_node = spine[-3] # The node representing (((S x) y) z)
            x = spine[-1].right.resolve()
            y = spine[-2].right.resolve()
            z = spine[-3].right.resolve()
            
            # S x y z -> (x z) (y z)
            new_left = mk_app(x, z)
            new_right = mk_app(y, z)
            new_node = mk_app(new_left, new_right)
            
            app_node.forward = new_node # In-place topological stretch!
            return True

    # If head can't reduce, try reducing arguments left-to-right
    for i in range(1, len(spine) + 1):
        app_node = spine[-i]
        arg = app_node.right.resolve()
        if reduce_graph(arg):
            # Because of hash consing, if a child mutates, we technically 
            # don't need to rebuild the parent's structure if we rely on .resolve().
            # However, to keep the MEMO_POOL clean, true graph reducers often 
            # do pointer reversal. For this prototype, the forward pointer handles it.
            return True
            
    return False

# --- Utilities ---
def to_string(node, is_right=False):
    node = node.resolve()
    if not node.is_app: return node.name
    left_str = to_string(node.left, False)
    right_str = to_string(node.right, True)
    res = f"{left_str}{right_str}"
    if is_right: return f"({res})"
    return res

def get_basin(node, is_right=False):
    node = node.resolve()
    if not node.is_app: return "*"
    left_str = get_basin(node.left, False)
    right_str = get_basin(node.right, True)
    res = f"{left_str}{right_str}"
    if is_right: return f"({res})"
    return res

# --- Rule 30 Compiled ---
T = K_c
F = mk_app(K_c, I_c)

# Hand-compiled XOR and OR for maximum sharing
# NOT = S(K(S I))(K T) F
NOT = mk_app(mk_app(S_c, mk_app(mk_app(S_c, I_c), mk_app(K_c, F))), mk_app(K_c, T))
# OR p q = p p q
# XOR p q = p (NOT q) q

# We build the Rule 30 logic directly as a Python function that constructs the graph
def apply_rule30(p, q, r):
    # OR(q, r) -> q q r
    q_or_r = mk_app(mk_app(q, q), r)
    # NOT(q_or_r)
    not_q_or_r = mk_app(NOT, q_or_r)
    # XOR(p, q_or_r) -> p (NOT q_or_r) q_or_r
    return mk_app(mk_app(p, not_q_or_r), q_or_r)

def build_center_cell(gen, pos=0):
    if gen == 0:
        return T if pos == 0 else F
    left = build_center_cell(gen - 1, pos - 1)
    center = build_center_cell(gen - 1, pos)
    right = build_center_cell(gen - 1, pos + 1)
    return apply_rule30(left, center, right)

print("--- Topological Memory Foam (Graph Reduction) Engine ---")

for gen in range(1, 6):
    MEMO_POOL.clear() # Reset memory foam for clean measurement
    K_c = get_comb('K')
    S_c = get_comb('S')
    I_c = get_comb('I')
    T = K_c
    F = mk_app(K_c, I_c)
    NOT = mk_app(mk_app(S_c, mk_app(mk_app(S_c, I_c), mk_app(K_c, F))), mk_app(K_c, T))
    
    root = build_center_cell(gen, 0)
    
    initial_physical_nodes = len(MEMO_POOL)
    theoretical_tree_size = 3**gen # Roughly, not counting internal logic
    
    print(f"\\n[Generation {gen}] Center Cell Topology:")
    print(f"  Theoretical Independent Cells: {theoretical_tree_size}")
    print(f"  Actual Physical Nodes in Memory: {initial_physical_nodes} (Hash-Consed Compression!)")
    
    steps = 0
    while reduce_graph(root):
        steps += 1
        if steps > 100000:
            print("  [!] Reached step limit.")
            break
            
    res_node = root.resolve()
    res_val = "True (Black)" if to_string(res_node) == "K" else "False (White)" if to_string(res_node) == "K(I)" else to_string(res_node)
    
    print(f"  Result: {res_val} in {steps} topological graph updates.")
    print(f"  Final Physical Nodes in Memory: {len(MEMO_POOL)}")
    print(f"  Final Depth: {res_node.depth}")
