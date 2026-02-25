import sys

sys.setrecursionlimit(500000)

MEMO_POOL = {}

class Node:
    __slots__ = ['is_app', 'left', 'right', 'name', 'depth', '_hash', 'forward']
    
    def __init__(self, is_app, left=None, right=None, name=None):
        self.is_app = is_app
        self.left = left
        self.right = right
        self.name = name
        self.forward = None
        
        if is_app:
            self.depth = 1 + max(self.left.depth, self.right.depth)
            self._hash = hash((True, id(self.left), id(self.right)))
        else:
            self.depth = 0
            self._hash = hash((False, self.name))

    def resolve(self):
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

K_c = get_comb('K')
S_c = get_comb('S')
I_c = get_comb('I')

T = K_c
F = mk_app(K_c, I_c)

# Correctly compiled NOT: S (S I (K F)) (K T)
NOT = mk_app(mk_app(S_c, mk_app(mk_app(S_c, I_c), mk_app(K_c, F))), mk_app(K_c, T))

def apply_rule30(p, q, r):
    q_or_r = mk_app(mk_app(q, q), r)
    not_q_or_r = mk_app(NOT, q_or_r)
    return mk_app(mk_app(p, not_q_or_r), q_or_r)

BUILD_MEMO = {}
def build_center_cell(gen, pos=0):
    if gen == 0:
        return T if pos == 0 else F
        
    key = (gen, pos)
    if key in BUILD_MEMO: return BUILD_MEMO[key]
    
    left = build_center_cell(gen - 1, pos - 1)
    center = build_center_cell(gen - 1, pos)
    right = build_center_cell(gen - 1, pos + 1)
    
    res = apply_rule30(left, center, right)
    BUILD_MEMO[key] = res
    return res

def count_combinators():
    s_count = 0
    k_count = 0
    i_count = 0
    app_count = 0
    for node in MEMO_POOL.values():
        if node.is_app:
            app_count += 1
        else:
            if node.name == 'S': s_count += 1
            elif node.name == 'K': k_count += 1
            elif node.name == 'I': i_count += 1
    return s_count, k_count, i_count, app_count

# Reduce function that also tracks dynamic execution metrics if we want them later
def reduce_graph(root):
    spine = []
    curr = root.resolve()
    
    while curr.is_app:
        spine.append(curr)
        curr = curr.left.resolve()

    if not curr.is_app:
        n_args = len(spine)
        if curr.name == 'I' and n_args >= 1:
            app_node = spine[-1]
            arg = app_node.right.resolve()
            app_node.forward = arg
            return True, 'I'
        elif curr.name == 'K' and n_args >= 2:
            app_node = spine[-2]
            arg_x = spine[-1].right.resolve()
            app_node.forward = arg_x
            return True, 'K'
        elif curr.name == 'S' and n_args >= 3:
            app_node = spine[-3]
            x = spine[-1].right.resolve()
            y = spine[-2].right.resolve()
            z = spine[-3].right.resolve()
            
            new_left = mk_app(x, z)
            new_right = mk_app(y, z)
            new_node = mk_app(new_left, new_right)
            
            app_node.forward = new_node
            return True, 'S'

    for i in range(1, len(spine) + 1):
        app_node = spine[-i]
        arg = app_node.right.resolve()
        reduced, comb = reduce_graph(arg)
        if reduced:
            return True, comb
            
    return False, None

def to_string(node, is_right=False):
    node = node.resolve()
    if not node.is_app: return node.name
    left_str = to_string(node.left, False)
    right_str = to_string(node.right, True)
    res = f"{left_str}{right_str}"
    if is_right: return f"({res})"
    return res

print("Gen,Total_Nodes,S_Nodes,K_Nodes,I_Nodes,App_Nodes,Reduction_Steps,S_Fired,K_Fired,I_Fired,Result")

for gen in range(1, 101):
    MEMO_POOL.clear()
    BUILD_MEMO.clear()
    K_c = get_comb('K')
    S_c = get_comb('S')
    I_c = get_comb('I')
    T = K_c
    F = mk_app(K_c, I_c)
    NOT = mk_app(mk_app(S_c, mk_app(mk_app(S_c, I_c), mk_app(K_c, F))), mk_app(K_c, T))
    
    root = build_center_cell(gen, 0)
    
    # Static Blueprint metrics
    s_nodes, k_nodes, i_nodes, app_nodes = count_combinators()
    total_nodes = len(MEMO_POOL)
    
    # Dynamic Execution metrics
    steps = 0
    s_fired = 0
    k_fired = 0
    i_fired = 0
    
    while True:
        reduced, comb = reduce_graph(root)
        if not reduced: break
        steps += 1
        if comb == 'S': s_fired += 1
        elif comb == 'K': k_fired += 1
        elif comb == 'I': i_fired += 1
            
    res_node = root.resolve()
    res_val = 1 if to_string(res_node) == "K" else 0
    
    print(f"{gen},{total_nodes},{s_nodes},{k_nodes},{i_nodes},{app_nodes},{steps},{s_fired},{k_fired},{i_fired},{res_val}")
