import sys
sys.setrecursionlimit(100000)

# Global Hash Consing Table
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

# --- Graph Reduction ---
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
            return True
            
        elif curr.name == 'K' and n_args >= 2:
            app_node = spine[-2]
            arg_x = spine[-1].right.resolve()
            app_node.forward = arg_x
            return True
            
        elif curr.name == 'S' and n_args >= 3:
            app_node = spine[-3]
            x = spine[-1].right.resolve()
            y = spine[-2].right.resolve()
            z = spine[-3].right.resolve()
            
            new_left = mk_app(x, z)
            new_right = mk_app(y, z)
            new_node = mk_app(new_left, new_right)
            
            app_node.forward = new_node
            return True

    for i in range(1, len(spine) + 1):
        app_node = spine[-i]
        arg = app_node.right.resolve()
        if reduce_graph(arg):
            return True
            
    return False

def to_string(node, is_right=False):
    node = node.resolve()
    if not node.is_app: return node.name
    left_str = to_string(node.left, False)
    right_str = to_string(node.right, True)
    res = f"{left_str}{right_str}"
    if is_right: return f"({res})"
    return res

K_c = get_comb('K')
S_c = get_comb('S')
I_c = get_comb('I')
T = K_c
F = mk_app(K_c, I_c)
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

print("gen,nodes,steps,result")
for gen in range(1, 51):
    MEMO_POOL.clear()
    BUILD_MEMO.clear()
    K_c = get_comb('K')
    S_c = get_comb('S')
    I_c = get_comb('I')
    T = K_c
    F = mk_app(K_c, I_c)
    NOT = mk_app(mk_app(S_c, mk_app(mk_app(S_c, I_c), mk_app(K_c, F))), mk_app(K_c, T))
    
    root = build_center_cell(gen, 0)
    
    steps = 0
    while reduce_graph(root):
        steps += 1
            
    res_node = root.resolve()
    res_val = 1 if to_string(res_node) == "K" else 0
    print(f"{gen},{len(MEMO_POOL)},{steps},{res_val}")
