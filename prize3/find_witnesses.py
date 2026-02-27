"""
Find witness configs (as bitmasks) for Essential n k for n=1,2,3,4.
A witness for (n, k) is a config c such that rule30n n c ≠ rule30n n (flipCell c k).
"""

def rule30Local(p, q, r):
    return p ^ (q or r)

def caStep(cells):
    result = []
    for i in range(len(cells) - 2):
        result.append(rule30Local(cells[i], cells[i+1], cells[i+2]))
    return result

def caEvolve(n, cells):
    for _ in range(n):
        cells = caStep(cells)
    return cells

def rule30n(n, cells):
    result = caEvolve(n, list(cells))
    return result[0] if result else False

def configOfMask(n, mask):
    num_cells = 2 * n + 1
    return [(mask >> i) & 1 == 1 for i in range(num_cells)]

def flipCell(cells, k):
    c = list(cells)
    c[k] = not c[k]
    return c

def find_witness(n, k):
    num_cells = 2 * n + 1
    for mask in range(2 ** num_cells):
        c = configOfMask(n, mask)
        c_flip = flipCell(c, k)
        if rule30n(n, c) != rule30n(n, c_flip):
            return mask
    return None

print("Witnesses for Essential n k (mask encoding):")
print(f"{'n':>3} {'k':>3} {'mask':>8} {'binary':>16}  verification")
print("-" * 60)

for n in range(1, 5):
    num_cells = 2 * n + 1
    all_found = True
    for k in range(num_cells):
        mask = find_witness(n, k)
        if mask is None:
            print(f"n={n}, k={k}: NO WITNESS FOUND!")
            all_found = False
        else:
            c = configOfMask(n, mask)
            c_flip = flipCell(c, k)
            r1 = rule30n(n, c)
            r2 = rule30n(n, c_flip)
            binary = format(mask, f'0{num_cells}b')
            print(f"n={n:>1}, k={k:>2}: mask={mask:>5}  {binary:>16}  rule30n={int(r1)} flip_rule30n={int(r2)} ✓")
    print()

