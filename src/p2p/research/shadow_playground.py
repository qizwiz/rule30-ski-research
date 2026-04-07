#!/usr/bin/env python3
"""
Shadow Playground: Interactive REPL for exploring Rule 30 shadow regions.

Commands:
  shadow(n, j)   -- Is (n,j) a shadow? Show dChain values and spike witnesses.
  evolve(n, x)   -- ASCII triangle of Rule 30 evolution from spike at position x.
  coverage(n)    -- All shadows at level n with their witnesses.
  spikes(n, j)   -- For Essential(n,j), which spike positions x work?
  help           -- Show this help.
  quit / exit    -- Exit.
"""

import sys
import re

try:
    import readline  # noqa: F401 — enables arrow-key history in input()
except ImportError:
    pass

# ---------- Rule 30 core ----------

def rule30_local(a, b, c):
    return a ^ (b | c)

def rule30_evolve(config):
    """One step of Rule 30: shrinks tape by 2."""
    return [rule30_local(config[i], config[i+1], config[i+2])
            for i in range(len(config) - 2)]

def rule30_center(T, config):
    """Evolve config (length 2T+1) for T steps, return single center cell."""
    tape = list(config)
    for _ in range(T):
        tape = rule30_evolve(tape)
    return tape[0]

# ---------- dChain ----------

T_MAX = 200
K_MAX = 400

def build_dchain(t_max, k_max):
    D = [[False] * (k_max + 1) for _ in range(t_max + 1)]
    for t in range(t_max + 1):
        D[t][0] = True
    for t in range(1, t_max + 1):
        D[t][1] = not D[t-1][1]
        for k in range(2, k_max + 1):
            D[t][k] = D[t-1][k] ^ (D[t-1][k-1] or D[t-1][k-2])
    return D

print("Pre-computing dChain table...", end=" ", flush=True)
DCHAIN = build_dchain(T_MAX, K_MAX)
print("done.")

def dchain(t, k):
    global DCHAIN, T_MAX, K_MAX
    if t < 0 or k < 0:
        return False
    if t > T_MAX or k > K_MAX:
        T_MAX = max(T_MAX, t)
        K_MAX = max(K_MAX, k)
        DCHAIN = build_dchain(T_MAX, K_MAX)
    return DCHAIN[t][k]

def is_shadow(n, j):
    return not dchain(n + 1, j) and not dchain(n, j)

# ---------- spike configs ----------

def make_spike(T, x):
    """Config of length 2T+1 with a single 1 at position x (0-indexed from left)."""
    width = 2 * T + 1
    cfg = [0] * width
    if 0 <= x < width:
        cfg[x] = 1
    return cfg

def make_flip(config, j):
    """Flip bit at position j."""
    c = list(config)
    c[j] ^= 1
    return c

def test_witness(n, j, x):
    """Does spike at x witness Essential(n+1, j)?"""
    T = n + 1
    width = 2 * T + 1
    if x < 0 or x >= width:
        return False, None, None
    spike = make_spike(T, x)
    flipped = make_flip(spike, j)
    f_spike = rule30_center(T, spike)
    f_flip = rule30_center(T, flipped)
    return f_spike != f_flip, f_spike, f_flip

# ---------- commands ----------

def cmd_shadow(n, j):
    if n < 0:
        print("  n must be >= 0")
        return
    width = 2 * (n + 1) + 1
    if j < 0 or j >= width:
        print(f"  j must be in 0..{width - 1}")
        return

    dc_np1 = dchain(n + 1, j)
    dc_n = dchain(n, j)
    shadow = not dc_np1 and not dc_n

    print(f"  dChain({n+1}, {j}) = {dc_np1}")
    print(f"  dChain({n}, {j})   = {dc_n}")
    print(f"  Shadow: {'YES' if shadow else 'NO'}")

    if shadow:
        rightmost = 2 * (n + 1)
        witnesses = []
        for x_label, x_val in [("rightmost", rightmost), ("x=1", 1), ("x=6", 6)]:
            ok, fs, ff = test_witness(n, j, x_val)
            if ok:
                witnesses.append(f"spike@{x_label}({x_val})")
                print(f"  Witness: spike@{x_label}({x_val})  F(spike)={fs}, F(flip)={ff}")
        if not witnesses:
            print("  Witness: NONE FOUND among {rightmost, 1, 6}")

def cmd_evolve(n, x):
    if n < 1:
        print("  n must be >= 1")
        return
    width = 2 * n + 1
    if x < 0 or x >= width:
        print(f"  x must be in 0..{width - 1}")
        return

    tape = make_spike(n, x)
    rows = [list(tape)]
    for _ in range(n):
        tape = rule30_evolve(tape)
        rows.append(list(tape))

    max_w = len(rows[0])
    for i, row in enumerate(rows):
        pad = (max_w - len(row)) // 2
        line = " " * pad + "".join("\u2588" if c else "\u00b7" for c in row)
        print(f"  {i:3d} | {line}")

def cmd_coverage(n):
    if n < 0:
        print("  n must be >= 0")
        return
    width = 2 * (n + 1) + 1
    rightmost = 2 * (n + 1)
    shadows = []
    for j in range(width):
        if is_shadow(n, j):
            shadows.append(j)

    if not shadows:
        print(f"  No shadows at n={n}")
        return

    print(f"  {len(shadows)} shadow(s) at n={n}:")
    for j in shadows:
        found = []
        for x_label, x_val in [("rightmost", rightmost), ("x=1", 1), ("x=6", 6)]:
            ok, _, _ = test_witness(n, j, x_val)
            if ok:
                found.append(f"{x_label}({x_val})")
        witness_str = ", ".join(found) if found else "NONE"
        print(f"    j={j:3d}  witness: {witness_str}")

def cmd_spikes(n, j):
    if n < 0:
        print("  n must be >= 0")
        return
    T = n + 1
    width = 2 * T + 1
    if j < 0 or j >= width:
        print(f"  j must be in 0..{width - 1}")
        return

    working = []
    for x in range(width):
        ok, _, _ = test_witness(n, j, x)
        if ok:
            working.append(x)

    if working:
        print(f"  {len(working)} witness spike(s) for Essential({T}, {j}):")
        print(f"    positions: {working}")
    else:
        print(f"  NO witnesses found (NOT essential at this level)")

def cmd_help():
    print("""
  shadow(n, j)   Is (n,j) a shadow? Show dChain, witnesses.
  evolve(n, x)   ASCII Rule 30 triangle from spike at x, n steps.
  coverage(n)    All shadows at level n with witnesses.
  spikes(n, j)   Which spike positions witness Essential(n+1, j)?
  help           This message.
  quit / exit    Leave.
""")

# ---------- REPL ----------

DISPATCH = {
    "shadow": (cmd_shadow, 2),
    "evolve": (cmd_evolve, 2),
    "coverage": (cmd_coverage, 1),
    "spikes": (cmd_spikes, 2),
}

def parse_and_run(line):
    line = line.strip()
    if not line:
        return True
    if line in ("quit", "exit", "q"):
        return False
    if line in ("help", "h", "?"):
        cmd_help()
        return True

    # parse: name(arg1, arg2, ...)
    m = re.match(r"(\w+)\s*\(\s*(.*?)\s*\)", line)
    if not m:
        # also try: name arg1 arg2
        parts = line.split()
        if parts[0] in DISPATCH:
            name = parts[0]
            try:
                args = [int(a.strip(",")) for a in parts[1:]]
            except ValueError:
                print(f"  Could not parse arguments: {line}")
                return True
        else:
            print(f"  Unknown command: {line}  (type 'help')")
            return True
    else:
        name = m.group(1)
        try:
            args = [int(a.strip()) for a in m.group(2).split(",")]
        except ValueError:
            print(f"  Could not parse arguments: {line}")
            return True

    if name not in DISPATCH:
        print(f"  Unknown command: {name}  (type 'help')")
        return True

    func, nargs = DISPATCH[name]
    if len(args) != nargs:
        print(f"  {name} expects {nargs} argument(s), got {len(args)}")
        return True

    func(*args)
    return True

def main():
    print("Rule 30 Shadow Playground")
    print("Type 'help' for commands, 'quit' to exit.\n")

    interactive = sys.stdin.isatty()

    while True:
        try:
            if interactive:
                line = input("> ")
            else:
                line = input()
        except (EOFError, KeyboardInterrupt):
            print()
            break
        if not parse_and_run(line):
            break

if __name__ == "__main__":
    main()
