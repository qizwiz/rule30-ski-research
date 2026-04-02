#!/usr/bin/env python3
"""Verify right-edge period-8 claims using the CORRECT shrinking CA (caStep).

The Lean `caEvolve` function uses `caStep` which shrinks the tape by 2 per step:
  caStep [a, b, c, ...] = [R30(a,b,c), R30(b,c,d), ...]
  
This is NOT the same as the standard fixed-size CA in verify_lean_claim.py.
"""

def rule30_local(p, q, r):
    return p ^ (q | r)

def caStep(tape):
    """Lean's caStep: shrinking CA, reduces length by 2."""
    if len(tape) < 3:
        return []
    return [rule30_local(tape[i], tape[i+1], tape[i+2]) for i in range(len(tape) - 2)]

def caEvolve(T, tape):
    """Lean's caEvolve: iterate caStep T times."""
    for _ in range(T):
        tape = caStep(tape)
    return tape

def rightEdgeF(k, T):
    w = 2*T - k
    tape = [i == w for i in range(2*T+1)]
    result = caEvolve(T, tape)
    return result[0] if result else False

def rightEdgeG(k, m, T):
    w = 2*T - k
    tape = [i == m or i == w for i in range(2*T+1)]
    result = caEvolve(T, tape)
    return result[0] if result else False

def main():
    import sys
    
    # Verify period-8 for F and G with k=10, m=4
    print("=== Right-edge period-8 verification (shrinking CA) ===\n")
    
    T_start, T_end = 100, 500
    fails_F, fails_G = [], []
    for T in range(T_start, T_end):
        if rightEdgeF(10, T+8) != rightEdgeF(10, T):
            fails_F.append(T)
        if rightEdgeG(10, 4, T+8) != rightEdgeG(10, 4, T):
            fails_G.append(T)
    
    print(f"F period-8 in [{T_start}, {T_end}): {'PASS' if not fails_F else 'FAIL at ' + str(fails_F[:10])}")
    print(f"G period-8 in [{T_start}, {T_end}): {'PASS' if not fails_G else 'FAIL at ' + str(fails_G[:10])}")
    
    # Verify sensitivity at SubcaseB positions (T ≡ 6 mod 8)
    sens_fails = []
    for T in range(T_start, T_end):
        if T % 8 == 6:
            f = rightEdgeF(10, T)
            g = rightEdgeG(10, 4, T)
            if f == g:
                sens_fails.append(T)
    
    print(f"Sensitivity at T≡6 mod 8 in [{T_start}, {T_end}): {'PASS' if not sens_fails else 'FAIL at ' + str(sens_fails[:10])}")
    
    # Base case verification
    f3094 = rightEdgeF(10, 3094)
    g3094 = rightEdgeG(10, 4, 3094)
    print(f"\nBase case T=3094: F={int(f3094)}, G={int(g3094)}, sens={f3094 != g3094}")
    
    # Show period pattern
    print(f"\nPeriod pattern (T=100..107):")
    for T in range(100, 108):
        f = rightEdgeF(10, T)
        g = rightEdgeG(10, 4, T)
        print(f"  T={T} (mod8={T%8}): F={int(f)}, G={int(g)}, sens={int(f != g)}")
    
    if not fails_F and not fails_G and not sens_fails:
        print("\n✓ All checks passed")
        sys.exit(0)
    else:
        print("\n✗ Some checks failed")
        sys.exit(1)

if __name__ == "__main__":
    main()
