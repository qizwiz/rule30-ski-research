"""
shadow_api.py — Pure function library for Rule 30 shadow region analysis.

Shadow(n, j): dChain(n+1, j) = False AND dChain(n, j) = False
dChain recurrence: dChain(t, 0) = True; dChain(0, k>=1) = False;
  dChain(t+1, k+2) = rule30Local(dChain(t, k+2), dChain(t, k+1), dChain(t, k))
rule30Local(a, b, c) = a XOR (b OR c)
"""

from __future__ import annotations

# ---------- Rule 30 core ----------

def _rule30_local(a: int, b: int, c: int) -> int:
    return a ^ (b | c)


def _rule30_evolve(config: list[int]) -> list[int]:
    return [_rule30_local(config[i], config[i + 1], config[i + 2])
            for i in range(len(config) - 2)]


def _rule30_center(steps: int, config: list[int]) -> int:
    tape = list(config)
    for _ in range(steps):
        tape = _rule30_evolve(tape)
    return tape[0]


# ---------- dChain table ----------

_T_MAX = 200
_K_MAX = 400
_DCHAIN: list[list[bool]] = []


def _build_dchain(t_max: int, k_max: int) -> list[list[bool]]:
    D = [[False] * (k_max + 1) for _ in range(t_max + 1)]
    for t in range(t_max + 1):
        D[t][0] = True
    for t in range(1, t_max + 1):
        D[t][1] = not D[t - 1][1]
        for k in range(2, k_max + 1):
            D[t][k] = D[t - 1][k] ^ (D[t - 1][k - 1] or D[t - 1][k - 2])
    return D


def _ensure_dchain(t: int, k: int) -> None:
    global _T_MAX, _K_MAX, _DCHAIN
    if t > _T_MAX or k > _K_MAX:
        _T_MAX = max(_T_MAX, t)
        _K_MAX = max(_K_MAX, k)
        _DCHAIN = _build_dchain(_T_MAX, _K_MAX)


# Pre-compute at import time
_DCHAIN = _build_dchain(_T_MAX, _K_MAX)


# ---------- Public API ----------

def dchain_value(t: int, k: int) -> bool:
    """Raw dChain(t, k) value."""
    if t < 0 or k < 0:
        return False
    _ensure_dchain(t, k)
    return _DCHAIN[t][k]


def is_shadow(n: int, j: int) -> bool:
    """True if dChain(n+1, j) = False AND dChain(n, j) = False."""
    return not dchain_value(n + 1, j) and not dchain_value(n, j)


def _make_spike(T: int, x: int) -> list[int]:
    width = 2 * T + 1
    cfg = [0] * width
    if 0 <= x < width:
        cfg[x] = 1
    return cfg


def _test_spike_raw(n: int, j: int, x: int) -> tuple[bool, int, int]:
    """Test if spike@x witnesses Essential(n+1, j). Returns (witnesses, f_spike, f_flip)."""
    T = n + 1
    width = 2 * T + 1
    if x < 0 or x >= width:
        return False, 0, 0
    spike = _make_spike(T, x)
    flipped = list(spike)
    flipped[j] ^= 1
    f_spike = _rule30_center(T, spike)
    f_flip = _rule30_center(T, flipped)
    return f_spike != f_flip, f_spike, f_flip


def test_spike(n: int, j: int, x: int) -> dict:
    """Does spike@x witness Essential(n+1, j)?

    Returns: {'witnesses': bool, 'f_spike': int, 'f_flip': int, 'level': int}
    """
    ok, f_spike, f_flip = _test_spike_raw(n, j, x)
    return {
        "witnesses": ok,
        "f_spike": f_spike,
        "f_flip": f_flip,
        "level": n + 1,
    }


def _find_witnesses(n: int, j: int) -> list[dict]:
    """Find witnesses for a shadow at (n, j). Try canonical spikes first, then brute-force."""
    T = n + 1
    width = 2 * T + 1
    rightmost = 2 * T

    candidates = [
        (rightmost, "rightmost"),
        (1, "x=1"),
        (6, "x=6"),
    ]

    witnesses = []
    for x_val, label in candidates:
        if x_val >= width:
            continue
        ok, f_spike, f_flip = _test_spike_raw(n, j, x_val)
        if ok:
            witnesses.append({
                "x": x_val,
                "label": label,
                "f_spike": f_spike,
                "f_flip": f_flip,
            })

    if not witnesses:
        for x in range(width):
            if x in (rightmost, 1, 6):
                continue
            ok, f_spike, f_flip = _test_spike_raw(n, j, x)
            if ok:
                witnesses.append({
                    "x": x,
                    "label": f"x={x}",
                    "f_spike": f_spike,
                    "f_flip": f_flip,
                })
                break  # one fallback witness suffices

    return witnesses


def query_shadow(n: int, j: int) -> dict:
    """Query shadow status at (n, j).

    Returns: {
        'is_shadow': bool,
        'dchain_n1': bool,
        'dchain_n': bool,
        'witnesses': list  -- populated only if is_shadow=True
    }
    """
    dc_n1 = dchain_value(n + 1, j)
    dc_n = dchain_value(n, j)
    shadow = not dc_n1 and not dc_n

    return {
        "is_shadow": shadow,
        "dchain_n1": dc_n1,
        "dchain_n": dc_n,
        "witnesses": _find_witnesses(n, j) if shadow else [],
    }


def scan_shadows(n: int) -> list[dict]:
    """All shadows at level n. Returns list of query_shadow results (is_shadow=True only)."""
    width = 2 * (n + 1) + 1
    results = []
    for j in range(width):
        dc_n1 = dchain_value(n + 1, j)
        dc_n = dchain_value(n, j)
        if not dc_n1 and not dc_n:
            results.append({
                "is_shadow": True,
                "dchain_n1": dc_n1,
                "dchain_n": dc_n,
                "witnesses": _find_witnesses(n, j),
            })
    return results


def evolve_ascii(n: int, x: int, width: int | None = None) -> str:
    """ASCII triangle of Rule 30 evolution from spike at x for n steps.

    Uses '\u2588' for 1, '\u00b7' for 0. Center-pads each row.
    """
    if n < 1:
        return ""
    if width is None:
        width = 2 * n + 1
    if x < 0 or x >= width:
        return f"x={x} out of range 0..{width - 1}"

    cfg = [0] * width
    cfg[x] = 1
    tape = list(cfg)
    rows = [list(tape)]
    for _ in range(n):
        tape = _rule30_evolve(tape)
        rows.append(list(tape))

    max_w = len(rows[0])
    lines = []
    for i, row in enumerate(rows):
        pad = (max_w - len(row)) // 2
        line = " " * pad + "".join("\u2588" if c else "\u00b7" for c in row)
        lines.append(f"{i:3d} | {line}")
    return "\n".join(lines)


def verify_coverage(n_max: int) -> dict:
    """Do {rightmost, x=1, x=6} cover ALL shadows for n in 0..n_max?

    Returns: {'covered': int, 'uncovered': int, 'coverage_pct': float,
              'uncovered_list': [(n, j)]}
    """
    covered = 0
    uncovered_list = []

    for n in range(n_max + 1):
        width = 2 * (n + 1) + 1
        rightmost = 2 * (n + 1)
        for j in range(width):
            if not is_shadow(n, j):
                continue
            found = False
            for x_val in (rightmost, 1, 6):
                if x_val >= width:
                    continue
                ok, _, _ = _test_spike_raw(n, j, x_val)
                if ok:
                    found = True
                    break
            if found:
                covered += 1
            else:
                uncovered_list.append((n, j))

    total = covered + len(uncovered_list)
    return {
        "covered": covered,
        "uncovered": len(uncovered_list),
        "coverage_pct": 100.0 * covered / total if total > 0 else 100.0,
        "uncovered_list": uncovered_list,
    }
