#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""exact_linalg.py — Self-contained pure-Fraction exact LDL^T positivity check,
dyadic rounding, and SDPA-GMP sparse format / result helpers for Thomson N = 11.

Adapted from thomson-n9 (exact.py, sdp_certify.py, typed_ladder.py) with zero float
acceptances in exact routines.
"""
from __future__ import annotations

import math
import re
import subprocess
from fractions import Fraction
from pathlib import Path

F0 = Fraction(0)
F1 = Fraction(1)

PARAM_SDPA = """500\tunsigned int maxIteration;
1.0E-30\tdouble 0.0 < epsilonStar;
1.0E4\tdouble 0.0 < lambdaStar;
2.0\tdouble 1.0 < omegaStar;
-1.0E5\tdouble lowerBound;
1.0E5\tdouble upperBound;
0.1\tdouble 0.0 <= betaStar <  1.0;
0.3\tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;
0.9\tdouble 0.0 < gammaStar <  1.0;
1.0E-30\tdouble 0.0 < epsilonDash;
200\tprecision
"""


class ExactMatrixError(ValueError):
    """Matrix violates exact rational symmetric square preconditions."""


class NotSymmetricError(ExactMatrixError):
    """Matrix is not exactly symmetric."""


class ZeroPivotError(ExactMatrixError):
    """Pivot-free LDL^T encountered a zero pivot."""


def _to_fraction(x) -> Fraction:
    if isinstance(x, float):
        raise ExactMatrixError("float elements are rejected in exact routines; pass int/Fraction/'p/q'")
    try:
        return Fraction(x)
    except (TypeError, ValueError) as exc:
        raise ExactMatrixError(f"cannot convert {x!r} to exact Fraction") from exc


def _as_matrix(A) -> list[list[Fraction]]:
    n = len(A)
    if n == 0:
        raise ExactMatrixError("empty matrix")
    rows = []
    for i, row in enumerate(A):
        if len(row) != n:
            raise ExactMatrixError(f"row {i} length {len(row)} != {n}")
        rows.append([_to_fraction(x) for x in row])
    return rows


def rational_ldlt(A) -> tuple[list[list[Fraction]], list[Fraction]]:
    """Exact pivot-free LDL^T factorization A = L * diag(d) * L^T."""
    rows = _as_matrix(A)
    n = len(rows)
    for i in range(n):
        for j in range(i):
            if rows[i][j] != rows[j][i]:
                raise NotSymmetricError(f"A[{i}][{j}]={rows[i][j]} != A[{j}][{i}]={rows[j][i]}")
    L = [[F1 if i == j else F0 for j in range(n)] for i in range(n)]
    d = [F0] * n
    for j in range(n):
        dj = rows[j][j]
        for k in range(j):
            dj -= L[j][k] * L[j][k] * d[k]
        if dj == 0:
            raise ZeroPivotError(f"zero pivot at index {j}")
        d[j] = dj
        for i in range(j + 1, n):
            lij = rows[i][j]
            for k in range(j):
                lij -= L[i][k] * L[j][k] * d[k]
            L[i][j] = lij / dj
    return L, d


def is_positive_definite(A) -> bool:
    """Exact rational positive-definiteness check via integer Bareiss Sylvester minors."""
    rows = _as_matrix(A)
    n = len(rows)
    for i in range(n):
        for j in range(i):
            if rows[i][j] != rows[j][i]:
                raise NotSymmetricError(f"A[{i}][{j}]={rows[i][j]} != A[{j}][{i}]={rows[j][i]}")
    scale = math.lcm(*(x.denominator for row in rows for x in row))
    M = [[x.numerator * (scale // x.denominator) for x in row] for row in rows]
    prev_pivot = 1
    for k in range(n):
        piv = M[k][k]
        if piv <= 0:
            return False
        mk = M[k]
        for i in range(k + 1, n):
            mi = M[i]
            mik = mi[k]
            for j in range(k + 1, i + 1):
                num = piv * mi[j] - mik * mk[j]
                if prev_pivot == 1:
                    val = num
                else:
                    val, rem = divmod(num, prev_pivot)
                    assert rem == 0, "Bareiss exact division invariant failed"
                mi[j] = val
                M[j][i] = val
        prev_pivot = piv
    return True


def dyad(x, k: int, floor: bool = False) -> Fraction:
    """Round Fraction (or float) to nearest (or floor) 2^-k dyadic rational."""
    if isinstance(x, Fraction):
        n = x * (1 << k)
        if floor:
            p = n.numerator // n.denominator
        else:
            p = (2 * n.numerator + n.denominator) // (2 * n.denominator)
        return Fraction(p, 1 << k)
    q = float(1 << k)
    v = x * q
    p = math.floor(v) if floor else int(round(v))
    return Fraction(p, 1 << k)


def frac_str(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


def frac_dec(f: Fraction, digits: int = 40) -> str:
    num, den = f.numerator, f.denominator
    sign = "-" if num < 0 else ""
    num = abs(num)
    ip, rem = divmod(num, den)
    out = []
    for _ in range(digits):
        if rem == 0:
            break
        rem *= 10
        d, rem = divmod(rem, den)
        out.append(str(d))
    if not out:
        return f"{sign}{ip}.0"
    return f"{sign}{ip}.{''.join(out)}"


def ceil_sqrt_rat(q: Fraction, bits: int = 80) -> Fraction:
    """Strict rational upper bound >= sqrt(q) for q >= 0."""
    if q < 0:
        raise ValueError(f"ceil_sqrt_rat requires q >= 0, got {q}")
    num = q.numerator * (1 << (2 * bits))
    den = q.denominator
    q_int = (num + den - 1) // den
    r = math.isqrt(q_int)
    while r * r * den < num:
        r += 1
    assert r * r * den >= num
    return Fraction(r, 1 << bits)


def repair_psd_fine(Mfr: list[list[Fraction]], k_bits: int) -> tuple[list[list[Fraction]], Fraction]:
    """Exact pivot-free LDL^T PD check & minimal dyadic diagonal shift starting at 2^-k_bits."""
    if is_positive_definite(Mfr):
        return Mfr, F0
    n = len(Mfr)
    delta = Fraction(1, 1 << k_bits)
    for _ in range(k_bits + 10):
        out = [[Mfr[i][j] + (delta if i == j else F0) for j in range(n)] for i in range(n)]
        if is_positive_definite(out):
            return out, delta
        delta *= 2
    raise RuntimeError("repair_psd_fine failed to make matrix strictly PD")


def parse_sdpa_result(path: Path) -> dict:
    """Parse SDPA-GMP .result file (yMat holds our primal X blocks in SDPA convention)."""
    text = path.read_text()

    def grab(pat, flags=0):
        m = re.search(pat, text, flags)
        return m.group(1) if m else None

    info = dict(
        phase_value=grab(r"phase\.value = (\S+)"),
        iteration=int(grab(r"Iteration = (\d+)") or -1),
        mu=float(grab(r"mu = ([0-9.eE+-]+)") or "nan"),
        relative_gap=float(grab(r"relative gap = ([0-9.eE+-]+)") or "nan"),
        p_feas_error=grab(r"p\.feas\.error = ([0-9.eE+-]+)"),
        d_feas_error=grab(r"d\.feas\.error = ([0-9.eE+-]+)"),
        obj_primal=grab(r"objValPrimal = ([0-9.eE+-]+)"),
        obj_dual=grab(r"objValDual = ([0-9.eE+-]+)"),
    )
    mm = re.search(r"yMat = \s*\n\{\n(.*)\n\}", text, re.S)
    if mm is None:
        raise RuntimeError(f"yMat section not found in {path}")
    body = mm.group(1)
    groups, depth, start = [], 0, None
    for idx, ch in enumerate(body):
        if ch == "{":
            if depth == 0:
                start = idx
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(body[start:idx + 1])
                start = None
    if not groups:
        raise RuntimeError("Empty yMat top-level groups")
    lp_str = groups[0]
    if "{" in lp_str[1:-1]:
        raise RuntimeError("First yMat group is not a flat LP block")
    lp_vals = [s for s in re.split(r"[{},\s]+", lp_str[1:-1]) if s]
    sdp = []
    for g in groups[1:]:
        rows = re.findall(r"\{([^{}]*)\}", g)
        if not rows:
            raise RuntimeError("Empty SDP block rows in yMat")
        sdp.append([[x for x in re.split(r"[,\s]+", r_) if x] for r_ in rows])
    return dict(info=info, lp=[Fraction(s) for s in lp_vals], sdp=sdp)


def parse_sdpa_xVec(path: Path) -> list[Fraction]:
    """Parse SDPA-GMP dual moment vector xVec (useful for diagnosing primal/moment relaxations!)."""
    text = path.read_text()
    mm = re.search(r"xVec = \s*\n\{([^{}]*)\}", text, re.S)
    if mm is None:
        return []
    vals = [s for s in re.split(r"[,\s]+", mm.group(1)) if s]
    return [Fraction(s) for s in vals]


def code_version(repo: Path) -> str:
    try:
        return subprocess.check_output(
            ["git", "describe", "--always", "--dirty"], cwd=str(repo),
            text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unknown(non-git)"
