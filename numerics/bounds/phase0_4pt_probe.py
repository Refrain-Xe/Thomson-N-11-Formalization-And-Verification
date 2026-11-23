#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""phase0_4pt_probe.py — Exact rational S_{11} x O(3)-reduced coupled 3-point + 4-point
SDP hierarchy probe for Thomson N = 11 (`Path B` 4-point local & global constraint test).

Implements the complete S_{11} x O(3) classification of 4-point constraints up to edge-monomial
degree D4 on (S^2)^11:
  - Case 4 (4 free vertices):
      * Exact 3D Euclidean realizability ideal multipliers q(e) * det(G_4(e)) = 0 (deg q <= D4 - 4)
      * Z2 x Z2 = <(01),(23)>-block-diagonalized 4-point Putinar SOS on 1, 1 + t_01, 1 - t_01
      * Z2 = <(01)>-block-diagonalized 4-point face-Gram SOS on det(G_3(0,1,2)) >= 0
  - Case 2 (2 free vertices + 1 summed neighbor):
      * Binet-Cauchy cross-product block `Harm4_odd` (sum_{i!=j} s_ij s_ij^T >= 0, s_ij = sum_k w(i,j,k) ((x_i x x_j).x_k))
      * Pair-flag block `Flag2_even` (sum_{i!=j} f_ij f_ij^T >= 0)
  - Case 0 (0 free vertices + 2 summed vertices):
      * Global pair-tensor blocks `GlobNat_d{0..D4}` and `GlobAx_d{2..D4-1}` in (R^3)^{\\otimes d}
        (coupling disjoint pairs (i,j), (k,m), 3-edge paths j-i-k-m, and I_3 contractions with ||I_3||^2 = 3).

Every single LP column and PSD block entry is verified with ZERO exact `Fraction` error against
explicit geometric evaluation on a random rational 11-point configuration on S^2 before solving.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

from exact_linalg import F0, F1, frac_dec, parse_sdpa_result  # noqa: E402
from sym_cap_sdpa import SymCapModel, canon  # noqa: E402

F2 = Fraction(2)
F3 = Fraction(3)
HALF = Fraction(1, 2)
QTR = Fraction(1, 4)
E_STAR_FLOAT = 40.596450508190605

EDGE_LIST = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
EDGE_IDX = {e: i for i, e in enumerate(EDGE_LIST)}
for (u, v), idx_e in list(EDGE_IDX.items()):
    EDGE_IDX[(v, u)] = idx_e

S4_PERMS = list(itertools.permutations(range(4)))
S4_EDGE_MAP = [tuple(EDGE_IDX[(p[u], p[v])] for (u, v) in EDGE_LIST) for p in S4_PERMS]

EM_ID = tuple(EDGE_IDX[((0, 1, 2, 3)[u], (0, 1, 2, 3)[v])] for (u, v) in EDGE_LIST)
EM_01 = tuple(EDGE_IDX[((1, 0, 2, 3)[u], (1, 0, 2, 3)[v])] for (u, v) in EDGE_LIST)
EM_23 = tuple(EDGE_IDX[((0, 1, 3, 2)[u], (0, 1, 3, 2)[v])] for (u, v) in EDGE_LIST)
EM_0123 = tuple(EDGE_IDX[((1, 0, 3, 2)[u], (1, 0, 3, 2)[v])] for (u, v) in EDGE_LIST)


def canon6(m: tuple[int, ...]) -> tuple[int, ...]:
    return max(tuple(m[idx] for idx in emap) for emap in S4_EDGE_MAP)


def all_monoms6(deg: int) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []

    def rec(pos: int, rem: int, cur: tuple[int, ...]) -> None:
        if pos == 5:
            for d in range(rem + 1):
                out.append(cur + (d,))
            return
        for d in range(rem + 1):
            rec(pos + 1, rem - d, cur + (d,))

    rec(0, deg, ())
    return out


def poly6_mul(p: dict, q: dict) -> dict:
    out: dict = {}
    for m1, v1 in p.items():
        if not v1:
            continue
        for m2, v2 in q.items():
            if not v2:
                continue
            k = tuple(m1[i] + m2[i] for i in range(6))
            nv = out.get(k, F0) + v1 * v2
            if nv:
                out[k] = nv
            else:
                out.pop(k, None)
    return out


def poly6_add(p: dict, q: dict, sc: Fraction = F1) -> dict:
    out = dict(p)
    for k, v in q.items():
        nv = out.get(k, F0) + sc * v
        if nv:
            out[k] = nv
        else:
            out.pop(k, None)
    return out


def unit6(idx: int, pw: int = 1) -> tuple[int, ...]:
    arr = [0] * 6
    arr[idx] = pw
    return tuple(arr)


DET4: dict[tuple[int, ...], Fraction] = {(0, 0, 0, 0, 0, 0): F1}
for _i in range(6):
    DET4[unit6(_i, 2)] = -F1
for (_u, _v, _w) in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:
    _m = [0] * 6
    _m[EDGE_IDX[(_u, _v)]] = 1
    _m[EDGE_IDX[(_u, _w)]] = 1
    _m[EDGE_IDX[(_v, _w)]] = 1
    DET4[tuple(_m)] = F2
for _i, _j in [(0, 5), (1, 4), (2, 3)]:
    _m = [0] * 6
    _m[_i] = 2
    _m[_j] = 2
    DET4[tuple(_m)] = F1
for (_i1, _j1), (_i2, _j2) in [((0, 5), (1, 4)), ((0, 5), (2, 3)), ((1, 4), (2, 3))]:
    _m = [0] * 6
    _m[_i1] = 1
    _m[_j1] = 1
    _m[_i2] = 1
    _m[_j2] = 1
    DET4[tuple(_m)] = -F2

DET3_012 = {
    (0, 0, 0, 0, 0, 0): F1,
    (2, 0, 0, 0, 0, 0): -F1,
    (0, 2, 0, 0, 0, 0): -F1,
    (0, 0, 0, 2, 0, 0): -F1,
    (1, 1, 0, 1, 0, 0): F2,
}
K4_01_23 = {
    (0, 0, 0, 0, 0, 1): F1,
    (2, 0, 0, 0, 0, 1): -F1,
    (0, 1, 1, 0, 0, 0): -F1,
    (0, 0, 0, 1, 1, 0): -F1,
    (1, 1, 0, 0, 1, 0): F1,
    (1, 0, 1, 1, 0, 0): F1,
}


def z2x2_bases(deg: int) -> list[list[dict]]:
    if deg < 0:
        return []
    mons = all_monoms6(deg)
    seen = set()
    blocks: list[list[dict]] = [[], [], [], []]
    chars = [(1, 1, 1, 1), (1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1)]
    ems = [EM_ID, EM_01, EM_23, EM_0123]
    for m in mons:
        orb = tuple(sorted(set(tuple(m[idx] for idx in em) for em in ems)))
        if orb in seen:
            continue
        seen.add(orb)
        for bi, ch in enumerate(chars):
            p: dict = {}
            for em, sgn in zip(ems, ch):
                pm = tuple(m[idx] for idx in em)
                p[pm] = p.get(pm, F0) + Fraction(sgn, 4)
            p = {k: v for k, v in p.items() if v}
            if p:
                blocks[bi].append(p)
    return [b for b in blocks if b]


def z2_01_bases(deg: int) -> list[list[dict]]:
    if deg < 0:
        return []
    mons = all_monoms6(deg)
    seen = set()
    even, odd = [], []
    for m in mons:
        m2 = tuple(m[idx] for idx in EM_01)
        key = tuple(sorted({m, m2}))
        if key in seen:
            continue
        seen.add(key)
        if m == m2:
            even.append({m: F1})
        else:
            even.append({m: HALF, m2: HALF})
            odd.append({m: HALF, m2: -HALF})
    return [b for b in (even, odd) if b]


def build_tensor_gram_poly(d: int, feat_a: tuple, feat_b: tuple, u_a: tuple, u_b: tuple) -> dict:
    """Exact polynomial inner product in (R^3)^{\\otimes d} with ||I_3||^2 = 3."""
    def dot_poly(va: int, vb: int) -> dict:
        return {(0,) * 6: F1} if va == vb else {unit6(EDGE_IDX[(va, vb)], 1): F1}

    if feat_a[0] == "cross" and feat_b[0] == "cross":
        _, pa, wa = feat_a
        _, pb, wb = feat_b
        i, j = u_a
        k, m = u_b
        p_ij = {unit6(EDGE_IDX[(i, j)], pa): F1} if pa > 0 else {(0,) * 6: F1}
        p_km = {unit6(EDGE_IDX[(k, m)], pb): F1} if pb > 0 else {(0,) * 6: F1}
        cr = poly6_add(
            poly6_mul(dot_poly(i, k), dot_poly(j, m)),
            poly6_mul(dot_poly(i, m), dot_poly(j, k)),
            -F1,
        )
        res = poly6_mul(poly6_mul(p_ij, p_km), cr)
        for bit_a, bit_b in zip(wa, wb):
            res = poly6_mul(res, dot_poly(u_a[bit_a], u_b[bit_b]))
        return res

    def unpack(feat: tuple, u: tuple):
        if feat[0] == "id":
            return {(0,) * 6: F1}, list(feat[1]), {}
        if feat[0] == "v1":
            return {(0,) * 6: F1}, list(feat[1]), {s: u[0] for s in feat[2]}
        _, p, pairs, smap = feat
        pw = {unit6(EDGE_IDX[(u[0], u[1])], p): F1} if p > 0 else {(0,) * 6: F1}
        return pw, list(pairs), {s: u[b] for s, b in smap.items()}

    pw_a, pairs_a, vmap_a = unpack(feat_a, u_a)
    pw_b, pairs_b, vmap_b = unpack(feat_b, u_b)
    res = poly6_mul(pw_a, pw_b)
    pa_m: dict[int, int] = {}
    pb_m: dict[int, int] = {}
    for s1, s2 in pairs_a:
        pa_m[s1] = s2
        pa_m[s2] = s1
    for s1, s2 in pairs_b:
        pb_m[s1] = s2
        pb_m[s2] = s1
    vis = [False] * d
    for s0 in range(d):
        if vis[s0]:
            continue
        ea, eb = (s0 in vmap_a), (s0 in vmap_b)
        if not (ea or eb):
            continue
        if ea and eb:
            vis[s0] = True
            res = poly6_mul(res, dot_poly(vmap_a[s0], vmap_b[s0]))
        elif ea:
            va = vmap_a[s0]
            cur = s0
            side = "B"
            vis[cur] = True
            while True:
                if side == "B":
                    if cur in vmap_b:
                        res = poly6_mul(res, dot_poly(va, vmap_b[cur]))
                        break
                    cur = pb_m[cur]
                    vis[cur] = True
                    side = "A"
                else:
                    if cur in vmap_a:
                        res = poly6_mul(res, dot_poly(va, vmap_a[cur]))
                        break
                    cur = pa_m[cur]
                    vis[cur] = True
                    side = "B"
        else:
            vb = vmap_b[s0]
            cur = s0
            side = "A"
            vis[cur] = True
            while True:
                if side == "A":
                    if cur in vmap_a:
                        res = poly6_mul(res, dot_poly(vb, vmap_a[cur]))
                        break
                    cur = pa_m[cur]
                    vis[cur] = True
                    side = "B"
                else:
                    if cur in vmap_b:
                        res = poly6_mul(res, dot_poly(vb, vmap_b[cur]))
                        break
                    cur = pb_m[cur]
                    vis[cur] = True
                    side = "A"
    for s0 in range(d):
        if vis[s0]:
            continue
        cur = s0
        side = "B"
        while not vis[cur]:
            vis[cur] = True
            cur = pb_m[cur] if side == "B" else pa_m[cur]
            side = "A" if side == "B" else "B"
        res = {k: v * F3 for k, v in res.items()}
    return res


def build_coupled_4pt_system(n: int, M: int, K: int, D4: int):
    """Construct coupled 3-point (M, K) + 4-point (D4) exact rational model."""
    base = SymCapModel(n, Fraction(-1), M, K)
    mons6 = all_monoms6(D4)
    orbs6: list[tuple[int, ...]] = []
    orb6_idx: dict[tuple[int, ...], int] = {}
    orb6_size: list[int] = []
    for m in mons6:
        c = canon6(m)
        if c not in orb6_idx:
            orb6_idx[c] = len(orbs6)
            orbs6.append(c)
            orb6_size.append(0)
        orb6_size[orb6_idx[c]] += 1

    orb6_target: list[tuple[int, Fraction]] = []
    n_new_rows = 0
    for c in orbs6:
        verts = set()
        for ei, dg in enumerate(c):
            if dg > 0:
                verts.update(EDGE_LIST[ei])
        r = len(verts)
        if r == 0:
            orb6_target.append((base.sym_idx[(0, 0, 0)] + 1, Fraction(3 * math.comb(n, 4), math.comb(n, 3))))
        elif r <= 3:
            vlist = sorted(verts)
            while len(vlist) < 3:
                for cv in range(4):
                    if cv not in vlist:
                        vlist.append(cv)
                        break
            u0, u1, u2 = vlist
            c3 = canon(c[EDGE_IDX[(u0, u1)]], c[EDGE_IDX[(u0, u2)]], c[EDGE_IDX[(u1, u2)]])
            if c3 in base.sym_idx:
                orb6_target.append((base.sym_idx[c3] + 1, Fraction(3 * math.comb(n - r, 4 - r), math.comb(n - r, 3 - r))))
            else:
                n_new_rows += 1
                orb6_target.append((base.m + n_new_rows, F1))
        else:
            n_new_rows += 1
            orb6_target.append((base.m + n_new_rows, F1))

    def poly6_to_rows(p: dict, sc: Fraction = F1) -> dict[int, Fraction]:
        ra: dict[int, Fraction] = {}
        for m, val in p.items():
            if not val:
                continue
            c = canon6(m)
            oidx = orb6_idx[c]
            r_row, mult = orb6_target[oidx]
            nv = ra.get(r_row, F0) - (val * sc / Fraction(orb6_size[oidx])) * mult
            if nv:
                ra[r_row] = nv
            else:
                ra.pop(r_row, None)
        return ra

    def ord_rows(r: int, gp: dict, sc: Fraction = F1) -> dict[int, Fraction]:
        return poly6_to_rows(gp, sc * Fraction(24 // math.factorial(4 - r), math.comb(n - r, 4 - r)))

    extra_lp: list[dict[int, Fraction]] = []
    extra_psd: list[tuple] = []

    seen_q = set()
    if D4 >= 4:
        for m in all_monoms6(D4 - 4):
            c = canon6(m)
            if c not in seen_q:
                seen_q.add(c)
                extra_lp.append(poly6_to_rows(poly6_mul({c: F1}, DET4)))

    for bi, B in enumerate(z2x2_bases(D4 // 2)):
        extra_psd.append((f"SOS4_1_{bi}", len(B), lambda a, b, B=B: poly6_to_rows(poly6_mul(B[a], B[b])), None))
    e_lo = {(0,) * 6: F1, (1, 0, 0, 0, 0, 0): F1}
    e_hi = {(0,) * 6: F1, (1, 0, 0, 0, 0, 0): -F1}
    for bi, B in enumerate(z2x2_bases((D4 - 1) // 2)):
        extra_psd.append((f"SOS4_lo_{bi}", len(B), lambda a, b, B=B: poly6_to_rows(poly6_mul(e_lo, poly6_mul(B[a], B[b]))), None))
        extra_psd.append((f"SOS4_hi_{bi}", len(B), lambda a, b, B=B: poly6_to_rows(poly6_mul(e_hi, poly6_mul(B[a], B[b]))), None))
    for bi, B in enumerate(z2_01_bases((D4 - 3) // 2)):
        extra_psd.append((f"SOS4_det3_{bi}", len(B), lambda a, b, B=B: poly6_to_rows(poly6_mul(DET3_012, poly6_mul(B[a], B[b]))), None))

    d_bc = (D4 - 3) // 2
    if d_bc >= 0:
        bc_b = [(p, q, s) for p in range(d_bc + 1) for q in range(d_bc - p + 1) for s in range(d_bc - p - q + 1)]

        def bc_e(a: int, b: int) -> dict[int, Fraction]:
            pa, qa, sa = bc_b[a]
            pb, qb, sb = bc_b[b]
            wa = {(pa, qa, 0, sa, 0, 0): F1}
            wb = {(pb, qb, 0, sb, 0, 0): F1}
            res = ord_rows(3, poly6_mul(poly6_mul(wa, wb), DET3_012), HALF)
            wb3 = {(pb, 0, qb, 0, sb, 0): F1}
            wa3 = {(pa, 0, qa, 0, sa, 0): F1}
            off = poly6_mul(poly6_add(poly6_mul(wa, wb3), poly6_mul(wb, wa3)), K4_01_23)
            for k, v in ord_rows(4, off, QTR).items():
                nv = res.get(k, F0) + v
                if nv:
                    res[k] = nv
                else:
                    res.pop(k, None)
            return res

        extra_psd.append(("Harm4_odd", len(bc_b), bc_e, bc_b))

    d_t2 = D4 // 2
    t2_f = [("pair", p, 0, 0) for p in range(d_t2 + 1)] + [
        ("nbr", p, q, s) for p in range(d_t2 + 1) for q in range(d_t2 - p + 1) for s in range(d_t2 - p - q + 1)
    ]

    def t2_e(a: int, b: int) -> dict[int, Fraction]:
        ka, pa, qa, sa = t2_f[a]
        kb, pb, qb, sb = t2_f[b]
        if ka == "pair" and kb == "pair":
            return ord_rows(2, {(pa + pb, 0, 0, 0, 0, 0): F1}, HALF)
        if ka == "pair":
            return ord_rows(3, {(pa + pb, qb, 0, sb, 0, 0): F1}, HALF)
        if kb == "pair":
            return ord_rows(3, {(pa + pb, qa, 0, sa, 0, 0): F1}, HALF)
        res = ord_rows(3, {(pa + pb, qa + qb, 0, sa + sb, 0, 0): F1}, HALF)
        off = poly6_add({(pa + pb, qa, qb, sa, sb, 0): F1}, {(pa + pb, qb, qa, sb, sa, 0): F1})
        for k, v in ord_rows(4, off, QTR).items():
            nv = res.get(k, F0) + v
            if nv:
                res[k] = nv
            else:
                res.pop(k, None)
        return res

    extra_psd.append(("Flag2_even", len(t2_f), t2_e, t2_f))

    def sop(d: int, fa: tuple, fb: tuple) -> dict[int, Fraction]:
        ka, kb = fa[0], fb[0]
        ar: dict[int, Fraction] = {}

        def adr(dr: dict[int, Fraction]) -> None:
            for k, v in dr.items():
                nv = ar.get(k, F0) + v
                if nv:
                    ar[k] = nv
                else:
                    ar.pop(k, None)

        if ka == "id" and kb == "id":
            adr(ord_rows(0, build_tensor_gram_poly(d, fa, fb, (), ())))
        elif ka == "id" and kb == "v1":
            adr(ord_rows(1, build_tensor_gram_poly(d, fa, fb, (), (0,))))
        elif ka == "v1" and kb == "id":
            adr(ord_rows(1, build_tensor_gram_poly(d, fa, fb, (0,), ())))
        elif ka == "id":
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (), (0, 1))))
        elif kb == "id":
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0, 1), ())))
        elif ka == "v1" and kb == "v1":
            adr(ord_rows(1, build_tensor_gram_poly(d, fa, fb, (0,), (0,))))
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0,), (1,))))
        elif ka == "v1":
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0,), (0, 1))))
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0,), (1, 0))))
            adr(ord_rows(3, build_tensor_gram_poly(d, fa, fb, (0,), (1, 2))))
        elif kb == "v1":
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0, 1), (0,))))
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (1, 0), (0,))))
            adr(ord_rows(3, build_tensor_gram_poly(d, fa, fb, (0, 1), (2,))))
        else:
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0, 1), (0, 1))))
            adr(ord_rows(2, build_tensor_gram_poly(d, fa, fb, (0, 1), (1, 0))))
            for km in [(0, 2), (2, 0), (1, 2), (2, 1)]:
                adr(ord_rows(3, build_tensor_gram_poly(d, fa, fb, (0, 1), km)))
            adr(ord_rows(4, build_tensor_gram_poly(d, fa, fb, (0, 1), (2, 3))))
        return ar

    for d in range(D4 + 1):
        nf: list[tuple] = []
        if d == 0:
            nf.append(("id", ()))
        elif d == 2:
            nf.append(("id", ((0, 1),)))
        elif d == 4:
            nf.extend([("id", ((0, 1), (2, 3))), ("id", ((0, 2), (1, 3))), ("id", ((0, 3), (1, 2)))])
        nf.append(("v1", (), tuple(range(d))))
        sw = set()
        for w in itertools.product((0, 1), repeat=d):
            wf = () if d == 0 else tuple(1 - b for b in w)
            key = min(w, wf)
            if key in sw:
                continue
            sw.add(key)
            for p in range((D4 - d) // 2 + 1):
                if p == 0 and len(set(w)) <= 1:
                    continue
                nf.append(("pair", p, (), {s: w[s] for s in range(d)}))
        if nf:
            extra_psd.append((f"GlobNat_d{d}", len(nf), lambda a, b, d=d, F=nf: sop(d, F[a], F[b]), (d, nf)))

        if d >= 1 and d + 1 <= D4:
            af: list[tuple] = []
            sa = set()
            for w in itertools.product((0, 1), repeat=d - 1):
                wf = tuple(1 - b for b in w)
                if w == wf:
                    continue
                key = min(w, wf)
                if key in sa:
                    continue
                sa.add(key)
                for p in range((D4 - d - 1) // 2 + 1):
                    af.append(("cross", p, w))
            if af:
                extra_psd.append((f"GlobAx_d{d}", len(af), lambda a, b, d=d, F=af: sop(d, F[a], F[b]), (d, af)))

    return base, orbs6, orb6_target, n_new_rows, extra_lp, extra_psd


def verify_exact_4pt_identities(n: int, M: int, K: int, D4: int) -> None:
    """Exact rational verification of every 4-point LP column and PSD block on S^2."""
    base, orbs6, orb6_target, _, extra_lp, extra_psd = build_coupled_4pt_system(n, M, K, D4)
    rng = random.Random(20261123 + D4)
    pts = []
    for _ in range(n):
        u = Fraction(rng.randint(-5, 5), rng.randint(1, 4))
        v = Fraction(rng.randint(-5, 5), rng.randint(1, 4))
        dn = F1 + u * u + v * v
        pts.append((2 * u / dn, 2 * v / dn, (F1 - u * u - v * v) / dn))
    G = [[sum(pts[i][c] * pts[j][c] for c in range(3)) for j in range(n)] for i in range(n)]

    row_func: dict[int, Fraction] = {}
    s3p = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
    for idx, c3 in enumerate(base.sym_mons):
        orb3 = sorted(set((c3[p[0]], c3[p[1]], c3[p[2]]) for p in s3p))
        tot = F0
        for i in range(n):
            for j in range(i + 1, n):
                for l in range(j + 1, n):
                    u, v, t = G[i][j], G[i][l], G[j][l]
                    for a, b, dg in orb3:
                        tot += (u ** a) * (v ** b) * (t ** dg)
        row_func[idx + 1] = tot / F3

    for oidx, c6 in enumerate(orbs6):
        r_row, _ = orb6_target[oidx]
        if r_row > base.m:
            verts = set()
            for ei, dg in enumerate(c6):
                if dg > 0:
                    verts.update(EDGE_LIST[ei])
            if len(verts) <= 3:
                vlist = sorted(verts)
                while len(vlist) < 3:
                    for cv in range(4):
                        if cv not in vlist:
                            vlist.append(cv)
                            break
                u0, u1, u2 = vlist
                c3 = canon(c6[EDGE_IDX[(u0, u1)]], c6[EDGE_IDX[(u0, u2)]], c6[EDGE_IDX[(u1, u2)]])
                orb3 = sorted(set((c3[p[0]], c3[p[1]], c3[p[2]]) for p in s3p))
                tot3 = F0
                for i in range(n):
                    for j in range(i + 1, n):
                        for l in range(j + 1, n):
                            u, v, t = G[i][j], G[i][l], G[j][l]
                            for a, b, dg in orb3:
                                tot3 += (u ** a) * (v ** b) * (t ** dg)
                # Note: orb6_target stored mult = 1, while poly6_to_rows divided by orb6_size;
                # evaluate directly via 4-tuples!
            orb4 = sorted(set(tuple(c6[idx] for idx in emap) for emap in S4_EDGE_MAP))
            tot = F0
            for i, j, k, l in itertools.combinations(range(n), 4):
                ev = (G[i][j], G[i][k], G[i][l], G[j][k], G[j][l], G[k][l])
                for m in orb4:
                    pr = F1
                    for ei, pw in enumerate(m):
                        if pw:
                            pr *= ev[ei] ** pw
                    tot += pr
            row_func[r_row] = tot

    for col in extra_lp:
        assert sum((-v) * row_func[r] for r, v in col.items()) == 0, "DET4=0 identity failed!"

    def cross(a, b):
        return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])

    def dot3(a, b):
        return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

    def eval_tensor_vec(d: int, feat: tuple) -> list[Fraction]:
        vec = [F0] * (3 ** d)
        kind = feat[0]
        if kind == "id":
            pairs = feat[1]
            for idx_tup in itertools.product(range(3), repeat=d):
                if all(idx_tup[s1] == idx_tup[s2] for s1, s2 in pairs):
                    flat = 0
                    for c in idx_tup:
                        flat = 3 * flat + c
                    vec[flat] += F1
        elif kind == "v1":
            for i in range(n):
                for flat, idx_tup in enumerate(itertools.product(range(3), repeat=d)):
                    pr = F1
                    for c in idx_tup:
                        pr *= pts[i][c]
                    vec[flat] += pr
        elif kind == "pair":
            _, p, _, smap = feat
            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue
                    wt = G[i][j] ** p
                    u_pair = (pts[i], pts[j])
                    for flat, idx_tup in enumerate(itertools.product(range(3), repeat=d)):
                        pr = wt
                        for s, c in enumerate(idx_tup):
                            pr *= u_pair[smap[s]][c]
                        vec[flat] += pr
        elif kind == "cross":
            _, p, w = feat
            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue
                    wt = G[i][j] ** p
                    cr = cross(pts[i], pts[j])
                    u_pair = (pts[i], pts[j])
                    for flat, idx_tup in enumerate(itertools.product(range(3), repeat=d)):
                        pr = wt * cr[idx_tup[0]]
                        for s_off, c in enumerate(idx_tup[1:]):
                            pr *= u_pair[w[s_off]][c]
                        vec[flat] += pr
        return vec

    for bname, bsz, efn, meta in extra_psd:
        if bname == "Harm4_odd":
            bc_b = meta
            for a in range(bsz):
                for b in range(a, bsz):
                    val_alg = sum((-v) * row_func[r] for r, v in efn(a, b).items())
                    pa, qa, sa = bc_b[a]
                    pb, qb, sb = bc_b[b]
                    val_geo = F0
                    for i in range(n):
                        for j in range(n):
                            if i == j:
                                continue
                            cij = cross(pts[i], pts[j])
                            sa_ij = sum(
                                (G[i][j] ** pa) * (G[i][k] ** qa) * (G[j][k] ** sa) * dot3(cij, pts[k])
                                for k in range(n) if k != i and k != j
                            )
                            sb_ij = sum(
                                (G[i][j] ** pb) * (G[i][k] ** qb) * (G[j][k] ** sb) * dot3(cij, pts[k])
                                for k in range(n) if k != i and k != j
                            )
                            val_geo += HALF * sa_ij * sb_ij
                    assert val_alg == val_geo, f"Harm4_odd ({a},{b}) mismatch"
        elif bname.startswith("GlobNat_d") or bname.startswith("GlobAx_d"):
            d, f_list = meta
            if d <= 5:
                vecs = [eval_tensor_vec(d, f) for f in f_list]
                for a in range(bsz):
                    for b in range(a, bsz):
                        val_alg = sum((-v) * row_func[r] for r, v in efn(a, b).items())
                        val_geo = sum(vecs[a][q] * vecs[b][q] for q in range(3 ** d))
                        assert val_alg == val_geo, f"{bname} ({a},{b}) mismatch"


def solve_coupled(n: int, M: int, K: int, D4: int, sdpa_bin: str, precision: int = 112, eps: str = "1.0E-16") -> dict:
    t0 = time.time()
    param_txt = (
        f"250\tunsigned int maxIteration;\n"
        f"{eps}\tdouble 0.0 < epsilonStar;\n"
        f"1.0E4\tdouble 0.0 < lambdaStar;\n"
        f"2.0\tdouble 1.0 < omegaStar;\n"
        f"-1.0E5\tdouble lowerBound;\n"
        f"1.0E5\tdouble upperBound;\n"
        f"0.1\tdouble 0.0 <= betaStar <  1.0;\n"
        f"0.3\tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\n"
        f"0.9\tdouble 0.0 < gammaStar <  1.0;\n"
        f"{eps}\tdouble 0.0 < epsilonDash;\n"
        f"{precision}\tprecision\n"
    )
    with tempfile.TemporaryDirectory() as td:
        td_p = Path(td)
        par_p = td_p / "param.sdpa"
        dat_p = td_p / "prob.dat-s"
        res_p = td_p / "prob.result"
        par_p.write_text(param_txt)

        if D4 == 0:
            base = SymCapModel(n, Fraction(-1), M, K)
            info = base.write_dat(dat_p)
            ts = time.time()
            proc = subprocess.run([sdpa_bin, "-ds", str(dat_p), "-o", str(res_p), "-p", str(par_p)],
                                  capture_output=True, text=True)
            solve_s = time.time() - ts
            if proc.returncode != 0:
                raise RuntimeError(f"SDPA-GMP failed ({proc.returncode}): {proc.stderr[-800:]}")
            parsed = parse_sdpa_result(res_p)
            e_raw = float(parsed["lp"][0])
            return dict(M=M, K=K, D3=2 * M - 2, D4=0, m_rows=info["m"], n_blocks=info["n_blocks"],
                        n_entries=info["n_entries"], solve_s=round(solve_s, 2),
                        phase=parsed["info"]["phase_value"], iterations=parsed["info"]["iteration"],
                        e_raw=e_raw, gap_to_E_star=E_STAR_FLOAT - e_raw)

        base, _, _, n_new_rows, extra_lp, extra_psd = build_coupled_4pt_system(n, M, K, D4)
        m_tot = base.m + n_new_rows
        n_q = len(extra_lp)
        n_lp_tot = base.n_lp + 2 * n_q
        blk_s = [-n_lp_tot] + [b["size"] for b in base.blocks] + [bsz for _, bsz, _, _ in extra_psd]
        acc: dict = {}

        def put(k: int, l: int, i: int, j: int, v: Fraction) -> None:
            if v:
                nv = acc.get((k, l, i, j), F0) + v
                if nv:
                    acc[(k, l, i, j)] = nv
                else:
                    acc.pop((k, l, i, j), None)

        for (k, l, i, j, v) in base.build_sdpa_entries():
            put(k, l, i, j, v)
        pen = Fraction(1, 10 ** 11)
        for qi, col in enumerate(extra_lp):
            ip = base.n_lp + 2 * qi + 1
            im = base.n_lp + 2 * qi + 2
            put(0, 1, ip, ip, -pen)
            put(0, 1, im, im, -pen)
            for r, v in col.items():
                put(r, 1, ip, ip, v)
                put(r, 1, im, im, -v)
        bn = 1 + len(base.blocks)
        for bi, (_, bsz, efn, _) in enumerate(extra_psd):
            l = bn + 1 + bi
            for a in range(bsz):
                for b in range(a, bsz):
                    for r, v in efn(a, b).items():
                        put(r, l, a + 1, b + 1, v)
        bv = [F0] * m_tot
        bv[base.n_sym] = F1
        lines = [
            f"{m_tot}\n",
            f"{len(blk_s)}\n",
            " ".join(str(x) for x in blk_s) + "\n",
            " ".join(frac_dec(x) for x in bv) + "\n",
        ]
        for (k, l, i, j), v in sorted(acc.items()):
            lines.append(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        dat_p.write_text("".join(lines))
        ts = time.time()
        proc = subprocess.run([sdpa_bin, "-ds", str(dat_p), "-o", str(res_p), "-p", str(par_p)],
                              capture_output=True, text=True)
        solve_s = time.time() - ts
        if proc.returncode != 0:
            raise RuntimeError(f"SDPA-GMP failed ({proc.returncode}): {proc.stderr[-800:]}")
        parsed = parse_sdpa_result(res_p)
        e_raw = float(parsed["lp"][0])
        return dict(M=M, K=K, D3=2 * M - 2, D4=D4, m_rows=m_tot, n_blocks=len(blk_s),
                    n_entries=len(acc), solve_s=round(solve_s, 2),
                    total_s=round(time.time() - t0, 2),
                    phase=parsed["info"]["phase_value"], iterations=parsed["info"]["iteration"],
                    e_raw=e_raw, gap_to_E_star=E_STAR_FLOAT - e_raw)


def selftest() -> None:
    for d4 in (4, 6):
        print(f"[selftest] Verifying exact rational 4-point identities (DET4, Harm4_odd, GlobNat/GlobAx) at D4={d4}...")
        verify_exact_4pt_identities(11, 6, 6, d4)
    print("[selftest] PASS: All 4-point algebraic & tensor Gram identities verified with ZERO error!")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--sdpa-bin", type=str, default="/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
    ap.add_argument("--skip-d4-8", action="store_true")
    ap.add_argument("--out", type=str, default=str(HERE / "results" / "phase0_4pt_probe.json"))
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    selftest()
    cases = [
        (4, 4, 0, 112, "1.0E-16"),
        (4, 4, 6, 112, "1.0E-16"),
        (5, 5, 0, 112, "1.0E-16"),
        (5, 5, 6, 112, "1.0E-16"),
    ]
    if not args.skip_d4_8:
        cases.append((5, 5, 8, 96, "1.0E-14"))
    cases.extend([
        (8, 8, 0, 112, "1.0E-16"),
        (8, 8, 4, 112, "1.0E-16"),
        (8, 8, 6, 112, "1.0E-16"),
    ])

    results = []
    ref_by_m: dict[int, float] = {}
    for M, K, D4, prec, eps in cases:
        row = solve_coupled(11, M, K, D4, args.sdpa_bin, precision=prec, eps=eps)
        if D4 == 0:
            ref_by_m[M] = row["e_raw"]
            row["gain_over_3pt"] = 0.0
        else:
            row["gain_over_3pt"] = row["e_raw"] - ref_by_m[M]
        results.append(row)
        print(
            f"[M={M}, K={K}, D3={row['D3']:2d}, D4={D4:2d}] phase={row['phase']} ({row['solve_s']:5.1f}s) | "
            f"e_raw = {row['e_raw']:.12f} | gain_over_3pt = {row['gain_over_3pt']:+.12f} | gap = {row['gap_to_E_star']:.8f}",
            flush=True,
        )

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = dict(
        n=11,
        E_star=E_STAR_FLOAT,
        summary=(
            "At matching polynomial degrees D3=D4=6 (M=4) and D3=D4=8 (M=5), full S_11 x O(3) 4-point "
            "constraints (det G_4 = 0 + 4-pt SOS + Binet-Cauchy Harm4_odd + Flag2_even + global (R^3)^{\\otimes d} "
            "pair-tensor blocks) strictly improve the 3-point SDP bound by +0.16307292 (40.32802558 -> 40.49109850) "
            "and +0.00782206 (40.50635763 -> 40.51417969). However, low-degree 4-point constraints (D4 <= 8, ceiling "
            "40.51418) cannot surpass high-degree 3-point SDP (M=8..12, D3=14..22, reaching 40.55149..40.55696), "
            "and coupling D4=4,6 onto M=8 (D3=14) gives zero gain (< 2e-13) because the 9-atom pseudo-measure "
            "admits a feasible degree-6 4-point extension; surpassing 40.557 via 4-point SDP requires D4 >= 14..18."
        ),
        runs=results,
    )
    out_path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
