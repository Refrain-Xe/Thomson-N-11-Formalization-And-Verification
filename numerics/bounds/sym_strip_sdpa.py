#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""sym_strip_sdpa.py — Standalone exact rational (Fraction) S2/S2/S3-symmetry-reduced
(2, n-2) pole-ring typed strip/slab SDP engine for Thomson N = 11 (general n >= 5).

For any configuration X in (S^2)^n with one distinguished pair (0, 1) satisfying
lo <= <x_0, x_1> <= hi and all other pairs satisfying a_other <= <x_i, x_j> <= b_other
(by default a_other = lo when certifying min_{i<j} <x_i, x_j> in [lo, hi], or a_other = -1
when certifying ANY configuration having AT LEAST ONE pair in [lo, hi]!):

Wait — notice THAT CRUCIAL FLEXIBILITY:
  1. If we assume `m = min_{i<j} <x_i, x_j> in [lo, hi]`, then `u = t_01 = m in [lo, hi]` AND
     all other pairs `v, t >= m >= lo`, so `a_other = lo` is valid!
     In particular, for the deepest slab `m <= hi` (i.e. `lo = -1`), BOTH `a_other = -1` and `lo = -1` coincide!
  2. Even more generally, if we want to exclude ANY configuration having some pair `t_01 in [lo, hi]`
     while other pairs satisfy `t_ij in [a_other, b_other]`, setting `a_other` independently makes
     this engine handle BOTH slab splits on `min_{i<j} t_ij` AND arbitrary pair-interval splits!
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

from exact_linalg import (  # noqa: E402
    F0, F1, PARAM_SDPA, ceil_sqrt_rat, code_version, dyad,
    frac_dec, frac_str, is_positive_definite, parse_sdpa_result,
    repair_psd_fine,
)
from sym_cap_sdpa import (  # noqa: E402
    F2, F3, S3_PERMS, build_Q_polys, build_s2_vt_bases_exact,
    build_s3_isotypic_bases_exact, orbit_size, poly_add, poly_mul,
    poly_sym_vec, sym_monoms_3d,
)

SEED = 20261123


def monoms_3d_full(deg: int):
    out = []
    for s in range(deg + 1):
        for a in range(s, -1, -1):
            for b in range(s - a, -1, -1):
                out.append((a, b, s - a - b))
    return out


def monoms_s2_vt(deg: int):
    out = []
    for s in range(deg + 1):
        for a in range(s, -1, -1):
            rem = s - a
            for b in range(rem, -1, -1):
                c = rem - b
                if b >= c:
                    out.append((a, b, c))
    return out


def monoms_s2_uv(deg: int):
    out = []
    for s in range(deg + 1):
        for c in range(s, -1, -1):
            rem = s - c
            for a in range(rem, -1, -1):
                b = rem - a
                if a >= b:
                    out.append((a, b, c))
    return out


def build_s2_uv_bases_exact(deg: int):
    even, odd = [], []
    half = Fraction(1, 2)
    for s in range(deg + 1):
        for c in range(s, -1, -1):
            rem = s - c
            for a in range(rem, -1, -1):
                b = rem - a
                if a > b:
                    even.append({(a, b, c): half, (b, a, c): half})
                    odd.append({(a, b, c): half, (b, a, c): -half})
                elif a == b:
                    even.append({(a, a, c): F1})
    return even, odd


def poly_proj_vt(p: dict, idx_vt: dict) -> dict:
    out: dict = {}
    half = Fraction(1, 2)
    for (a, b, c), v in p.items():
        if not v:
            continue
        if b == c:
            idx = idx_vt[(a, b, c)]
            nv = out.get(idx, F0) + v
        else:
            key = (a, b, c) if b > c else (a, c, b)
            idx = idx_vt[key]
            nv = out.get(idx, F0) + v * half
        if nv:
            out[idx] = nv
        else:
            out.pop(idx, None)
    return out


def poly_proj_uv(p: dict, idx_uv: dict) -> dict:
    out: dict = {}
    half = Fraction(1, 2)
    for (a, b, c), v in p.items():
        if not v:
            continue
        if a == b:
            idx = idx_uv[(a, b, c)]
            nv = out.get(idx, F0) + v
        else:
            key = (a, b, c) if a > b else (b, a, c)
            idx = idx_uv[key]
            nv = out.get(idx, F0) + v * half
        if nv:
            out[idx] = nv
        else:
            out.pop(idx, None)
    return out


def eval_gm_poly(Y: dict) -> dict:
    out: dict = {}
    for (a, b, c), v in Y.items():
        if not v:
            continue
        for d in (b + c, a + c, a + b):
            nv = out.get(d, F0) + v
            if nv:
                out[d] = nv
            else:
                out.pop(d, None)
    return out


class SymStripModel:
    """Exact rational symmetry-reduced (2, n-2) pole-ring typed SDP on u=t_01 in [lo, hi], others in [a_other, 1]."""

    def __init__(self, n: int, lo: Fraction, hi: Fraction, M: int, K: int,
                 a_other: Fraction | None = None,
                 include_upper_1m: bool = True,
                 lp_penalty: Fraction = Fraction(1, 10 ** 11)):
        assert n >= 5, f"SymStripModel requires n >= 5, got {n}"
        if a_other is None:
            a_other = lo
        assert -F1 <= lo < hi <= F1
        assert -F1 <= a_other < F1
        self.n = n
        self.nR = n - 2
        self.N_A = Fraction(self.nR)
        self.N_B = Fraction(self.nR * (self.nR - 1))
        self.N_G = Fraction(math.comb(self.nR, 3))

        self.lo = lo
        self.hi = hi
        self.a_other = a_other
        self.M = M
        self.K = K
        self.include_upper_1m = include_upper_1m
        self.lp_penalty = lp_penalty
        self.D = 2 * M - 2
        self.d_H = self.D
        self.b2_A = (F1 - lo) / F2
        self.c2_A = (F1 - hi) / F2
        self.b2_other = (F1 - a_other) / F2
        self.n_y = 2 * self.d_H + 2

        self.mons_A = monoms_s2_vt(self.D)
        self.idx_A = {m: i for i, m in enumerate(self.mons_A)}
        self.n_A = len(self.mons_A)

        self.mons_B = monoms_s2_uv(self.D)
        self.idx_B = {m: i for i, m in enumerate(self.mons_B)}
        self.n_B = len(self.mons_B)

        self.mons_G = sym_monoms_3d(self.D)
        self.idx_G = {m: i for i, m in enumerate(self.mons_G)}
        self.n_G = len(self.mons_G)

        self.row_A = 1
        self.row_B = self.row_A + self.n_A
        self.row_G = self.row_B + self.n_B
        self.row_mA = self.row_G + self.n_G
        self.row_mB = self.row_mA + self.n_y
        self.row_mC = self.row_mB + self.n_y
        self.row_norm = self.row_mC + self.n_y
        self.m = self.row_norm

        d_H1 = self.d_H + 1
        pos = 1
        self.e_pos = pos
        pos += 1
        self.vpos = {}
        for name in ("h_A", "h_B", "h_C", "psi_Ba", "psi_Cb"):
            self.vpos[name] = (pos, pos + d_H1)
            pos += 2 * d_H1
        for name in ("c_a", "c_b", "c_g"):
            self.vpos[name] = (pos, pos + 1)
            pos += 2
        self.n_lp = pos - 1

        self.Q = build_Q_polys(K)
        self.blocks = []

        for typ in ("P", "R"):
            for k in range(K):
                mk = M - k
                if mk > 0:
                    self.blocks.append(dict(name=f"F_{typ}_{k}", kind="F", typ=typ, k=k, size=mk))

        detG = {(0, 0, 0): F1, (1, 1, 1): F2, (2, 0, 0): -F1, (0, 2, 0): -F1, (0, 0, 2): -F1}
        u_loA = {(1, 0, 0): F1, (0, 0, 0): -lo}
        hi_uA = {(0, 0, 0): hi, (1, 0, 0): -F1}

        u_loO = {(1, 0, 0): F1, (0, 0, 0): -a_other}
        v_loO = {(0, 1, 0): F1, (0, 0, 0): -a_other}
        t_loO = {(0, 0, 1): F1, (0, 0, 0): -a_other}
        u_hi1 = {(0, 0, 0): F1, (1, 0, 0): -F1}
        v_hi1 = {(0, 0, 0): F1, (0, 1, 0): -F1}
        t_hi1 = {(0, 0, 0): F1, (0, 0, 1): -F1}

        def add_A_s2(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_vt_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_A_{tag}_even", kind="sos_A", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_A_{tag}_odd", kind="sos_A", mp=mp, basis=odd, size=len(odd)))

        def add_A_asym(tag, mp, zdeg):
            if zdeg < 0:
                return
            mons = [{m: F1} for m in monoms_3d_full(zdeg)]
            self.blocks.append(dict(name=f"SOS_A_{tag}", kind="sos_A", mp=mp, basis=mons, size=len(mons)))

        add_A_s2("1", {(0, 0, 0): F1}, self.D // 2)
        add_A_s2("ulo", u_loA, (self.D - 1) // 2)
        add_A_s2("hiu", hi_uA, (self.D - 1) // 2)
        add_A_s2("detG", detG, (self.D - 3) // 2)
        add_A_asym("vlo", v_loO, (self.D - 1) // 2)
        if include_upper_1m:
            add_A_asym("vhi", v_hi1, (self.D - 1) // 2)

        def add_B_s2(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_uv_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_B_{tag}_even", kind="sos_B", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_B_{tag}_odd", kind="sos_B", mp=mp, basis=odd, size=len(odd)))

        def add_B_asym(tag, mp, zdeg):
            if zdeg < 0:
                return
            mons = [{m: F1} for m in monoms_3d_full(zdeg)]
            self.blocks.append(dict(name=f"SOS_B_{tag}", kind="sos_B", mp=mp, basis=mons, size=len(mons)))

        add_B_s2("1", {(0, 0, 0): F1}, self.D // 2)
        add_B_s2("tlo", t_loO, (self.D - 1) // 2)
        add_B_s2("detG", detG, (self.D - 3) // 2)
        add_B_asym("ulo", u_loO, (self.D - 1) // 2)
        if include_upper_1m:
            add_B_s2("thi", t_hi1, (self.D - 1) // 2)
            add_B_asym("uhi", u_hi1, (self.D - 1) // 2)

        def add_G_s3(tag, mp, zdeg):
            if zdeg < 0:
                return
            triv, sign, std_pairs = build_s3_isotypic_bases_exact(zdeg)
            if triv:
                self.blocks.append(dict(name=f"SOS_G_{tag}_triv", kind="sos_G_plain", mp=mp, basis=triv, size=len(triv)))
            if sign:
                self.blocks.append(dict(name=f"SOS_G_{tag}_sign", kind="sos_G_plain", mp=mp, basis=sign, size=len(sign)))
            if std_pairs:
                self.blocks.append(dict(name=f"SOS_G_{tag}_std", kind="sos_G_std", mp=mp, basis=std_pairs, size=len(std_pairs)))

        def add_G_s2(tag, mp, zdeg):
            if zdeg < 0:
                return
            even, odd = build_s2_vt_bases_exact(zdeg)
            if even:
                self.blocks.append(dict(name=f"SOS_G_{tag}_even", kind="sos_G_plain", mp=mp, basis=even, size=len(even)))
            if odd:
                self.blocks.append(dict(name=f"SOS_G_{tag}_odd", kind="sos_G_plain", mp=mp, basis=odd, size=len(odd)))

        add_G_s3("1", {(0, 0, 0): F1}, self.D // 2)
        add_G_s3("detG", detG, (self.D - 3) // 2)
        add_G_s2("ulo", u_loO, (self.D - 1) // 2)
        if include_upper_1m:
            add_G_s2("uhi", u_hi1, (self.D - 1) // 2)

        # Minorant blocks: H_A on [lo, hi], H_B and H_C on [a_other, 1)
        self.blocks.append(dict(name="tauA_0", kind="minor", row0=self.row_mA, pm={0: F1}, size=self.d_H + 1))
        self.blocks.append(dict(name="tauA_1", kind="minor", row0=self.row_mA, pm={1: F1}, size=self.d_H + 1))
        self.blocks.append(dict(name="tauA_2", kind="minor", row0=self.row_mA, pm={0: -self.c2_A, 2: F1}, size=self.d_H))
        self.blocks.append(dict(name="tauA_3", kind="minor", row0=self.row_mA, pm={0: self.b2_A, 2: -F1}, size=self.d_H))
        self.blocks.append(dict(name="tauA_4", kind="minor", row0=self.row_mA, pm={1: -self.c2_A, 3: F1}, size=self.d_H))
        self.blocks.append(dict(name="tauA_5", kind="minor", row0=self.row_mA, pm={1: self.b2_A, 3: -F1}, size=self.d_H))
        for cname, row0 in (("B", self.row_mB), ("C", self.row_mC)):
            self.blocks.append(dict(name=f"sig{cname}_0", kind="minor", row0=row0, pm={0: F1}, size=self.d_H + 1))
            self.blocks.append(dict(name=f"sig{cname}_1", kind="minor", row0=row0, pm={1: F1}, size=self.d_H + 1))
            self.blocks.append(dict(name=f"sig{cname}_2", kind="minor", row0=row0, pm={0: self.b2_other, 2: -F1}, size=self.d_H))
            self.blocks.append(dict(name=f"sig{cname}_3", kind="minor", row0=row0, pm={1: self.b2_other, 3: -F1}, size=self.d_H))

        self.blk_struct = [-self.n_lp] + [b["size"] for b in self.blocks]

    def _f_sym_Y(self, k: int, a: int, b: int) -> dict:
        Qk = self.Q[k]
        if a == b:
            return {(e0 + a, e1 + b, e2): v for (e0, e1, e2), v in Qk.items()}
        out: dict = {}
        half = Fraction(1, 2)
        for (e0, e1, e2), v in Qk.items():
            k1 = (e0 + a, e1 + b, e2)
            k2 = (e0 + b, e1 + a, e2)
            out[k1] = out.get(k1, F0) + v * half
            out[k2] = out.get(k2, F0) + v * half
        return {kk: vv for kk, vv in out.items() if vv}

    def block_entry_map(self, blk: dict, a: int, b: int) -> dict[int, Fraction]:
        kind = blk["kind"]
        nR = self.nR
        if kind == "F":
            typ = blk["typ"]
            k = blk["k"]
            Y = self._f_sym_Y(k, a, b)
            gm = eval_gm_poly(Y)
            res: dict[int, Fraction] = {}

            def add_to(r, v):
                if v:
                    nv = res.get(r, F0) + v
                    if nv:
                        res[r] = nv
                    else:
                        res.pop(r, None)

            if typ == "P":
                for d, v in gm.items():
                    add_to(self.row_A + self.idx_A[(d, 0, 0)], -Fraction(2, nR) * v)
                for idx, v in poly_proj_vt(Y, self.idx_A).items():
                    add_to(self.row_A + idx, -Fraction(4) * v)

                for d, v in gm.items():
                    if d == 0:
                        add_to(self.row_B + self.idx_B[(0, 0, 0)], -Fraction(2, nR - 1) * v)
                    else:
                        add_to(self.row_B + self.idx_B[(d, 0, 0)], -Fraction(1, nR - 1) * v)
                for idx, v in poly_proj_uv(Y, self.idx_B).items():
                    add_to(self.row_B + idx, -F2 * v)

                y111 = sum(Y.values(), F0)
                if y111:
                    add_to(self.row_norm, -F2 * y111)
            else:
                Y_vtu = {(e2, e0, e1): v for (e0, e1, e2), v in Y.items()}
                for idx, v in poly_proj_vt(Y_vtu, self.idx_A).items():
                    add_to(self.row_A + idx, -F2 * v)

                for d, v in gm.items():
                    if d == 0:
                        add_to(self.row_B + self.idx_B[(0, 0, 0)], -Fraction(2, nR - 1) * v)
                    else:
                        add_to(self.row_B + self.idx_B[(d, 0, 0)], -Fraction(1, nR - 1) * v)
                Y_utv = {(e0, e2, e1): v for (e0, e1, e2), v in Y.items()}
                for idx, v in poly_proj_uv(Y_utv, self.idx_B).items():
                    add_to(self.row_B + idx, -Fraction(4) * v)

                for d, v in gm.items():
                    if d == 0:
                        add_to(self.row_G + self.idx_G[(0, 0, 0)], -Fraction(6, nR - 2) * v)
                    else:
                        add_to(self.row_G + self.idx_G[(d, 0, 0)], -Fraction(2, nR - 2) * v)
                for idx, v in poly_sym_vec(Y, self.idx_G).items():
                    add_to(self.row_G + idx, -Fraction(6) * v)

                y111 = sum(Y.values(), F0)
                if y111:
                    add_to(self.row_norm, -Fraction(nR) * y111)
            return res

        elif kind == "sos_A":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {self.row_A + idx: -v for idx, v in poly_proj_vt(p, self.idx_A).items() if v}

        elif kind == "sos_B":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {self.row_B + idx: -v for idx, v in poly_proj_uv(p, self.idx_B).items() if v}

        elif kind == "sos_G_plain":
            B = blk["basis"]
            p = poly_mul(blk["mp"], poly_mul(B[a], B[b]))
            return {self.row_G + idx: -v for idx, v in poly_sym_vec(p, self.idx_G).items() if v}

        elif kind == "sos_G_std":
            B = blk["basis"]
            p = poly_add(poly_mul(B[a][0], B[b][0]), poly_mul(B[a][1], B[b][1]), F3)
            p = {kk: vv / F3 for kk, vv in p.items()}
            pm = poly_mul(blk["mp"], p)
            return {self.row_G + idx: -v for idx, v in poly_sym_vec(pm, self.idx_G).items() if v}

        elif kind == "minor":
            pm = blk["pm"]
            row0 = blk["row0"]
            out: dict[int, Fraction] = {}
            for dp, vp in pm.items():
                deg = a + b + dp
                if deg < self.n_y:
                    r = row0 + deg
                    out[r] = out.get(r, F0) + vp
            return {r: v for r, v in out.items() if v}

        raise ValueError(kind)

    def build_sdpa_entries(self):
        acc: dict = {}
        nR = self.nR

        def put(k, l, i, j, v):
            if v:
                nv = acc.get((k, l, i, j), F0) + v
                if nv:
                    acc[(k, l, i, j)] = nv
                else:
                    acc.pop((k, l, i, j), None)

        def put_split(r, name, d, v):
            pp, mm = self.vpos[name]
            put(r, 1, pp + d, pp + d, v)
            put(r, 1, mm + d, mm + d, -v)

        put(0, 1, self.e_pos, self.e_pos, F1)
        if self.lp_penalty:
            for name, (pp, mm) in self.vpos.items():
                sz = mm - pp
                for d in range(sz):
                    put(0, 1, pp + d, pp + d, -self.lp_penalty)
                    put(0, 1, mm + d, mm + d, -self.lp_penalty)

        put(self.row_norm, 1, self.e_pos, self.e_pos, -F1)
        put_split(self.row_norm, "c_a", 0, self.N_A)
        put_split(self.row_norm, "c_b", 0, self.N_B)
        put_split(self.row_norm, "c_g", 0, self.N_G)

        put_split(self.row_A + self.idx_A[(0, 0, 0)], "c_a", 0, -F1)
        for d in range(self.d_H + 1):
            put_split(self.row_A + self.idx_A[(d, 0, 0)], "h_A", d, Fraction(1, nR))
            if d == 0:
                put_split(self.row_A + self.idx_A[(0, 0, 0)], "psi_Ba", 0, F2)
            else:
                put_split(self.row_A + self.idx_A[(0, d, 0)], "psi_Ba", d, F1)

        put_split(self.row_B + self.idx_B[(0, 0, 0)], "c_b", 0, -F1)
        for d in range(self.d_H + 1):
            if d == 0:
                put_split(self.row_B + self.idx_B[(0, 0, 0)], "h_B", 0, Fraction(2, nR - 1))
                put_split(self.row_B + self.idx_B[(0, 0, 0)], "psi_Ba", 0, -Fraction(2, nR - 1))
            else:
                put_split(self.row_B + self.idx_B[(d, 0, 0)], "h_B", d, Fraction(1, nR - 1))
                put_split(self.row_B + self.idx_B[(d, 0, 0)], "psi_Ba", d, -Fraction(1, nR - 1))
            put_split(self.row_B + self.idx_B[(0, 0, d)], "psi_Cb", d, F1)

        put_split(self.row_G + self.idx_G[(0, 0, 0)], "c_g", 0, -F1)
        for d in range(self.d_H + 1):
            if d == 0:
                put_split(self.row_G + self.idx_G[(0, 0, 0)], "h_C", 0, Fraction(3, nR - 2))
                put_split(self.row_G + self.idx_G[(0, 0, 0)], "psi_Cb", 0, -Fraction(6, nR - 2))
            else:
                put_split(self.row_G + self.idx_G[(d, 0, 0)], "h_C", d, Fraction(1, nR - 2))
                put_split(self.row_G + self.idx_G[(d, 0, 0)], "psi_Cb", d, -Fraction(2, nR - 2))

        for name, row0 in (("h_A", self.row_mA), ("h_B", self.row_mB), ("h_C", self.row_mC)):
            for d in range(self.d_H + 1):
                for j in range(d + 1):
                    c_yj = Fraction(2 * math.comb(d, j) * ((-2) ** j))
                    put_split(row0 + (2 * j + 1), name, d, c_yj)

        for b_idx, blk in enumerate(self.blocks):
            l = 2 + b_idx
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    emap = self.block_entry_map(blk, a, b)
                    for r, v in emap.items():
                        put(r, l, a + 1, b + 1, v)

        return [(k, l, i, j, v) for (k, l, i, j), v in acc.items()]

    def write_dat(self, path: Path) -> dict:
        t0 = time.time()
        entries = self.build_sdpa_entries()
        b_vec = [F0] * self.m
        b_vec[self.row_mA - 1] = F1
        b_vec[self.row_mB - 1] = F1
        b_vec[self.row_mC - 1] = F1
        entries.sort(key=lambda x: (x[0], x[1], x[2], x[3]))
        lines = [
            f"{self.m}\n",
            f"{len(self.blk_struct)}\n",
            " ".join(str(x) for x in self.blk_struct) + "\n",
            " ".join(frac_dec(x) for x in b_vec) + "\n",
        ]
        for (k, l, i, j, v) in entries:
            lines.append(f"{k} {l} {i} {j} {frac_dec(v)}\n")
        path.write_text("".join(lines))
        return dict(m=self.m, n_blocks=len(self.blk_struct), n_entries=len(entries),
                    export_s=round(time.time() - t0, 2))

    def exact_residuals(self, lp_vals: dict, psd_mats: list) -> dict:
        nR = self.nR
        res = [F0] * self.m
        res[self.row_mA - 1] = -F1
        res[self.row_mB - 1] = -F1
        res[self.row_mC - 1] = -F1

        res[self.row_norm - 1] += (
            -lp_vals["e"]
            + self.N_A * lp_vals["c_a"]
            + self.N_B * lp_vals["c_b"]
            + self.N_G * lp_vals["c_g"]
        )

        res[self.row_A - 1 + self.idx_A[(0, 0, 0)]] -= lp_vals["c_a"]
        for d in range(self.d_H + 1):
            res[self.row_A - 1 + self.idx_A[(d, 0, 0)]] += lp_vals["h_A"][d] / Fraction(nR)
            if d == 0:
                res[self.row_A - 1 + self.idx_A[(0, 0, 0)]] += F2 * lp_vals["psi_Ba"][0]
            else:
                res[self.row_A - 1 + self.idx_A[(0, d, 0)]] += lp_vals["psi_Ba"][d]

        res[self.row_B - 1 + self.idx_B[(0, 0, 0)]] -= lp_vals["c_b"]
        for d in range(self.d_H + 1):
            diff = lp_vals["h_B"][d] - lp_vals["psi_Ba"][d]
            if d == 0:
                res[self.row_B - 1 + self.idx_B[(0, 0, 0)]] += Fraction(2, nR - 1) * diff
            else:
                res[self.row_B - 1 + self.idx_B[(d, 0, 0)]] += Fraction(1, nR - 1) * diff
            res[self.row_B - 1 + self.idx_B[(0, 0, d)]] += lp_vals["psi_Cb"][d]

        res[self.row_G - 1 + self.idx_G[(0, 0, 0)]] -= lp_vals["c_g"]
        for d in range(self.d_H + 1):
            diff = lp_vals["h_C"][d] - F2 * lp_vals["psi_Cb"][d]
            if d == 0:
                res[self.row_G - 1 + self.idx_G[(0, 0, 0)]] += Fraction(3, nR - 2) * diff
            else:
                res[self.row_G - 1 + self.idx_G[(d, 0, 0)]] += Fraction(1, nR - 2) * diff

        for name, row0 in (("h_A", self.row_mA), ("h_B", self.row_mB), ("h_C", self.row_mC)):
            hv = lp_vals[name]
            for d in range(self.d_H + 1):
                if not hv[d]:
                    continue
                for j in range(d + 1):
                    c_yj = Fraction(2 * math.comb(d, j) * ((-2) ** j))
                    res[row0 - 1 + (2 * j + 1)] += c_yj * hv[d]

        for blk, mat in zip(self.blocks, psd_mats):
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    x_ab = mat[a][b]
                    if not x_ab:
                        continue
                    mult = F1 if a == b else F2
                    for r, v in self.block_entry_map(blk, a, b).items():
                        res[r - 1] += mult * x_ab * v

        R1_A = F0
        for i, (a, b, c) in enumerate(self.mons_A):
            mult = 1 if b == c else 2
            R1_A += mult * abs(res[self.row_A - 1 + i])
        R1_B = F0
        for i, (a, b, c) in enumerate(self.mons_B):
            mult = 1 if a == b else 2
            R1_B += mult * abs(res[self.row_B - 1 + i])
        R1_G = F0
        for i, c in enumerate(self.mons_G):
            R1_G += orbit_size(c) * abs(res[self.row_G - 1 + i])

        w_hat_A = ceil_sqrt_rat(self.b2_A, bits=80)
        w_hat_O = ceil_sqrt_rat(self.b2_other, bits=80)
        R2 = {}
        for cname, row0, wh in (("A", self.row_mA, w_hat_A), ("B", self.row_mB, w_hat_O), ("C", self.row_mC, w_hat_O)):
            acc = F0
            wp = F1
            for j in range(self.n_y):
                acc += abs(res[row0 - 1 + j]) * wp
                wp *= wh
            R2[cname] = acc
        norm_err = abs(res[self.row_norm - 1])
        return dict(R1_A=R1_A, R1_B=R1_B, R1_G=R1_G, R2=R2, norm_err=norm_err,
                    w_hat_A=w_hat_A, w_hat_O=w_hat_O)

    def certify_from_result(self, res_path: Path, k_bits: int = 96) -> dict:
        parsed = parse_sdpa_result(res_path)
        info = parsed["info"]
        lp = parsed["lp"]
        assert len(lp) == self.n_lp

        def get_split(name, is_poly=True):
            pp, mm = self.vpos[name]
            if is_poly:
                return [lp[pp - 1 + d] - lp[mm - 1 + d] for d in range(self.d_H + 1)]
            return lp[pp - 1] - lp[mm - 1]

        lp_raw = dict(
            e=lp[self.e_pos - 1],
            h_A=get_split("h_A"), h_B=get_split("h_B"), h_C=get_split("h_C"),
            psi_Ba=get_split("psi_Ba"), psi_Cb=get_split("psi_Cb"),
            c_a=get_split("c_a", False), c_b=get_split("c_b", False), c_g=get_split("c_g", False),
        )
        psd_raw = [[[Fraction(x) for x in row] for row in g] for g in parsed["sdp"]]
        raw_res = self.exact_residuals(lp_raw, psd_raw)

        e_d = dyad(lp_raw["e"], k_bits, floor=True)
        lp_d = dict(
            e=e_d,
            h_A=[dyad(x, k_bits) for x in lp_raw["h_A"]],
            h_B=[dyad(x, k_bits) for x in lp_raw["h_B"]],
            h_C=[dyad(x, k_bits) for x in lp_raw["h_C"]],
            psi_Ba=[dyad(x, k_bits) for x in lp_raw["psi_Ba"]],
            psi_Cb=[dyad(x, k_bits) for x in lp_raw["psi_Cb"]],
            c_a=dyad(lp_raw["c_a"], k_bits),
            c_b=dyad(lp_raw["c_b"], k_bits),
            c_g=F0,
        )
        psd_d = []
        repairs = {}
        sP_111 = F0
        sR_111 = F0
        for blk, mat in zip(self.blocks, psd_raw):
            sz = blk["size"]
            M_d = [[dyad(mat[i][j], k_bits) for j in range(sz)] for i in range(sz)]
            for i in range(sz):
                for j in range(i + 1, sz):
                    M_d[j][i] = M_d[i][j]
            M_rep, delta = repair_psd_fine(M_d, k_bits)
            assert is_positive_definite(M_rep), f"Block {blk['name']} failed exact LDL^T!"
            psd_d.append(M_rep)
            if delta > 0:
                repairs[blk["name"]] = frac_str(delta)
            if blk["kind"] == "F" and blk["k"] == 0:
                s111 = sum(M_rep[i][j] for i in range(sz) for j in range(sz))
                if blk["typ"] == "P":
                    sP_111 = s111
                else:
                    sR_111 = s111

        lp_d["c_g"] = (
            e_d + F2 * sP_111 + Fraction(self.nR) * sR_111
            - self.N_A * lp_d["c_a"] - self.N_B * lp_d["c_b"]
        ) / self.N_G
        d_res = self.exact_residuals(lp_d, psd_d)
        assert d_res["norm_err"] == 0, f"Normalization error nonzero: {d_res['norm_err']}"
        defl = self.N_A * d_res["R1_A"] + self.N_B * d_res["R1_B"] + self.N_G * d_res["R1_G"]
        R2max = max(d_res["R2"].values())
        certified = (e_d - defl) / (F1 + R2max)
        return dict(
            info=info, lp_raw=lp_raw, raw_res=raw_res,
            k_bits=k_bits, lp_d=lp_d, psd_d=psd_d, d_res=d_res,
            R2max=R2max, certified=certified, repairs=repairs,
        )

    def write_certificate(self, cert_data: dict, out_path: Path, solve_s: float) -> dict:
        blocks_json = []
        for blk, mat in zip(self.blocks, cert_data["psd_d"]):
            sz = blk["size"]
            utri = [[frac_str(mat[i][j]) for j in range(i, sz)] for i in range(sz)]
            blocks_json.append(dict(name=blk["name"], kind=blk["kind"], size=sz, utri=utri))
        lp_d = cert_data["lp_d"]
        d_res = cert_data["d_res"]
        payload = dict(
            kind=f"n{self.n}-symstrip-exact-certificate",
            schema="symstrip-2n2/v1",
            n=self.n,
            lo=frac_str(self.lo),
            hi=frac_str(self.hi),
            a_other=frac_str(self.a_other),
            include_upper_1m=self.include_upper_1m,
            M=self.M,
            K=self.K,
            round_bits=cert_data["k_bits"],
            lp=dict(
                e=frac_str(lp_d["e"]),
                h_A=[frac_str(x) for x in lp_d["h_A"]],
                h_B=[frac_str(x) for x in lp_d["h_B"]],
                h_C=[frac_str(x) for x in lp_d["h_C"]],
                psi_Ba=[frac_str(x) for x in lp_d["psi_Ba"]],
                psi_Cb=[frac_str(x) for x in lp_d["psi_Cb"]],
                c_a=frac_str(lp_d["c_a"]),
                c_b=frac_str(lp_d["c_b"]),
                c_g=frac_str(lp_d["c_g"]),
            ),
            R1_A=frac_str(d_res["R1_A"]),
            R1_B=frac_str(d_res["R1_B"]),
            R1_G=frac_str(d_res["R1_G"]),
            R2={k: frac_str(v) for k, v in d_res["R2"].items()},
            R2max=frac_str(cert_data["R2max"]),
            claimed_bound=frac_str(cert_data["certified"]),
            claimed_bound_float=float(cert_data["certified"]),
            repairs=cert_data["repairs"],
            blocks=blocks_json,
            provenance=dict(
                script="numerics/bounds/sym_strip_sdpa.py",
                code_version=code_version(REPO),
                seed=SEED,
                generated_utc=datetime.now(timezone.utc).isoformat(),
                sdpa_phase=cert_data["info"]["phase_value"],
                sdpa_iteration=cert_data["info"]["iteration"],
                sdpa_mu=cert_data["info"]["mu"],
                sdpa_relgap=cert_data["info"]["relative_gap"],
                solve_s=round(solve_s, 2),
                e_raw_exact=frac_str(cert_data["lp_raw"]["e"]),
            ),
        )
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(payload, indent=2) + "\n")
        return payload


def verify_certificate_file(cert_path: Path, run_identity_check: bool = True) -> dict:
    """Independent exact Fraction + Sylvester/LDL^T certificate verifier for (2, n-2) typed strip SDP."""
    t0 = time.time()
    raw = json.loads(cert_path.read_text())
    n = int(raw["n"])
    assert raw["kind"] == f"n{n}-symstrip-exact-certificate"
    lo = Fraction(raw["lo"])
    hi = Fraction(raw["hi"])
    a_other = Fraction(raw["a_other"])
    inc_u = bool(raw.get("include_upper_1m", True))
    M = int(raw["M"])
    K = int(raw["K"])
    model = SymStripModel(n, lo, hi, M, K, a_other=a_other, include_upper_1m=inc_u)

    lp_raw_j = raw["lp"]
    lp_d = dict(
        e=Fraction(lp_raw_j["e"]),
        h_A=[Fraction(x) for x in lp_raw_j["h_A"]],
        h_B=[Fraction(x) for x in lp_raw_j["h_B"]],
        h_C=[Fraction(x) for x in lp_raw_j["h_C"]],
        psi_Ba=[Fraction(x) for x in lp_raw_j["psi_Ba"]],
        psi_Cb=[Fraction(x) for x in lp_raw_j["psi_Cb"]],
        c_a=Fraction(lp_raw_j["c_a"]),
        c_b=Fraction(lp_raw_j["c_b"]),
        c_g=Fraction(lp_raw_j["c_g"]),
    )
    for kpoly in ("h_A", "h_B", "h_C", "psi_Ba", "psi_Cb"):
        assert len(lp_d[kpoly]) == model.d_H + 1

    blocks_json = raw["blocks"]
    assert len(blocks_json) == len(model.blocks), f"Block count mismatch {len(blocks_json)} != {len(model.blocks)}"
    psd_d = []
    for blk_spec, bj in zip(model.blocks, blocks_json):
        assert bj["name"] == blk_spec["name"] and bj["size"] == blk_spec["size"]
        sz = blk_spec["size"]
        mat = [[F0] * sz for _ in range(sz)]
        for i in range(sz):
            row = bj["utri"][i]
            assert len(row) == sz - i
            for off, s in enumerate(row):
                val = Fraction(s)
                mat[i][i + off] = val
                mat[i + off][i] = val
        if not is_positive_definite(mat):
            raise AssertionError(f"EXACT PD CHECK FAILED on block {blk_spec['name']}!")
        psd_d.append(mat)

    d_res = model.exact_residuals(lp_d, psd_d)
    assert d_res["norm_err"] == 0, f"Nonzero normalization error: {d_res['norm_err']}"
    assert d_res["R1_A"] == Fraction(raw["R1_A"]), "R1_A mismatch"
    assert d_res["R1_B"] == Fraction(raw["R1_B"]), "R1_B mismatch"
    assert d_res["R1_G"] == Fraction(raw["R1_G"]), "R1_G mismatch"
    R2max = max(d_res["R2"].values())
    assert R2max == Fraction(raw["R2max"]), "R2max mismatch"
    defl = model.N_A * d_res["R1_A"] + model.N_B * d_res["R1_B"] + model.N_G * d_res["R1_G"]
    certified = (lp_d["e"] - defl) / (F1 + R2max)
    claimed = Fraction(raw["claimed_bound"])
    assert certified == claimed, f"Bound mismatch: recomputed {certified} != claimed {claimed}"

    id_err = F0
    if run_identity_check:
        rng = random.Random(SEED + n)
        G = [[F1 if i == j else F0 for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                G[i][j] = G[j][i] = Fraction(rng.randint(-3, 3), 5)
        nR = model.nR
        d1 = model.d_H + 1
        res = [F0] * model.m
        res[model.row_A - 1 + model.idx_A[(0, 0, 0)]] -= lp_d["c_a"]
        for d in range(d1):
            res[model.row_A - 1 + model.idx_A[(d, 0, 0)]] += lp_d["h_A"][d] / Fraction(nR)
            if d == 0:
                res[model.row_A - 1 + model.idx_A[(0, 0, 0)]] += F2 * lp_d["psi_Ba"][0]
            else:
                res[model.row_A - 1 + model.idx_A[(0, d, 0)]] += lp_d["psi_Ba"][d]
        res[model.row_B - 1 + model.idx_B[(0, 0, 0)]] -= lp_d["c_b"]
        for d in range(d1):
            diff = lp_d["h_B"][d] - lp_d["psi_Ba"][d]
            if d == 0:
                res[model.row_B - 1 + model.idx_B[(0, 0, 0)]] += Fraction(2, nR - 1) * diff
            else:
                res[model.row_B - 1 + model.idx_B[(d, 0, 0)]] += Fraction(1, nR - 1) * diff
            res[model.row_B - 1 + model.idx_B[(0, 0, d)]] += lp_d["psi_Cb"][d]
        res[model.row_G - 1 + model.idx_G[(0, 0, 0)]] -= lp_d["c_g"]
        for d in range(d1):
            diff = lp_d["h_C"][d] - F2 * lp_d["psi_Cb"][d]
            if d == 0:
                res[model.row_G - 1 + model.idx_G[(0, 0, 0)]] += Fraction(3, nR - 2) * diff
            else:
                res[model.row_G - 1 + model.idx_G[(d, 0, 0)]] += Fraction(1, nR - 2) * diff
        F_mats: dict = {"P": [], "R": []}
        for blk, mat in zip(model.blocks, psd_d):
            if blk["kind"] != "F":
                continue
            F_mats[blk["typ"]].append((blk["k"], mat))
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    mult = F1 if a == b else F2
                    for r, v in model.block_entry_map(blk, a, b).items():
                        if r < model.row_mA:
                            res[r - 1] += mult * mat[a][b] * v

        max_pw = max(model.D, M)
        powG = [[[F1] for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                gij = G[i][j]
                pij = powG[i][j]
                for _ in range(max_pw):
                    pij.append(pij[-1] * gij)

        def ev_A(pu, pv, pt):
            tot = F0
            for idx_m, (a, b, c) in enumerate(model.mons_A):
                val = res[model.row_A - 1 + idx_m]
                if not val:
                    continue
                if b == c:
                    tot += val * pu[a] * pv[b] * pt[c]
                else:
                    tot += val * pu[a] * (pv[b] * pt[c] + pv[c] * pt[b])
            return tot

        def ev_B(pu, pv, pt):
            tot = F0
            for idx_m, (a, b, c) in enumerate(model.mons_B):
                val = res[model.row_B - 1 + idx_m]
                if not val:
                    continue
                if a == b:
                    tot += val * pu[a] * pv[b] * pt[c]
                else:
                    tot += val * (pu[a] * pv[b] + pu[b] * pv[a]) * pt[c]
            return tot

        terms_G = []
        for idx_m, c in enumerate(model.mons_G):
            val = res[model.row_G - 1 + idx_m]
            if val:
                terms_G.append((val, sorted(set((c[p[0]], c[p[1]], c[p[2]]) for p in S3_PERMS))))

        def ev_G(pu, pv, pt):
            tot = F0
            for val, orb in terms_G:
                tot += val * sum(pu[a] * pv[b] * pt[d] for a, b, d in orb)
            return tot

        def ev1(coeffs, px):
            return sum(c * px[d] for d, c in enumerate(coeffs))

        lhs = -lp_d["e"]
        for i in range(n):
            for j in range(i + 1, n):
                if i < 2 and j < 2:
                    lhs += ev1(lp_d["h_A"], powG[i][j])
                elif i < 2:
                    lhs += ev1(lp_d["h_B"], powG[i][j])
                else:
                    lhs += ev1(lp_d["h_C"], powG[i][j])

        sum_lam = F0
        for r in range(2, n):
            sum_lam += ev_A(powG[0][1], powG[0][r], powG[1][r])
        for p in range(2):
            for r1 in range(2, n):
                for r2 in range(r1 + 1, n):
                    sum_lam += ev_B(powG[p][r1], powG[p][r2], powG[r1][r2])
        for r1 in range(2, n):
            for r2 in range(r1 + 1, n):
                for r3 in range(r2 + 1, n):
                    sum_lam += ev_G(powG[r1][r2], powG[r1][r3], powG[r2][r3])

        sum_all = F0
        for i in range(n):
            typ = "P" if i < 2 else "R"
            fm_list = F_mats[typ]
            u_contracted = []
            for j in range(n):
                pu = powG[i][j]
                by_k = []
                for k, mat in fm_list:
                    sz = len(mat)
                    by_k.append([sum(pu[a] * mat[a][b] for a in range(sz)) for b in range(sz)])
                u_contracted.append(by_k)
            for j in range(n):
                u = G[i][j]
                omu2 = F1 - u * u
                by_k = u_contracted[j]
                for l in range(n):
                    v, t = G[i][l], G[j][l]
                    pv = powG[i][l]
                    q_vals = [F1]
                    if K > 1:
                        tuv = t - u * v
                        omu2v2 = omu2 * (F1 - v * v)
                        q_vals.append(tuv)
                        for _ in range(2, K):
                            q_vals.append(2 * tuv * q_vals[-1] - omu2v2 * q_vals[-2])
                    for idx_k, (k, _) in enumerate(fm_list):
                        w_vec = by_k[idx_k]
                        quad = sum(w_vec[b] * pv[b] for b in range(len(w_vec)))
                        sum_all += q_vals[k] * quad

        id_err = abs(lhs - (sum_lam + sum_all))
        assert id_err == 0, f"EXACT (2, {n-2}) IDENTITY FAILED: |LHS-RHS|={id_err}"

    sha = hashlib.sha256(cert_path.read_bytes()).hexdigest()
    try:
        rel_cert = str(cert_path.resolve().relative_to(REPO.resolve()))
    except ValueError:
        rel_cert = cert_path.name
    return dict(
        ok=True, cert_path=rel_cert, sha256=sha,
        n=n, lo=frac_str(lo), hi=frac_str(hi), a_other=frac_str(a_other),
        M=M, K=K, blocks_verified=len(psd_d),
        R1_A=float(d_res["R1_A"]), R1_B=float(d_res["R1_B"]), R1_G=float(d_res["R1_G"]),
        R2max=float(R2max),
        certified_exact=frac_str(certified), certified_float=float(certified),
        identity_error=int(id_err), verify_s=round(time.time() - t0, 2),
    )


def selftest() -> None:
    for n in (9, 11):
        print(f"[selftest] Testing exact (2, {n-2}) combinatorial identity on random rational Gram (n={n}, M=4, K=4)...")
        model = SymStripModel(n, Fraction(-9, 10), Fraction(-4, 5), M=4, K=4)
        rng = random.Random(SEED + n)
        G = [[F1 if i == j else F0 for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                G[i][j] = G[j][i] = Fraction(rng.randint(-5, 5), 8)
        d1 = model.d_H + 1
        rpoly = lambda: [Fraction(rng.randint(-3, 3), 4) for _ in range(d1)]
        lp = dict(e=Fraction(10), h_A=rpoly(), h_B=rpoly(), h_C=rpoly(),
                  psi_Ba=rpoly(), psi_Cb=rpoly(), c_a=Fraction(1, 3), c_b=Fraction(-1, 5), c_g=F0)
        psd = []
        sP111, sR111 = F0, F0
        F_mats: dict = {"P": {}, "R": {}}
        for blk in model.blocks:
            sz = blk["size"]
            if blk["kind"] == "F":
                M = [[Fraction(rng.randint(-2, 2), 4) for _ in range(sz)] for _ in range(sz)]
                M = [[(M[i][j] + M[j][i]) / F2 for j in range(sz)] for i in range(sz)]
                psd.append(M)
                F_mats[blk["typ"]][blk["k"]] = M
                if blk["k"] == 0:
                    s = sum(M[i][j] for i in range(sz) for j in range(sz))
                    if blk["typ"] == "P":
                        sP111 = s
                    else:
                        sR111 = s
            else:
                psd.append([[F0] * sz for _ in range(sz)])
        lp["c_g"] = (
            lp["e"] + F2 * sP111 + Fraction(model.nR) * sR111
            - model.N_A * lp["c_a"] - model.N_B * lp["c_b"]
        ) / model.N_G

        nR = model.nR
        res = [F0] * model.m
        res[model.row_A - 1 + model.idx_A[(0, 0, 0)]] -= lp["c_a"]
        for d in range(d1):
            res[model.row_A - 1 + model.idx_A[(d, 0, 0)]] += lp["h_A"][d] / Fraction(nR)
            if d == 0:
                res[model.row_A - 1 + model.idx_A[(0, 0, 0)]] += F2 * lp["psi_Ba"][0]
            else:
                res[model.row_A - 1 + model.idx_A[(0, d, 0)]] += lp["psi_Ba"][d]
        res[model.row_B - 1 + model.idx_B[(0, 0, 0)]] -= lp["c_b"]
        for d in range(d1):
            diff = lp["h_B"][d] - lp["psi_Ba"][d]
            if d == 0:
                res[model.row_B - 1 + model.idx_B[(0, 0, 0)]] += Fraction(2, nR - 1) * diff
            else:
                res[model.row_B - 1 + model.idx_B[(d, 0, 0)]] += Fraction(1, nR - 1) * diff
            res[model.row_B - 1 + model.idx_B[(0, 0, d)]] += lp["psi_Cb"][d]
        res[model.row_G - 1 + model.idx_G[(0, 0, 0)]] -= lp["c_g"]
        for d in range(d1):
            diff = lp["h_C"][d] - F2 * lp["psi_Cb"][d]
            if d == 0:
                res[model.row_G - 1 + model.idx_G[(0, 0, 0)]] += Fraction(3, nR - 2) * diff
            else:
                res[model.row_G - 1 + model.idx_G[(d, 0, 0)]] += Fraction(1, nR - 2) * diff
        for blk, mat in zip(model.blocks, psd):
            if blk["kind"] != "F":
                continue
            sz = blk["size"]
            for a in range(sz):
                for b in range(a, sz):
                    mult = F1 if a == b else F2
                    for r, v in model.block_entry_map(blk, a, b).items():
                        if r < model.row_mA:
                            res[r - 1] += mult * mat[a][b] * v

        def ev_A(u, v, t):
            tot = F0
            for i, (a, b, c) in enumerate(model.mons_A):
                val = res[model.row_A - 1 + i]
                if not val:
                    continue
                if b == c:
                    tot += val * (u ** a) * (v ** b) * (t ** c)
                else:
                    tot += val * (u ** a) * ((v ** b) * (t ** c) + (v ** c) * (t ** b))
            return tot

        def ev_B(u, v, t):
            tot = F0
            for i, (a, b, c) in enumerate(model.mons_B):
                val = res[model.row_B - 1 + i]
                if not val:
                    continue
                if a == b:
                    tot += val * (u ** a) * (v ** b) * (t ** c)
                else:
                    tot += val * ((u ** a) * (v ** b) + (u ** b) * (v ** a)) * (t ** c)
            return tot

        def ev_G(u, v, t):
            tot = F0
            for i, c in enumerate(model.mons_G):
                val = res[model.row_G - 1 + i]
                if not val:
                    continue
                orb = set((c[p[0]], c[p[1]], c[p[2]]) for p in S3_PERMS)
                tot += val * sum((u ** a) * (v ** b) * (t ** d) for a, b, d in orb)
            return tot

        def ev1(coeffs, x):
            return sum(c * (x ** d) for d, c in enumerate(coeffs))

        def ev_s(typ, u, v, t):
            tot = F0
            for k, M in F_mats[typ].items():
                Qk = model.Q[k]
                qv = sum(val * (u ** e0) * (v ** e1) * (t ** e2) for (e0, e1, e2), val in Qk.items())
                sz = len(M)
                for a in range(sz):
                    for b in range(sz):
                        tot += M[a][b] * (u ** a) * (v ** b) * qv
            return tot

        lhs = -lp["e"]
        for i in range(n):
            for j in range(i + 1, n):
                if i < 2 and j < 2:
                    lhs += ev1(lp["h_A"], G[i][j])
                elif i < 2:
                    lhs += ev1(lp["h_B"], G[i][j])
                else:
                    lhs += ev1(lp["h_C"], G[i][j])

        sum_lam = F0
        for r in range(2, n):
            sum_lam += ev_A(G[0][1], G[0][r], G[1][r])
        for p in range(2):
            for r1 in range(2, n):
                for r2 in range(r1 + 1, n):
                    sum_lam += ev_B(G[p][r1], G[p][r2], G[r1][r2])
        for r1 in range(2, n):
            for r2 in range(r1 + 1, n):
                for r3 in range(r2 + 1, n):
                    sum_lam += ev_G(G[r1][r2], G[r1][r3], G[r2][r3])
        sum_all = F0
        for i in range(n):
            typ = "P" if i < 2 else "R"
            for j in range(n):
                for l in range(n):
                    sum_all += ev_s(typ, G[i][j], G[i][l], G[j][l])

        assert lhs == sum_lam + sum_all, f"IDENTITY MISMATCH for n={n}: LHS={lhs} vs RHS={sum_lam + sum_all}"
        print(f"  [OK] Exact rational (2, {n-2}) combinatorial identity holds with ZERO error!")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--verify-cert", type=str, default=None)
    ap.add_argument("--no-identity-check", action="store_true")
    ap.add_argument("--n", type=int, default=11)
    ap.add_argument("--lo", type=str, default="-1")
    ap.add_argument("--hi", type=str, default="-1023/1024")
    ap.add_argument("--a-other", type=str, default=None)
    ap.add_argument("--M", type=int, default=6)
    ap.add_argument("--K", type=int, default=6)
    ap.add_argument("--no-upper-1m", action="store_true")
    ap.add_argument("--precision", type=int, default=200)
    ap.add_argument("--eps", type=str, default="1.0E-30")
    ap.add_argument("--sdpa-bin", type=str, default="/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
    ap.add_argument("--workdir", type=str, default=None)
    ap.add_argument("--tag", type=str, default=None)
    ap.add_argument("--k-bits", type=int, default=128)
    ap.add_argument("--skip-solve", action="store_true")
    ap.add_argument("--cert-out", type=str, default=None)
    args = ap.parse_args()

    if args.selftest:
        selftest()
        return

    if args.verify_cert:
        res = verify_certificate_file(Path(args.verify_cert), run_identity_check=not args.no_identity_check)
        print(json.dumps(res, indent=2))
        return

    lo, hi = Fraction(args.lo), Fraction(args.hi)
    a_other = Fraction(args.a_other) if args.a_other is not None else lo
    ao_sfx = "" if a_other == lo else f"_ao{str(a_other).replace('/','o').replace('-','m')}"
    tag = args.tag or (
        f"n{args.n}_strip_{str(lo).replace('/','o').replace('-','m')}_"
        f"{str(hi).replace('/','o').replace('-','m')}{ao_sfx}_M{args.M}_K{args.K}"
    )
    param_txt = (
        PARAM_SDPA.replace("1.0E-30", args.eps)
        .replace("200\tprecision", f"{args.precision}\tprecision")
    )
    model = SymStripModel(args.n, lo, hi, args.M, args.K, a_other=a_other, include_upper_1m=not args.no_upper_1m)

    def _solve_in(wdir: Path):
        wdir.mkdir(parents=True, exist_ok=True)
        dat_path = wdir / f"{tag}.dat-s"
        res_path = wdir / f"{tag}.result"
        param_path = wdir / "param.sdpa"
        param_path.write_text(param_txt)
        if args.skip_solve and res_path.exists():
            solve_s_ = 0.0
        else:
            info = model.write_dat(dat_path)
            print(f"[{tag}] Exported m={info['m']}, blks={info['n_blocks']}, entries={info['n_entries']} in {info['export_s']}s", flush=True)
            t0 = time.time()
            proc = subprocess.run([args.sdpa_bin, "-ds", str(dat_path), "-o", str(res_path), "-p", str(param_path)],
                                  capture_output=True, text=True)
            solve_s_ = time.time() - t0
            if proc.returncode != 0:
                raise RuntimeError(f"SDPA-GMP failed ({proc.returncode}): {proc.stderr[-1000:]}")
            print(f"[{tag}] SDPA-GMP finished in {solve_s_:.1f}s", flush=True)
        return model.certify_from_result(res_path, k_bits=args.k_bits), solve_s_

    if args.workdir:
        cert, solve_s = _solve_in(Path(args.workdir) / tag)
    else:
        with tempfile.TemporaryDirectory() as td:
            cert, solve_s = _solve_in(Path(td) / tag)

    out_path = Path(args.cert_out) if args.cert_out else (REPO / "certificates" / f"n{args.n}-symstrip-{tag}.json")
    payload = model.write_certificate(cert, out_path, solve_s)
    print(f"[{tag}] Written exact certificate -> {out_path}")
    print(f"  e_raw     = {float(cert['lp_raw']['e']):.16f}")
    print(f"  certified = {payload['claimed_bound_float']:.16f}  R2_max={float(cert['R2max']):.2e}")
    ver = verify_certificate_file(out_path, run_identity_check=True)
    print(f"[{tag}] VERIFY OK in {ver['verify_s']}s: identity_err={ver['identity_error']}, blocks={ver['blocks_verified']}, sha256={ver['sha256'][:16]}...")


if __name__ == "__main__":
    main()
