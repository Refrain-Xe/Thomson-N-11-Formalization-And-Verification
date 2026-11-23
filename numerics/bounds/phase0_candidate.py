#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""phase0_candidate.py — 60-dps high-precision stationary point, Riemannian Hessian,
and pairwise inner-product spectrum for the Thomson N = 11 C2v candidate X*_{11}
(edge-contracted icosahedron) and the runner-up C5v local minimum.

Uses rational stereographic parameterization of the 5-dimensional C2v manifold
(orbit decomposition 1 + 2 + 2 + 2 + 4 = 11):
  - p_0 = (0, 0, -1)
  - p_1, p_2 = (+/- 2*t1/(1+t1^2), 0, (1-t1^2)/(1+t1^2))                 [xz mirror]
  - p_3, p_4 = (0, +/- 2*t2/(1+t2^2), (1-t2^2)/(1+t2^2))                 [yz mirror, upper]
  - p_5, p_6 = (0, +/- 2*t3/(1+t3^2), (1-t3^2)/(1+t3^2))                 [yz mirror, lower]
  - p_7..10  = (+/- 2*u4/(1+u4^2+v4^2), +/- 2*v4/(1+u4^2+v4^2),
                (1-u4^2-v4^2)/(1+u4^2+v4^2))                             [general C2v orbit]

Every point lies identically on S^2 for all real/rational (t1, t2, t3, u4, v4).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
import mpmath as mp

DPS_SOLVE = 80
DPS_REPORT = 60


def c2v_points(params):
    """Map 5 parameters (t1, t2, t3, u4, v4) -> 11 unit vectors in (mpf^3)^11."""
    t1, t2, t3, u4, v4 = params
    zero = mp.mpf(0)
    one = mp.mpf(1)

    pts = []
    # 0: south pole (0, 0, -1) on C2 axis
    pts.append([zero, zero, -one])

    # 1, 2: xz-mirror pair
    d1 = one + t1 * t1
    x1 = 2 * t1 / d1
    z1 = (one - t1 * t1) / d1
    pts.append([x1, zero, z1])
    pts.append([-x1, zero, z1])

    # 3, 4: yz-mirror upper pair
    d2 = one + t2 * t2
    y2 = 2 * t2 / d2
    z2 = (one - t2 * t2) / d2
    pts.append([zero, y2, z2])
    pts.append([zero, -y2, z2])

    # 5, 6: yz-mirror lower pair
    d3 = one + t3 * t3
    y3 = 2 * t3 / d3
    z3 = (one - t3 * t3) / d3
    pts.append([zero, y3, z3])
    pts.append([zero, -y3, z3])

    # 7, 8, 9, 10: general 4-orbit
    d4 = one + u4 * u4 + v4 * v4
    x4 = 2 * u4 / d4
    y4 = 2 * v4 / d4
    z4 = (one - u4 * u4 - v4 * v4) / d4
    pts.append([x4, y4, z4])
    pts.append([x4, -y4, z4])
    pts.append([-x4, y4, z4])
    pts.append([-x4, -y4, z4])
    return pts


def coulomb_energy_mp(pts):
    n = len(pts)
    total = mp.mpf(0)
    for i in range(n):
        xi = pts[i]
        for j in range(i + 1, n):
            xj = pts[j]
            dx = xi[0] - xj[0]
            dy = xi[1] - xj[1]
            dz = xi[2] - xj[2]
            total += 1 / mp.sqrt(dx * dx + dy * dy + dz * dz)
    return total


def sym_grad_and_hess(params):
    """Compute gradient (5,) and Hessian (5,5) of E(c2v_points(params)) via complex-step / high-order FD
    or exact analytic chain rule. Let's use exact analytic first & second derivatives on R^33!"""
    pts = c2v_points(params)
    n = len(pts)
    # First compute ambient gradient G (11x3) and ambient Hessian H_amb (33x33) of sum_{i<j} ||x_i - x_j||^{-1}
    G = [[mp.mpf(0)] * 3 for _ in range(n)]
    H_amb = [[mp.mpf(0)] * (3 * n) for _ in range(3 * n)]
    for i in range(n):
        for j in range(i + 1, n):
            dvec = [pts[i][a] - pts[j][a] for a in range(3)]
            r2 = dvec[0] ** 2 + dvec[1] ** 2 + dvec[2] ** 2
            r = mp.sqrt(r2)
            inv_r3 = 1 / (r * r2)
            inv_r5 = inv_r3 / r2
            for a in range(3):
                g_ia = -dvec[a] * inv_r3
                G[i][a] += g_ia
                G[j][a] -= g_ia
                for b in range(3):
                    # d/dx_{j,b} (- (x_{i,a}-x_{j,a})/r^3)
                    # For d/dx_{i,b}: -(delta_{ab}/r^3 - 3 d_a d_b / r^5) = 3 d_a d_b / r^5 - delta_{ab}/r^3
                    hab = 3 * dvec[a] * dvec[b] * inv_r5 - (inv_r3 if a == b else mp.mpf(0))
                    H_amb[3 * i + a][3 * i + b] += hab
                    H_amb[3 * j + a][3 * j + b] += hab
                    H_amb[3 * i + a][3 * j + b] -= hab
                    H_amb[3 * j + a][3 * i + b] -= hab

    # Exact first and second derivatives of c2v_points(params) w.r.t. params
    t1, t2, t3, u4, v4 = params
    one = mp.mpf(1)
    zero = mp.mpf(0)

    def circle_d1_d2(t):
        # f(t) = 2t/(1+t^2), g(t) = (1-t^2)/(1+t^2)
        d = one + t * t
        d2 = d * d
        d3 = d2 * d
        fp = 2 * (one - t * t) / d2
        gp = -4 * t / d2
        fpp = 4 * t * (t * t - 3) / d3
        gpp = 4 * (3 * t * t - one) / d3
        return fp, gp, fpp, gpp

    fp1, gp1, fpp1, gpp1 = circle_d1_d2(t1)
    fp2, gp2, fpp2, gpp2 = circle_d1_d2(t2)
    fp3, gp3, fpp3, gpp3 = circle_d1_d2(t3)

    # J[33][5] and second derivatives D2[33][5][5]
    J = [[zero] * 5 for _ in range(33)]
    D2 = [[[zero] * 5 for _ in range(5)] for _ in range(33)]

    # pts 1, 2 depend on param 0 (t1)
    for idx, sgn in ((1, 1), (2, -1)):
        J[3 * idx + 0][0] = sgn * fp1
        J[3 * idx + 2][0] = gp1
        D2[3 * idx + 0][0][0] = sgn * fpp1
        D2[3 * idx + 2][0][0] = gpp1

    # pts 3, 4 depend on param 1 (t2)
    for idx, sgn in ((3, 1), (4, -1)):
        J[3 * idx + 1][1] = sgn * fp2
        J[3 * idx + 2][1] = gp2
        D2[3 * idx + 1][1][1] = sgn * fpp2
        D2[3 * idx + 2][1][1] = gpp2

    # pts 5, 6 depend on param 2 (t3)
    for idx, sgn in ((5, 1), (6, -1)):
        J[3 * idx + 1][2] = sgn * fp3
        J[3 * idx + 2][2] = gp3
        D2[3 * idx + 1][2][2] = sgn * fpp3
        D2[3 * idx + 2][2][2] = gpp3

    # pts 7..10 depend on params 3 (u4), 4 (v4)
    # x = 2u/D, y = 2v/D, z = (1 - u^2 - v^2)/D = 2/D - 1 where D = 1 + u^2 + v^2
    D = one + u4 * u4 + v4 * v4
    D_2 = D * D
    D_3 = D_2 * D
    # dx/du = 2(1 - u^2 + v^2)/D^2, dx/dv = -4uv/D^2
    xu = 2 * (one - u4 * u4 + v4 * v4) / D_2
    xv = -4 * u4 * v4 / D_2
    yu = -4 * u4 * v4 / D_2
    yv = 2 * (one + u4 * u4 - v4 * v4) / D_2
    # z = 2/D - 1 => dz/du = -4u/D^2, dz/dv = -4v/D^2
    zu = -4 * u4 / D_2
    zv = -4 * v4 / D_2

    # Second partials:
    # d/du [2(1 - u^2 + v^2)/D^2] = (-4u D - 8u(1 - u^2 + v^2))/D^3 = 4u(u^2 - 3 - 3v^2)/D^3
    xuu = 4 * u4 * (u4 * u4 - 3 - 3 * v4 * v4) / D_3
    # d/dv [-4uv/D^2] = (-4u D + 16 u v^2)/D^3 = 4u(3v^2 - 1 - u^2)/D^3
    xvv = 4 * u4 * (3 * v4 * v4 - one - u4 * u4) / D_3
    # d/dv [2(1 - u^2 + v^2)/D^2] = (4v D - 8v(1 - u^2 + v^2))/D^3 = 4v(3u^2 - 1 - v^2)/D^3
    xuv = 4 * v4 * (3 * u4 * u4 - one - v4 * v4) / D_3

    yvv = 4 * v4 * (v4 * v4 - 3 - 3 * u4 * u4) / D_3
    yuu = 4 * v4 * (3 * u4 * u4 - one - v4 * v4) / D_3
    yuv = 4 * u4 * (3 * v4 * v4 - one - u4 * u4) / D_3

    # d/du [-4u/D^2] = (-4D + 16u^2)/D^3 = 4(3u^2 - 1 - v^2)/D^3
    zuu = 4 * (3 * u4 * u4 - one - v4 * v4) / D_3
    zvv = 4 * (3 * v4 * v4 - one - u4 * u4) / D_3
    zuv = 16 * u4 * v4 / D_3

    for idx, (sx, sy) in ((7, (1, 1)), (8, (1, -1)), (9, (-1, 1)), (10, (-1, -1))):
        J[3 * idx + 0][3] = sx * xu
        J[3 * idx + 0][4] = sx * xv
        J[3 * idx + 1][3] = sy * yu
        J[3 * idx + 1][4] = sy * yv
        J[3 * idx + 2][3] = zu
        J[3 * idx + 2][4] = zv

        D2[3 * idx + 0][3][3] = sx * xuu
        D2[3 * idx + 0][3][4] = D2[3 * idx + 0][4][3] = sx * xuv
        D2[3 * idx + 0][4][4] = sx * xvv

        D2[3 * idx + 1][3][3] = sy * yuu
        D2[3 * idx + 1][3][4] = D2[3 * idx + 1][4][3] = sy * yuv
        D2[3 * idx + 1][4][4] = sy * yvv

        D2[3 * idx + 2][3][3] = zuu
        D2[3 * idx + 2][3][4] = D2[3 * idx + 2][4][3] = zuv
        D2[3 * idx + 2][4][4] = zvv

    G_flat = [G[i][a] for i in range(n) for a in range(3)]
    grad5 = mp.matrix(5, 1)
    hess5 = mp.matrix(5, 5)
    for p in range(5):
        grad5[p] = sum(G_flat[k] * J[k][p] for k in range(33))
    for p in range(5):
        for q in range(p, 5):
            val = sum(G_flat[k] * D2[k][p][q] for k in range(33))
            for k in range(33):
                if J[k][p] != 0:
                    val += J[k][p] * sum(H_amb[k][l] * J[l][q] for l in range(33) if J[l][q] != 0)
            hess5[p, q] = hess5[q, p] = val

    return pts, G, H_amb, grad5, hess5


def riemannian_grad_and_hess(pts, G, H_amb):
    """Full 22x22 Riemannian gradient and Hessian on (S^2)^11."""
    n = len(pts)
    # Tangent basis at each point x_i: two orthonormal vectors e1_i, e2_i orthogonal to x_i
    frames = []
    grad_tan = []
    for i in range(n):
        x = pts[i]
        # Pick coordinate smallest in |x_a| to cross with x
        amin = min(range(3), key=lambda a: abs(x[a]))
        u = [mp.mpf(1 if a == amin else 0) for a in range(3)]
        dot_ux = sum(u[a] * x[a] for a in range(3))
        e1 = [u[a] - dot_ux * x[a] for a in range(3)]
        n1 = mp.sqrt(sum(c * c for c in e1))
        e1 = [c / n1 for c in e1]
        e2 = [
            x[1] * e1[2] - x[2] * e1[1],
            x[2] * e1[0] - x[0] * e1[2],
            x[0] * e1[1] - x[1] * e1[0],
        ]
        frames.append((e1, e2))
        g = G[i]
        grad_tan.append(sum(g[a] * e1[a] for a in range(3)))
        grad_tan.append(sum(g[a] * e2[a] for a in range(3)))

    # Riemannian Hessian on (S^2)^n at a critical point:
    # Hess_R E(X)[v, w] = D^2 E(X)[v, w] - sum_i <G_i, X_i> <v_i, w_i>
    H_riem = mp.matrix(2 * n, 2 * n)
    gx_dots = [sum(G[i][a] * pts[i][a] for a in range(3)) for i in range(n)]
    # Build 33 x 22 basis matrix B
    B = [[mp.mpf(0)] * (2 * n) for _ in range(3 * n)]
    for i in range(n):
        e1, e2 = frames[i]
        for a in range(3):
            B[3 * i + a][2 * i] = e1[a]
            B[3 * i + a][2 * i + 1] = e2[a]

    for c1 in range(2 * n):
        for c2 in range(c1, 2 * n):
            val = mp.mpf(0)
            i1 = c1 // 2
            i2 = c2 // 2
            for a in range(3):
                b1 = B[3 * i1 + a][c1]
                for b in range(3):
                    val += b1 * H_amb[3 * i1 + a][3 * i2 + b] * B[3 * i2 + b][c2]
            if c1 == c2:
                val -= gx_dots[i1]
            H_riem[c1, c2] = H_riem[c2, c1] = val

    return grad_tan, H_riem


def solve_c5v_runner_up():
    """60-dps Newton solve for the C5v (1 + 5 + 5) vertex-removed icosahedron local minimum."""
    # Points: south pole (0,0,-1), ring 1 at height z1 (angles 2*pi*k/5), ring 2 at height z2 (angles pi/5 + 2*pi*k/5)
    def e_c5v(z1, z2):
        one = mp.mpf(1)
        r1 = mp.sqrt(one - z1 * z1)
        r2 = mp.sqrt(one - z2 * z2)
        pts = [[mp.mpf(0), mp.mpf(0), -one]]
        for k in range(5):
            th = 2 * mp.pi * k / 5
            pts.append([r1 * mp.cos(th), r1 * mp.sin(th), z1])
        for k in range(5):
            th = mp.pi / 5 + 2 * mp.pi * k / 5
            pts.append([r2 * mp.cos(th), r2 * mp.sin(th), z2])
        return coulomb_energy_mp(pts)

    # Initial guess from icosahedron without top vertex: z1 ~ 1/sqrt(5) ~ 0.447, z2 ~ -1/sqrt(5) ~ -0.447
    # Wait: top vertex removed means south pole present (-1), ring at -1/sqrt(5), ring at +1/sqrt(5) (pushed toward +1)!
    z1 = mp.mpf("0.65")
    z2 = mp.mpf("-0.25")
    h = mp.mpf("1e-25")
    for _ in range(25):
        f00 = e_c5v(z1, z2)
        fp0 = e_c5v(z1 + h, z2)
        fm0 = e_c5v(z1 - h, z2)
        f0p = e_c5v(z1, z2 + h)
        f0m = e_c5v(z1, z2 - h)
        fpp = e_c5v(z1 + h, z2 + h)
        fpm = e_c5v(z1 + h, z2 - h)
        fmp = e_c5v(z1 - h, z2 + h)
        fmm = e_c5v(z1 - h, z2 - h)
        g1 = (fp0 - fm0) / (2 * h)
        g2 = (f0p - f0m) / (2 * h)
        h11 = (fp0 - 2 * f00 + fm0) / (h * h)
        h22 = (f0p - 2 * f00 + f0m) / (h * h)
        h12 = (fpp - fpm - fmp + fmm) / (4 * h * h)
        det = h11 * h22 - h12 * h12
        dz1 = (h22 * g1 - h12 * g2) / det
        dz2 = (-h12 * g1 + h11 * g2) / det
        z1 -= dz1
        z2 -= dz2
        if max(abs(dz1), abs(dz2)) < mp.mpf("1e-55"):
            break
    return z1, z2, e_c5v(z1, z2)


def main():
    mp.mp.dps = DPS_SOLVE

    # Initial guess from reference_config.json:
    # z1 ~ 0.80595489657, x1 ~ 0.59197694608 => t1 = x1 / (1 + z1)
    # z2 ~ 0.55268146295, y2 ~ 0.83339258486 => t2 = y2 / (1 + z2)
    # z3 ~ -0.51530714119, y3 ~ 0.85700557188 => t3 = y3 / (1 + z3)
    # x4 ~ 0.85592633707, y4 ~ 0.48892240363, z4 ~ -0.16835970044 => u4 = x4/(1+z4), v4 = y4/(1+z4)
    t1 = mp.mpf("0.59197694608") / (1 + mp.mpf("0.80595489657"))
    t2 = mp.mpf("0.83339258486") / (1 + mp.mpf("0.55268146295"))
    t3 = mp.mpf("0.85700557188") / (1 + mp.mpf("-0.51530714119"))
    u4 = mp.mpf("0.85592633707") / (1 + mp.mpf("-0.16835970044"))
    v4 = mp.mpf("0.48892240363") / (1 + mp.mpf("-0.16835970044"))
    params = [t1, t2, t3, u4, v4]

    print("=== Phase 0A: 80-dps Newton Iteration on C2v 5-Parameter Manifold ===")
    for it in range(15):
        pts, G, H_amb, grad5, hess5 = sym_grad_and_hess(params)
        gnorm = max(abs(grad5[k]) for k in range(5))
        E = coulomb_energy_mp(pts)
        print(f"  iter {it:2d}: max|grad_sym| = {mp.nstr(gnorm, 6):>12s}   E = {mp.nstr(E, 35)}")
        if gnorm < mp.mpf("1e-70"):
            break
        delta = mp.lu_solve(hess5, grad5)
        for k in range(5):
            params[k] -= delta[k]

    pts, G, H_amb, grad5, hess5 = sym_grad_and_hess(params)
    E_star = coulomb_energy_mp(pts)
    grad_tan, H_riem = riemannian_grad_and_hess(pts, G, H_amb)
    max_tan_grad = max(abs(x) for x in grad_tan)

    # Eigenvalues of symmetric 5x5 Hessian and 22x22 Riemannian Hessian
    eig5, _ = mp.eighe(hess5)
    eig22, _ = mp.eighe(H_riem)
    eig5 = sorted(list(eig5))
    eig22 = sorted(list(eig22))

    assert max_tan_grad < mp.mpf("1e-65"), f"Tangential gradient too large: {max_tan_grad}"
    assert max(abs(eig22[0]), abs(eig22[1]), abs(eig22[2])) < mp.mpf("1e-65"), "3 rotational zero modes missing"
    assert eig22[3] > mp.mpf("0.01"), f"Not strictly locally minimal! lambda_4 = {eig22[3]}"

    # Pairwise inner products (55 pairs)
    pair_dots = []
    for i in range(11):
        for j in range(i + 1, 11):
            d = sum(pts[i][a] * pts[j][a] for a in range(3))
            pair_dots.append((d, i, j))
    pair_dots.sort(key=lambda x: x[0])

    # Group into exact C2v orbits (tolerance 1e-60!)
    levels = []
    for d, i, j in pair_dots:
        if levels and abs(d - levels[-1]["val"]) < mp.mpf("1e-60"):
            levels[-1]["pairs"].append((i, j))
        else:
            levels.append({"val": d, "pairs": [(i, j)]})

    gaps = [levels[k + 1]["val"] - levels[k]["val"] for k in range(len(levels) - 1)]
    g_min = min(gaps)
    g_min_idx = gaps.index(g_min)
    m_star = levels[0]["val"]

    # Runner-up C5v local minimum
    z1_c5v, z2_c5v, E_c5v = solve_c5v_runner_up()

    print("\n=== High-Precision Results (60 dps) ===")
    print(f"E*(11) [C2v]        = {mp.nstr(E_star, DPS_REPORT)}")
    print(f"E_runnerup [C5v]    = {mp.nstr(E_c5v, DPS_REPORT)}")
    print(f"E_C5v - E*(11)      = {mp.nstr(E_c5v - E_star, 20)}")
    print(f"max|grad_Riem(S^2)| = {mp.nstr(max_tan_grad, 10)}")
    print(f"SO(3) zero modes    = {[mp.nstr(x, 6) for x in eig22[:3]]}")
    print(f"lambda_min(H_0)     = {mp.nstr(eig22[3], 30)}  (smallest positive 22x22 Riem. Hessian eig)")
    print(f"lambda_max(H_0)     = {mp.nstr(eig22[-1], 20)}")
    print(f"5x5 C2v Hessian eig = {[mp.nstr(x, 15) for x in eig5]}")
    print(f"Distinct dot levels = {len(levels)} (total pairs = {sum(len(L['pairs']) for L in levels)})")
    print(f"m* (min dot prod)   = {mp.nstr(m_star, DPS_REPORT)}  (multiplicity {len(levels[0]['pairs'])}, pairs {levels[0]['pairs']})")
    print(f"2nd min dot prod    = {mp.nstr(levels[1]['val'], 30)}  (multiplicity {len(levels[1]['pairs'])}, pairs {levels[1]['pairs']})")
    print(f"g_min (level gap)   = {mp.nstr(g_min, 20)}  (between levels {g_min_idx} and {g_min_idx + 1})")

    print("\n--- All Inner-Product Levels ---")
    for idx, L in enumerate(levels):
        print(f"  L{idx:02d}: {mp.nstr(L['val'], 25):>28s}   mult={len(L['pairs'])}   rep={L['pairs'][0]}")

    out_dir = Path(__file__).resolve().parent / "results"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "phase0_candidate.json"
    payload = {
        "n": 11,
        "symmetry": "C2v",
        "orbit_decomposition": [1, 2, 2, 2, 4],
        "dps": DPS_REPORT,
        "E_star": mp.nstr(E_star, DPS_REPORT),
        "E_c5v_runner_up": mp.nstr(E_c5v, DPS_REPORT),
        "gap_to_runner_up": mp.nstr(E_c5v - E_star, 30),
        "stereographic_params": {
            "t1": mp.nstr(params[0], DPS_REPORT),
            "t2": mp.nstr(params[1], DPS_REPORT),
            "t3": mp.nstr(params[2], DPS_REPORT),
            "u4": mp.nstr(params[3], DPS_REPORT),
            "v4": mp.nstr(params[4], DPS_REPORT),
        },
        "coordinates_60dps": [[mp.nstr(c, DPS_REPORT) for c in row] for row in pts],
        "max_tangential_grad": mp.nstr(max_tan_grad, 12),
        "riemannian_hessian_zero_modes": [mp.nstr(x, 12) for x in eig22[:3]],
        "riemannian_hessian_pos_eigs": [mp.nstr(x, 30) for x in eig22[3:]],
        "lambda_min_H0": mp.nstr(eig22[3], 35),
        "c2v_subspace_hessian_eigs": [mp.nstr(x, 30) for x in eig5],
        "num_distinct_levels": len(levels),
        "m_star": mp.nstr(m_star, DPS_REPORT),
        "g_min": mp.nstr(g_min, 30),
        "g_min_levels": [g_min_idx, g_min_idx + 1],
        "levels": [
            {
                "index": idx,
                "dot": mp.nstr(L["val"], DPS_REPORT),
                "multiplicity": len(L["pairs"]),
                "pairs": L["pairs"],
            }
            for idx, L in enumerate(levels)
        ],
    }
    out_path.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"\nWrote {out_path}")


if __name__ == "__main__":
    main()
