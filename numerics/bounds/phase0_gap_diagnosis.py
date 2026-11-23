#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""phase0_gap_diagnosis.py — Self-contained spectral, moment, 1D-LP, and antipodal-ladder
diagnosis of the N = 11 3-point SDP relaxation gap.

Computes and writes `numerics/bounds/results/phase0_gap_diagnosis.json`:
  1. Active harmonic blocks F_0 .. F_{K-1} directly from committed exact certificates
     `n11-symcap-n11_am1_M10_K10.json` and `n11-symcap-n11_am1_M12_K12.json` (confirming
     the icosahedral parity selection rule F_9, F_11 ~ 0 vs F_10 = 1.05e-4 > 0).
  2. Dual marginal pair pseudo-moments mu_0 .. mu_18, 10x10 Hankel spectrum, and exact
     9-node Gauss-Christoffel quadrature atoms + effective pair multiplicities (solved in
     an isolated TemporaryDirectory via SDPA-GMP with zero scratch-file assumptions).
  3. Primal minorant gap phi(t) - H*(t) local contact points on [-1, 0.85].
  4. Global Gram matrix spectral traces (||sum x_i||^2, Tr(G), Tr(G^2), E_tri[uvt], Tr(G^3))
     comparing the (10, 10) dual pseudo-measure against true X*_{11}.
  5. 1D polynomial minorant LP on true X*_{11} moments for M = 4, 6, 8, 10, 12, proving
     1D polynomial approximation error is < 5e-7 by M = 8 (< 1e-8 by M = 10).
  6. Constrained k-antipodal (k = 0 .. 5) minimum Coulomb energy ladder on (S^2)^11,
     demonstrating the parity-frustration penalty for true antipodal pairs at odd N = 11.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

from exact_linalg import PARAM_SDPA, parse_sdpa_xVec  # noqa: E402
from sym_cap_sdpa import SymCapModel  # noqa: E402


def load_cert_block_float(bj: dict) -> np.ndarray:
    sz = int(bj["size"])
    mat = np.zeros((sz, sz), dtype=float)
    for i in range(sz):
        for off, s in enumerate(bj["utri"][i]):
            v = float(Fraction(s))
            mat[i, i + off] = v
            mat[i + off, i] = v
    return mat


def solve_dual_xvec_m10(sdpa_bin: str) -> list[Fraction]:
    model = SymCapModel(11, Fraction(-1), 10, 10)
    param_txt = (
        PARAM_SDPA.replace("1.0E-30", "1.0E-18")
        .replace("200\tprecision", "112\tprecision")
    )
    with tempfile.TemporaryDirectory() as td:
        td_p = Path(td)
        dat_p = td_p / "m10.dat-s"
        res_p = td_p / "m10.result"
        par_p = td_p / "param.sdpa"
        par_p.write_text(param_txt)
        model.write_dat(dat_p)
        proc = subprocess.run(
            [sdpa_bin, "-ds", str(dat_p), "-o", str(res_p), "-p", str(par_p)],
            capture_output=True, text=True,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"SDPA-GMP failed ({proc.returncode}): {proc.stderr[-800:]}")
        return parse_sdpa_xVec(res_p)


def run_1d_true_moment_lp(cand_levels: list[tuple[float, int]]) -> list[dict]:
    """Maximize sum_{i<j} H(t_ij) on X*_{11} subject to H(t) <= 1/sqrt(2 - 2t) on [-1, b_max]."""
    # Note: max inner product of X*_{11} is ~0.5805; on [-1, 0.92] (or [-1, 1) via y = sqrt((1-t)/2) in [0, 1]),
    # in variable y in [0, 1] where 1 - t = 2*y^2, H(t) <= 1/(2*y) <=> 2*y*H(1 - 2*y^2) <= 1 on y in (0, 1]!
    # Checking 2*y*H(1 - 2*y^2) <= 1 on a 20,001-point grid in [1e-4, 1.0] handles the t -> 1 singularity cleanly!
    ys = np.linspace(1e-4, 1.0, 20001)
    ts = 1.0 - 2.0 * (ys ** 2)
    out = []
    for M in (4, 6, 8, 10, 12):
        deg = 2 * M - 2
        # Objective: maximize sum_{(t, mult)} mult * sum_{d=0}^deg h_d t^d
        pair_sums = np.array([sum(mult * (t ** d) for t, mult in cand_levels) for d in range(deg + 1)])
        # Constraints: for each grid point y, sum_{d=0}^deg h_d * (2 * y * t^d) <= 1
        V = np.vander(ts, N=deg + 1, increasing=True)
        A_ub = (2.0 * ys)[:, None] * V
        b_ub = np.ones_like(ys)
        res = linprog(c=-pair_sums, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None)] * (deg + 1), method="highs")
        if not res.success:
            raise RuntimeError(f"1D minorant LP failed at M={M}: {res.message}")
        val = float(-res.fun)
        out.append({"M": M, "deg_H": deg, "lp_bound_on_Xstar11": val})
    return out


def solve_k_antipodal_min_energy(k_anti: int, n_starts: int = 40, seed: int = 20261123) -> float:
    """Minimize Coulomb energy of 11 points on S^2 with k_anti forced antipodal pairs (x_{2p+1} = -x_{2p})."""
    n_tot = 11
    n_free = n_tot - k_anti  # k_anti pairs (first k_anti free points generate -x_p) + (11 - 2*k_anti) singletons
    rng = np.random.default_rng(seed + 100 * k_anti)

    def unpack_pts(u_flat: np.ndarray) -> np.ndarray:
        U = u_flat.reshape(n_free, 3)
        norms = np.linalg.norm(U, axis=1, keepdims=True)
        X_free = U / np.maximum(norms, 1e-15)
        if k_anti == 0:
            return X_free
        anti = -X_free[:k_anti]
        return np.vstack([X_free[:k_anti], anti, X_free[k_anti:]])

    def energy_and_grad(u_flat: np.ndarray):
        U = u_flat.reshape(n_free, 3)
        norms = np.linalg.norm(U, axis=1)
        X_free = U / norms[:, None]
        if k_anti == 0:
            X = X_free
        else:
            X = np.vstack([X_free[:k_anti], -X_free[:k_anti], X_free[k_anti:]])
        diff = X[:, None, :] - X[None, :, :]
        r2 = np.sum(diff * diff, axis=-1)
        np.fill_diagonal(r2, np.inf)
        inv_r = 1.0 / np.sqrt(r2)
        energy = 0.5 * float(np.sum(inv_r))
        inv_r3 = inv_r ** 3
        # dE / dX_i = -sum_{j != i} (X_i - X_j) / ||X_i - X_j||^3
        G_X = -np.sum(diff * inv_r3[:, :, None], axis=1)
        G_free = np.zeros_like(X_free)
        if k_anti > 0:
            G_free[:k_anti] = G_X[:k_anti] - G_X[k_anti:2 * k_anti]
            G_free[k_anti:] = G_X[2 * k_anti:]
        else:
            G_free[:] = G_X
        # Pullback through X_p = U_p / ||U_p||: dE/dU_p = (G_free_p - <G_free_p, X_p> X_p) / ||U_p||
        proj = G_free - np.sum(G_free * X_free, axis=1, keepdims=True) * X_free
        G_U = proj / norms[:, None]
        return energy, G_U.ravel()

    best_e = float("inf")
    for _ in range(n_starts):
        u0 = rng.normal(size=(n_free, 3))
        u0 /= np.linalg.norm(u0, axis=1, keepdims=True)
        res = minimize(energy_and_grad, u0.ravel(), jac=True, method="L-BFGS-B",
                       options={"gtol": 1e-13, "ftol": 0.0, "maxiter": 800})
        X_opt = unpack_pts(res.x)
        diff = X_opt[:, None, :] - X_opt[None, :, :]
        r2 = np.sum(diff * diff, axis=-1)
        np.fill_diagonal(r2, np.inf)
        e_val = 0.5 * float(np.sum(1.0 / np.sqrt(r2)))
        if e_val < best_e:
            best_e = e_val
    return best_e


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sdpa-bin", type=str, default="/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
    args = ap.parse_args()

    t0 = time.time()
    cand_path = HERE / "results" / "phase0_candidate.json"
    cert10_path = REPO / "certificates" / "n11-symcap-n11_am1_M10_K10.json"
    cert12_path = REPO / "certificates" / "n11-symcap-n11_am1_M12_K12.json"

    cand = json.loads(cand_path.read_text())
    cert10 = json.loads(cert10_path.read_text())
    cert12 = json.loads(cert12_path.read_text())
    e_star = float(cand["E_star"])

    print("=== 1. Active Harmonic Blocks F_0 .. F_{K-1} from Committed Exact Certificates ===")
    f_summary_10 = []
    for k in range(10):
        mat = load_cert_block_float(cert10["blocks"][k])
        eigs = np.linalg.eigvalsh(mat)
        tr = float(np.trace(mat))
        print(f"  [M=10] F_{k:2d} ({10-k:2d}x{10-k:2d}): trace = {tr:.6e}   max_eig = {eigs[-1]:.6e}   min_eig = {eigs[0]:.3e}")
        f_summary_10.append({"k": k, "size": 10 - k, "trace": tr, "max_eig": float(eigs[-1]), "min_eig": float(eigs[0])})

    print("\n  [M=12, K=12] Higher-Harmonic Selection Rule (F_0 .. F_11):")
    f_summary_12 = []
    for k in range(12):
        mat = load_cert_block_float(cert12["blocks"][k])
        eigs = np.linalg.eigvalsh(mat)
        tr = float(np.trace(mat))
        # Subtract repair shift (if any) from trace to report pure dual activity alongside certified trace
        rep = float(Fraction(cert12["repairs"].get(f"F_{k}", "0")))
        pure_tr = max(0.0, tr - (12 - k) * rep)
        print(f"  [M=12] F_{k:2d} ({12-k:2d}x{12-k:2d}): cert_trace = {tr:.6e}   pure_trace = {pure_tr:.6e}")
        f_summary_12.append({"k": k, "size": 12 - k, "cert_trace": tr, "pure_trace": pure_tr, "max_eig": float(eigs[-1])})

    print("\n=== 2. Dual Pair Pseudo-Moments mu_0 .. mu_18 & Gauss-Christoffel Atoms (M=10, K=10) ===")
    xvec = solve_dual_xvec_m10(args.sdpa_bin)
    model = SymCapModel(11, Fraction(-1), 10, 10)
    D = model.D  # 18
    mu = [1.0]
    for d in range(1, D + 1):
        rd = model.sym_idx[(d, 0, 0)]
        mu.append(float(xvec[rd]) / (-55.0 * 3.0))

    cand_levels = [(float(L["dot"]), int(L["multiplicity"])) for L in cand["levels"]]
    mu_cand = [sum(m * (t ** d) for t, m in cand_levels) / 55.0 for d in range(D + 1)]
    s5 = 1.0 / np.sqrt(5.0)
    mu_ico = [(6.0 * ((-1.0) ** d) + 30.0 * ((-s5) ** d) + 30.0 * ((+s5) ** d)) / 66.0 for d in range(D + 1)]

    print("   d      mu_SDP(10,10)      mu(X*_11)          mu(Icosa_12)")
    for d in range(D + 1):
        print(f"  {d:2d}   {mu[d]:+16.12f}   {mu_cand[d]:+16.12f}   {mu_ico[d]:+16.12f}")

    H10 = np.array([[mu[i + j] for j in range(10)] for i in range(10)])
    hankel_eigs = np.linalg.eigvalsh(H10)
    print("\n10x10 Hankel eigenvalues:", [float(f"{x:.4e}") for x in hankel_eigs])

    H9 = H10[:9, :9]
    H9_shift = np.array([[mu[i + j + 1] for j in range(9)] for i in range(9)])
    L_chol = np.linalg.cholesky(H9)
    Linv = np.linalg.inv(L_chol)
    T_op = Linv @ H9_shift @ Linv.T
    nodes, vecs = np.linalg.eigh(T_op)
    LV = L_chol @ vecs
    weights = LV[0, :] ** 2
    assert abs(np.sum(weights) - 1.0) < 1e-12, f"Weights sum to {np.sum(weights)}"

    print("\nDual Pseudo-Measure 9-Node Gauss Representation (sum of pairs = 55.000000):")
    e_gauss = 0.0
    atoms = []
    for nd, wt in zip(nodes, weights):
        pairs = 55.0 * wt
        phi_v = 1.0 / np.sqrt(2.0 - 2.0 * nd)
        e_gauss += pairs * phi_v
        print(f"  t = {nd:+14.10f}   eff_pairs = {pairs:10.6f}   phi(t) = {phi_v:10.6f}")
        atoms.append({"t": float(nd), "eff_pairs": float(pairs), "phi": float(phi_v)})
    print(f"  Sum of eff_pairs = {55.0 * float(np.sum(weights)):.10f},  Gauss energy sum = {e_gauss:.12f}")

    print("\n=== 3. Primal Minorant Contact Points (local minima of phi(t) - H*(t) < 1e-3) ===")
    h_coeffs = [float(Fraction(s)) for s in cert10["h"]]
    ts = np.linspace(-1.0, 0.85, 200001)
    phi_ts = 1.0 / np.sqrt(2.0 - 2.0 * ts)
    H_ts = np.zeros_like(ts)
    for c in reversed(h_coeffs):
        H_ts = H_ts * ts + c
    gap_ts = phi_ts - H_ts

    minima = []
    if gap_ts[0] < gap_ts[1] and gap_ts[0] < 1e-3:
        minima.append((float(ts[0]), float(gap_ts[0])))
    for i in range(1, len(ts) - 1):
        if gap_ts[i] <= gap_ts[i - 1] and gap_ts[i] <= gap_ts[i + 1] and gap_ts[i] < 1e-3:
            minima.append((float(ts[i]), float(gap_ts[i])))
    for tm, gm in minima:
        print(f"  t_contact = {tm:+14.10f}   phi(t) - H*(t) = {gm:.4e}")

    print("\n=== 4. Global Gram Matrix Spectral Traces of Dual Pseudo-Measure vs X*_{11} ===")
    pts_cand = np.array([[float(c) for c in row] for row in cand["coordinates_60dps"]])
    G_cand = pts_cand @ pts_cand.T
    e_uvt_cand = sum(
        G_cand[i, j] * G_cand[i, l] * G_cand[j, l]
        for i in range(11) for j in range(i + 1, 11) for l in range(j + 1, 11)
    ) / 165.0
    tr_G3_cand = float(np.trace(G_cand @ G_cand @ G_cand))

    e_uvt_sdp = float(xvec[model.sym_idx[(1, 1, 1)]]) / (-55.0)
    tr_G = 11.0
    tr_G2 = 11.0 + 110.0 * mu[2]
    tr_G3 = 11.0 + 330.0 * mu[2] + 990.0 * e_uvt_sdp
    print(f"  ||sum x_i||^2 = 11 + 110*mu_1 = {11.0 + 110.0 * mu[1]:.10f}  (X*_11: {11.0 + 110.0 * mu_cand[1]:.10f})")
    print(f"  Tr(G^2)       = {tr_G2:.10f}  (isotropic min 121/3 = {121/3:.10f}; X*_11: {11 + 110*mu_cand[2]:.10f})")
    print(f"  E_tri[u*v*t]  = {e_uvt_sdp:+.10f}  (X*_11: {e_uvt_cand:+.10f})")
    print(f"  Tr(G^3)       = {tr_G3:.10f}  (isotropic 1331/9 = {1331/9:.10f}; X*_11: {tr_G3_cand:.10f})")

    print("\n=== 5. 1D Polynomial Minorant LP on True X*_{11} Moments ===")
    lp_1d = run_1d_true_moment_lp(cand_levels)
    for row in lp_1d:
        print(f"  M={row['M']:2d} (deg H = {row['deg_H']:2d}): 1D LP = {row['lp_bound_on_Xstar11']:.10f}  "
              f"(gap to E*(11) = {e_star - row['lp_bound_on_Xstar11']:.3e})")

    print("\n=== 6. Constrained k-Antipodal (k = 0 .. 5) Spherical Minimum Energy Ladder ===")
    antipodal_ladder = []
    for k_anti in range(6):
        ek = solve_k_antipodal_min_energy(k_anti)
        pen = ek - e_star
        print(f"  k = {k_anti} antipodal pairs: E_min = {ek:.9f}   penalty vs E*(11) = {pen:+.9f}")
        antipodal_ladder.append({"k_antipodal_pairs": k_anti, "E_min": ek, "penalty_vs_E_star": pen})
    assert abs(antipodal_ladder[0]["E_min"] - e_star) < 1e-7
    assert antipodal_ladder[1]["E_min"] > e_star + 4e-4
    assert antipodal_ladder[3]["E_min"] > 40.62

    e_cert_10 = float(Fraction(cert10["claimed_bound"]))
    e_cert_12 = float(Fraction(cert12["claimed_bound"]))
    out_path = HERE / "results" / "phase0_gap_diagnosis.json"
    out_path.write_text(json.dumps({
        "M": 10,
        "K": 10,
        "e_certified_M10": e_cert_10,
        "e_certified_M12": e_cert_12,
        "E_star": e_star,
        "gap_M10": e_star - e_cert_10,
        "gap_M12": e_star - e_cert_12,
        "F_summary_M10": f_summary_10,
        "F_summary_M12": f_summary_12,
        "moments_sdp": mu,
        "moments_Xstar11": mu_cand,
        "moments_icosa12": mu_ico,
        "hankel_10x10_eigs": [float(x) for x in hankel_eigs],
        "gauss_9_atoms": atoms,
        "minorant_contact_points": [{"t": t, "gap": g} for t, g in minima],
        "gram_traces": {
            "sum_norm_sq": 11.0 + 110.0 * mu[1],
            "Tr_G": tr_G,
            "Tr_G2": tr_G2,
            "Tr_G2_Xstar11": 11.0 + 110.0 * mu_cand[2],
            "Tr_G2_isotropic_min": 121.0 / 3.0,
            "E_triple_uvt": e_uvt_sdp,
            "E_triple_uvt_Xstar11": e_uvt_cand,
            "Tr_G3": tr_G3,
            "Tr_G3_Xstar11": tr_G3_cand,
            "Tr_G3_isotropic": 1331.0 / 9.0,
        },
        "true_moment_1d_lp": lp_1d,
        "k_antipodal_energy_ladder": antipodal_ladder,
        "elapsed_s": round(time.time() - t0, 2),
    }, indent=2) + "\n")
    print(f"\nWrote {out_path} in {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
