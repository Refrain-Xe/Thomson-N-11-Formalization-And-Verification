#!/usr/bin/env python3
"""Multi-start numerical optimisation of the Thomson problem for N = 11.

Minimise the Coulomb energy E(x) = sum_{i<j} 1/||x_i - x_j|| over 11 distinct points on the
unit sphere S^2 of R^3.

Method (deterministic, seeded):
  1. N_STARTS random starts (fixed seed): uniform points on the sphere, jittered so that no
     two coincide;
  2. per start, L-BFGS-B on the unconstrained parameter u in R^{11x3}, with the points
     projected onto the sphere row by row (X_i = u_i / ||u_i||) and the analytic gradient
     pulled back through the projection;
  3. every local result polished with SLSQP under the 11 equality constraints ||x_i||^2 = 1;
  4. the best configuration is written to reference_config.json next to this script, with
     coordinates and energy formatted to 17 significant digits.

Acceptance: the best energy must reproduce the reference value
    E_1(11) = 40.596450508...
to within 1e-5; otherwise this script exits 1 (the workflow treats the exit code as a gate).

ERRATUM (recorded in README.md and PROGRESS.md): the original task brief pinned
39.783856229 as the reference energy. That number is below the true global minimum and is
unreachable; it appears in no published Thomson table. The correct value is pinned here
instead, on the strength of three independent confirmations obtained in this run:
  * this script's own multi-start search converges to 40.59645050819059 from every start
    (see PROGRESS.md for the full search log summary: 60 random starts, growth from the
    N=9/N=10 optima, basin hopping, structured ring families);
  * Wikipedia's Thomson problem table lists U(11) = 40.596450510, C2v, "edge-contracted
    icosahedron" (its N=7/8/9/10/12 rows are reproduced by this very code to <= 1e-9);
  * the Wales-Ulker Cambridge Cluster Database table lists 40.5964505 for N = 11, and its
    coordinate file (xyz/11.xyz) evaluates to 40.596475 at its 8-decimal precision with the
    same pairwise-inner-product multiset as the configuration found here.

Usage: python3 optimize.py [output.json]
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, str(Path(__file__).resolve().parent))
from energy import coulomb_energy  # noqa: E402

N = 11
N_STARTS = 60          # >= 40 random starts, as required by the project brief
SEED = 20261002
REF_ENERGY = 40.596450508   # erratum-pinned reference, see module docstring and README.md
TOL = 1e-5


def project(u: np.ndarray) -> np.ndarray:
    """Normalise each row of u onto the unit sphere (rows are never zero by construction)."""
    return u / np.linalg.norm(u, axis=1, keepdims=True)


def energy_and_grad_x(X: np.ndarray):
    """E(X) and dE/dX on R^{n x 3} (points need not be on the sphere)."""
    diff = X[:, None, :] - X[None, :, :]          # x_i - x_j
    d = np.linalg.norm(diff, axis=-1)
    np.fill_diagonal(d, np.inf)                   # excluded from every sum below
    iu = np.triu_indices(len(X), k=1)
    E = float((1.0 / d[iu]).sum())
    inv3 = d ** -3
    # dE/dx_k = sum_{j != k} -(x_k - x_j) / ||x_k - x_j||^3
    g = -(diff * inv3[:, :, None]).sum(axis=1)
    return E, g


def energy_and_grad_u(u_flat: np.ndarray):
    """Projected energy E(P(u)) and its gradient w.r.t. u (pullback through row projection)."""
    u = u_flat.reshape(N, 3)
    r = np.linalg.norm(u, axis=1, keepdims=True)
    X = u / r
    E, g = energy_and_grad_x(X)
    # dX_i/du_i = (I - X_i X_i^T) / r_i
    gu = (g - (X * g).sum(axis=1, keepdims=True) * X) / r
    return E, gu.ravel()


def slsqp_polish(X0: np.ndarray):
    """Polish with SLSQP under the constraints ||x_i||^2 - 1 = 0
    (one vector-valued constraint, analytic jacobians)."""
    def fun(X):
        E, g = energy_and_grad_x(X.reshape(N, 3))
        return E, g.ravel()

    def con_fun(X):
        return (X.reshape(N, 3) ** 2).sum(axis=1) - 1.0

    def con_jac(X):
        J = np.zeros((N, 3 * N))
        for i in range(N):
            J[i, 3 * i:3 * i + 3] = 2.0 * X[3 * i:3 * i + 3]
        return J

    res = minimize(
        fun, X0.ravel(), method="SLSQP", jac=True,
        constraints=[{"type": "eq", "fun": con_fun, "jac": con_jac}],
        options={"maxiter": 1000, "ftol": 1e-16},
    )
    return project(res.x.reshape(N, 3))


def tangential_gradient(X: np.ndarray) -> float:
    """Max |tangential component of the gradient| -- stationarity diagnostic."""
    _, g = energy_and_grad_x(X)
    g = g.reshape(len(X), 3)
    return float(np.abs(g - (X * g).sum(axis=1, keepdims=True) * X).max())


def final_polish(X: np.ndarray, rounds: int = 12) -> np.ndarray:
    """Exhaustive L-BFGS polishing of one configuration (used for the best one only)."""
    x = X.ravel().copy()
    for _ in range(rounds):
        res = minimize(energy_and_grad_u, x, jac=True, method="L-BFGS-B",
                       options={"maxiter": 200000, "ftol": 0.0, "gtol": 0.0,
                                "maxls": 200, "maxcor": 60})
        x = res.x
        Xn = project(x.reshape(N, 3))
        if tangential_gradient(Xn) < 1e-13:
            return Xn
    return project(x.reshape(N, 3))


def main() -> int:
    rng = np.random.default_rng(SEED)
    results = []   # (energy, X)
    print(f"N = {N} points on S^2, {N_STARTS} seeded random starts (seed = {SEED})")
    for k in range(N_STARTS):
        u0 = rng.normal(size=(N, 3))
        u0 += 1e-3 * rng.normal(size=(N, 3))   # jitter; keep rows away from 0
        res = minimize(energy_and_grad_u, u0.ravel(), jac=True, method="L-BFGS-B",
                       options={"maxiter": 5000, "ftol": 1e-16, "gtol": 1e-12})
        X = project(res.x.reshape(N, 3))
        X = slsqp_polish(X)
        results.append((coulomb_energy(X), X))
        if (k + 1) % 10 == 0:
            best = min(results, key=lambda t: t[0])
            print(f"  after {k + 1:3d} starts: best E = {best[0]:.12f}, this start E = {results[-1][0]:.9f}")

    results.sort(key=lambda t: t[0])
    E_best, X_best = results[0]
    X_best = final_polish(X_best)
    E_best = coulomb_energy(X_best)

    # landscape report: distinct local minima among the starts
    distinct = []
    for E, X in results:
        for E2, _ in distinct:
            if abs(E - E2) < 1e-7:
                break
        else:
            hits = sum(1 for E2, _ in results if abs(E2 - E) < 1e-7)
            distinct.append((E, hits))
    print(f"distinct local minima within 1e-7: {len(distinct)}")
    for E, hits in sorted(distinct)[:8]:
        print(f"    E = {E:.12f}   reached by {hits} start(s)")
    print(f"global best: E = {E_best:.17g}")
    print(f"stationarity: max|tangential gradient| = {tangential_gradient(X_best):.2e}, "
          f"max|row norm - 1| = {float(np.abs(np.linalg.norm(X_best, axis=1) - 1).max()):.2e}")

    # canonical output frame: rotate (an isometry, so all distances and the energy are
    # preserved exactly) so that the covariance principal axes align with the coordinate
    # axes, then fix the remaining sign/azimuth freedom by convention.
    _, _, Vt = np.linalg.svd(X_best, full_matrices=False)
    X_out = X_best @ Vt.T
    assert abs(coulomb_energy(X_out) - E_best) < 1e-12, "rotation changed the energy"
    # fix an overall sign/orientation convention: largest-z vertex first quadrant, z >= 0
    if X_out[np.argmax(X_out[:, 2]), 2] < 0:
        X_out = -X_out
    i0 = int(np.argmax(X_out[:, 2]))
    phi = float(np.arctan2(X_out[i0, 1], X_out[i0, 0]))
    cp, sp = np.cos(phi), np.sin(phi)
    X_out = np.column_stack([
        cp * X_out[:, 0] + sp * X_out[:, 1],
        -sp * X_out[:, 0] + cp * X_out[:, 1],
        X_out[:, 2],
    ])
    assert abs(coulomb_energy(X_out) - E_best) < 1e-12, "framing changed the energy"
    assert float(np.abs(np.linalg.norm(X_out, axis=1) - 1).max()) < 1e-12

    gap = abs(E_best - REF_ENERGY)
    print(f"|E_best - {REF_ENERGY}| = {gap:.3e} (tolerance {TOL:.0e})")

    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / "reference_config.json"

    def g17(x: float) -> str:
        return format(float(x), ".17g")

    doc = (
        "{\n"
        '  "n": 11,\n'
        f'  "energy": {g17(E_best)},\n'
        '  "reference_energy": 40.596450508,\n'
        f'  "abs_gap": {g17(gap)},\n'
        '  "coordinates": [\n'
        + ",\n".join(
            "    [" + ", ".join(g17(v) for v in row) + "]" for row in X_out
        )
        + "\n  ],\n"
        f'  "method": "L-BFGS-B on radial projection + SLSQP polish, {N_STARTS} random starts, seed {SEED}",\n'
        f'  "generated_by": "numerics/optimize.py"\n'
        "}\n"
    )
    out.write_text(doc, encoding="utf-8")
    print(f"wrote {out}")

    if not gap < TOL:
        print(f"FAILED: best energy {E_best!r} does not reproduce the reference {REF_ENERGY} "
              f"to within {TOL}")
        return 1
    print(f"OK: reproduced the reference energy to within {TOL}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
