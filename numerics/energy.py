#!/usr/bin/env python3
"""Coulomb energy of a point configuration in R^3.

    coulomb_energy(X) = sum_{i<j} 1 / ||x_i - x_j||

for an n x 3 array of coordinates. This mirrors the Lean definition
`ThomsonN11.coulombEnergy` (formal/lean/ComparatorChallenges/ThomsonN11.lean):
a sum over strictly ordered pairs of the inverse chordal distance. Any pair of
coincident rows gives distance 0 and hence +inf for the pair (numpy warns and
returns inf); callers that need an error should check for coincident rows first.

No third-party dependencies beyond numpy.
"""
from __future__ import annotations

import numpy as np

__all__ = ["coulomb_energy", "pairwise_distances"]


def pairwise_distances(X) -> np.ndarray:
    """Full n x n matrix of pairwise Euclidean distances (zero diagonal)."""
    X = np.asarray(X, dtype=float)
    if X.ndim != 2 or X.shape[1] != 3:
        raise ValueError(f"expected an n x 3 array, got shape {X.shape}")
    return np.linalg.norm(X[:, None, :] - X[None, :, :], axis=-1)


def coulomb_energy(X) -> float:
    """Coulomb energy sum_{i<j} 1 / ||x_i - x_j|| of the n x 3 configuration X."""
    X = np.asarray(X, dtype=float)
    if X.ndim != 2 or X.shape[1] != 3:
        raise ValueError(f"expected an n x 3 array, got shape {X.shape}")
    d = pairwise_distances(X)
    iu = np.triu_indices(X.shape[0], k=1)
    return float(np.sum(1.0 / d[iu]))


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    import json

    with open(sys.argv[1]) as f:
        cfg = json.load(f)
    print(f"coulomb_energy = {coulomb_energy(cfg['coordinates']):.17g}")
