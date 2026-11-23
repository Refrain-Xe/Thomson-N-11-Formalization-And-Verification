#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Generate publication-quality vector figures for the Thomson N = 11 paper
directly from the committed JSON ledgers in numerics/bounds/results/.

Outputs (in paper/figures/):
  - fig_c2v.{pdf,png}              (3D C2v edge-contracted icosahedron + 20-level spectrum)
  - fig_sdp_obstruction.{pdf,png}  (3-point SDP convergence ladder + 9-atom fractional-icosahedral dual measure)
  - fig_4pt_probe.{pdf,png}        (k-antipodal 3D frustration wall + coupled S_11 x O(3) 4-point SDP probe)
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
from scipy.spatial import ConvexHull

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
RESULTS = REPO / "numerics" / "bounds" / "results"

plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["DejaVu Serif", "Computer Modern Roman", "Times New Roman"],
    "mathtext.fontset": "cm",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "legend.fontsize": 8.0,
    "axes.linewidth": 0.75,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})


def load_results():
    cand = json.loads((RESULTS / "phase0_candidate.json").read_text())
    sweep = json.loads((RESULTS / "phase0_sdp_sweep.json").read_text())
    diag = json.loads((RESULTS / "phase0_gap_diagnosis.json").read_text())
    probe = json.loads((RESULTS / "phase0_4pt_probe.json").read_text())
    return cand, sweep, diag, probe


def make_fig_c2v(cand: dict) -> None:
    pts = np.array([[float(c) for c in row] for row in cand["coordinates_60dps"]])
    levels = cand["levels"]

    fig = plt.figure(figsize=(11.4, 4.5))
    ax1 = fig.add_subplot(1, 2, 1, projection="3d")
    ax2 = fig.add_subplot(1, 2, 2)

    # --- Panel (a): 3D C2v edge-contracted icosahedron ---
    u = np.linspace(0, 2 * np.pi, 48)
    v = np.linspace(0, np.pi, 24)
    xs = np.outer(np.cos(u), np.sin(v))
    ys = np.outer(np.sin(u), np.sin(v))
    zs = np.outer(np.ones_like(u), np.cos(v))
    ax1.plot_surface(xs, ys, zs, color="#dce8f2", alpha=0.14, linewidth=0, shade=True)
    ax1.plot_wireframe(xs, ys, zs, rstride=6, cstride=6, color="#8fa8bf", alpha=0.18, linewidth=0.45)

    hull = ConvexHull(pts)
    edge_faces: dict[tuple[int, int], list[np.ndarray]] = {}
    for idx_s, tri in enumerate(hull.simplices):
        normal = hull.equations[idx_s, :3]
        for a, b in ((tri[0], tri[1]), (tri[1], tri[2]), (tri[2], tri[0])):
            e = (min(int(a), int(b)), max(int(a), int(b)))
            edge_faces.setdefault(e, []).append(normal)
    true_edges = [
        e for e, norms in edge_faces.items()
        if not (len(norms) == 2 and float(np.dot(norms[0], norms[1])) > 0.9999)
    ]

    for i, j in true_edges:
        ax1.plot(
            [pts[i, 0], pts[j, 0]],
            [pts[i, 1], pts[j, 1]],
            [pts[i, 2], pts[j, 2]],
            color="#4a5568", linewidth=1.05, alpha=0.68, zorder=2,
        )

    for i, j in ((3, 6), (4, 5)):
        ax1.plot(
            [pts[i, 0], pts[j, 0]],
            [pts[i, 1], pts[j, 1]],
            [pts[i, 2], pts[j, 2]],
            color="#c1121f", linestyle="--", linewidth=1.45, alpha=0.90, zorder=3,
        )

    orbit_specs = [
        ([0], "#1d3557", "Orbit 1: south pole {0}"),
        ([1, 2], "#e63946", "Orbit 2: xz-upper {1,2}"),
        ([3, 4], "#2a9d8f", "Orbit 3: yz-upper {3,4}"),
        ([5, 6], "#d97706", "Orbit 4: yz-lower {5,6}"),
        ([7, 8, 9, 10], "#457b9d", "Orbit 5: general {7..10}"),
    ]
    for idxs, col, _ in orbit_specs:
        ax1.scatter(
            pts[idxs, 0], pts[idxs, 1], pts[idxs, 2],
            s=68, c=col, edgecolors="white", linewidths=0.9, depthshade=False, zorder=5,
        )

    # Custom subtle offsets so all 11 vertex labels sit cleanly outside their markers
    extra_offsets = {
        0: np.array([0.0, 0.0, -0.08]),
        1: np.array([0.08, -0.06, 0.06]),
        6: np.array([0.02, -0.08, -0.15]),
        7: np.array([0.14, 0.14, -0.08]),
        8: np.array([0.12, -0.08, 0.10]),
        10: np.array([-0.14, -0.14, 0.08]),
    }
    for i in range(11):
        p = pts[i] * 1.18 + extra_offsets.get(i, np.zeros(3))
        ax1.text(
            p[0], p[1], p[2], str(i),
            fontsize=8.0, fontweight="bold", color="#0f172a",
            ha="center", va="center", zorder=6,
            bbox=dict(boxstyle="circle,pad=0.06", facecolor="white", edgecolor="none", alpha=0.72),
        )

    ax1.view_init(elev=19, azim=36)
    ax1.set_box_aspect([1, 1, 1])
    ax1.set_xlim(-1.22, 1.22)
    ax1.set_ylim(-1.22, 1.22)
    ax1.set_zlim(-1.22, 1.22)
    ax1.set_axis_off()
    ax1.set_title(r"(a) $C_{2v}$ edge-contracted icosahedron $X^*_{11}$ ($1+2+2+2+4$)", pad=2)

    legend_handles = [
        Line2D([0], [0], marker="o", color="w", markerfacecolor=col, markersize=6.5, label=lbl)
        for _, col, lbl in orbit_specs
    ] + [
        Line2D([0], [0], color="#c1121f", linestyle="--", linewidth=1.4, label=r"Near-antipodal (3,6), (4,5)")
    ]
    ax1.legend(
        handles=legend_handles,
        loc="lower center", bbox_to_anchor=(0.5, -0.11),
        ncol=2, frameon=True, framealpha=0.94, edgecolor="#cbd5e1",
        columnspacing=0.9, handletextpad=0.4, fontsize=7.4,
    )

    # --- Panel (b): 20-level pairwise inner-product spectrum ---
    icosa_t = [-1.0, -1.0 / math.sqrt(5.0), 1.0 / math.sqrt(5.0)]
    for idx_ic, tic in enumerate(icosa_t):
        ax2.axvline(
            tic, color="#94a3b8", linestyle=":", linewidth=1.1, zorder=1,
            label=r"Icosahedron $N=12$ levels" if idx_ic == 0 else None,
        )

    mult_colors = {1: "#64748b", 2: "#2a9d8f", 4: "#1d3557"}
    for mval, col in ((4, mult_colors[4]), (2, mult_colors[2]), (1, mult_colors[1])):
        pts_m = [float(lv["dot"]) for lv in levels if int(lv["multiplicity"]) == mval]
        ax2.vlines(pts_m, 0, mval, color=col, linewidth=1.65, zorder=3)
        ax2.scatter(pts_m, [mval] * len(pts_m), color=col, s=34, zorder=4, label=f"Multiplicity {mval}")

    m_star = float(cand["m_star"])
    ax2.annotate(
        r"$m^* \approx -0.99902$" + "\n" + r"(mult. 2)",
        xy=(m_star, 2.04), xytext=(-0.94, 3.05),
        fontsize=7.9, color="#c1121f", fontweight="bold",
        bbox=dict(boxstyle="round,pad=0.10", facecolor="white", edgecolor="none", alpha=0.80),
        arrowprops=dict(arrowstyle="->", color="#c1121f", lw=0.95, connectionstyle="arc3,rad=0.14"),
    )
    ax2.annotate(
        r"$g_{\min} = 0.00370$" + "\n(levels 6, 7)",
        xy=(-0.467, 2.05), xytext=(-0.27, 2.65),
        fontsize=7.9, color="#1e293b",
        arrowprops=dict(arrowstyle="->", color="#475569", lw=0.85, connectionstyle="arc3,rad=0.14"),
    )
    ax2.annotate(
        r"$t_{\max} \approx +0.52191$",
        xy=(0.52191, 2.04), xytext=(0.40, 4.62),
        ha="center", fontsize=7.9, color="#1e293b",
        arrowprops=dict(arrowstyle="->", color="#475569", lw=0.85, connectionstyle="arc3,rad=-0.16"),
    )

    ax2.set_xlim(-1.09, 0.70)
    ax2.set_ylim(0, 5.55)
    ax2.set_yticks([0, 1, 2, 3, 4])
    ax2.set_xlabel(r"Pairwise inner product $t = \langle x_i, x_j \rangle$")
    ax2.set_ylabel("Pair multiplicity (sum = 55)")
    ax2.set_title(r"(b) 20 distinct inner-product orbits of $X^*_{11}$")
    ax2.grid(axis="y", alpha=0.25, linewidth=0.6)
    ax2.spines["top"].set_visible(False)
    ax2.spines["right"].set_visible(False)
    # Place legend cleanly in the empty headroom above y=4
    ax2.legend(
        loc="upper left", bbox_to_anchor=(0.01, 0.99),
        ncol=2, frameon=True, framealpha=0.94, edgecolor="#cbd5e1",
        columnspacing=0.9, handletextpad=0.4, fontsize=7.5,
    )

    fig.subplots_adjust(left=0.02, right=0.98, top=0.90, bottom=0.16, wspace=0.18)
    for ext in ("pdf", "png"):
        fig.savefig(HERE / f"fig_c2v.{ext}", dpi=240, bbox_inches="tight")
    plt.close(fig)


def make_fig_sdp_obstruction(cand: dict, sweep: dict, diag: dict) -> None:
    E_star = float(cand["E_star"])
    E_c5v = float(cand["E_c5v_runner_up"])

    glob_certs = [c for c in sweep["symcap_certificates"] if c["a0"] == "-1" and c["b0"] == "1"]
    glob_certs.sort(key=lambda c: c["M"])
    ms_sdp = [c["M"] for c in glob_certs]
    es_sdp = [c["e_certified"] for c in glob_certs]

    lp_rows = [r for r in diag["true_moment_1d_lp"] if r["M"] >= 6]
    ms_lp = [r["M"] for r in lp_rows]
    es_lp = [r["lp_bound_on_Xstar11"] for r in lp_rows]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.4))

    # --- Panel (a): 3-point SDP saturation vs E*(11) & 1D true-moment LP ---
    ax1.axhline(E_star, color="#c1121f", linewidth=1.35, label=rf"$E^*(11) = {E_star:.6f}$ ($C_{{2v}}$)")
    ax1.axhline(E_c5v, color="#64748b", linestyle="--", linewidth=1.05, label=rf"$C_{{5v}}$ runner-up (${E_c5v:.6f}$)")

    ax1.plot(
        ms_lp, es_lp, color="#2a9d8f", linestyle="-.", marker="D", markersize=5.2,
        markerfacecolor="white", markeredgewidth=1.3, linewidth=1.25,
        label=r"1D LP on true $X^*_{11}$ moments",
    )
    ax1.plot(
        ms_sdp, es_sdp, color="#1d3557", linestyle="-", marker="o", markersize=6.0,
        linewidth=1.7, label=r"Global $S_3$ 3-pt SDP ($a_0 = -1$)",
    )
    ax1.scatter([10], [40.555471704371], s=115, facecolors="none", edgecolors="#d97706", linewidths=1.8, zorder=6)
    ax1.annotate(
        "Lean 4 certified\n" + r"$(10,10)$: $40.55547$",
        xy=(10, 40.5554717), xytext=(8.2, 40.5335),
        fontsize=7.9, color="#b45309", fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#d97706", lw=1.0, connectionstyle="arc3,rad=0.14"),
    )
    ax1.annotate(
        "Stage A strongest\n" + r"$(12,12)$: $40.55696$",
        xy=(12, 40.5569603), xytext=(10.75, 40.5390),
        fontsize=7.9, color="#1d3557",
        arrowprops=dict(arrowstyle="->", color="#1d3557", lw=0.95, connectionstyle="arc3,rad=-0.12"),
    )
    ax1.annotate(
        "", xy=(12.22, E_star), xytext=(12.22, es_sdp[-1]),
        arrowprops=dict(arrowstyle="<->", color="#c1121f", lw=1.2),
    )
    ax1.text(
        12.32, 0.5 * (E_star + es_sdp[-1]),
        r"$\Delta \approx 0.0395$" + "\n(intrinsic\n3-pt gap)",
        fontsize=7.8, color="#c1121f", va="center", ha="left",
    )

    ax1.set_xlim(5.6, 13.65)
    ax1.set_ylim(40.526, 40.625)
    ax1.set_xticks([6, 7, 8, 9, 10, 11, 12])
    ax1.set_xticklabels(["(6,6)", "(7,7)", "(8,8)", "(9,9)", "(10,10)", "(11,11)", "(12,12)"])
    ax1.set_xlabel(r"Three-point SDP hierarchy order $(M, K)$")
    ax1.set_ylabel("Certified Coulomb energy bound")
    ax1.set_title(r"(a) Three-point SDP saturation vs. $E^*(11)$ and 1D LP")
    ax1.grid(True, alpha=0.25, linewidth=0.6)
    ax1.spines["top"].set_visible(False)
    ax1.spines["right"].set_visible(False)
    # Place legend cleanly in the wide open corridor between 40.562 and 40.592
    ax1.legend(
        loc="center left", bbox_to_anchor=(0.02, 0.54),
        frameon=True, framealpha=0.95, edgecolor="#cbd5e1", fontsize=7.5,
    )

    # --- Panel (b): Optimal (10,10) dual 9-atom Gauss-Christoffel pseudo-measure ---
    atoms = diag["gauss_9_atoms"]
    ts = [a["t"] for a in atoms]
    ws = [a["eff_pairs"] for a in atoms]

    for tic, lbl, dx, ha in [
        (-1.0, r"$-1$", 0.02, "left"),
        (-1.0 / math.sqrt(5.0), r"$-1/\sqrt{5}$", 0.02, "left"),
        (1.0 / math.sqrt(5.0), r"$+1/\sqrt{5}$", 0.02, "left"),
    ]:
        ax2.axvline(tic, color="#94a3b8", linestyle=":", linewidth=1.15, zorder=1)
        ax2.text(tic + dx, 22.2, lbl, fontsize=7.8, color="#475569", ha=ha, va="top")

    bar_colors = ["#c1121f" if t < -0.95 else "#1d3557" for t in ts]
    ax2.bar(ts, ws, width=0.052, color=bar_colors, edgecolor="white", linewidth=0.6, zorder=3)

    ax2.annotate(
        "3.395 fractional\nantipodal pairs\n" + r"($t_1 = -0.99964$)",
        xy=(ts[0], ws[0]), xytext=(-0.95, 11.2),
        fontsize=7.9, color="#c1121f", fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#c1121f", lw=1.0, connectionstyle="arc3,rad=0.10"),
    )
    ax2.annotate(
        "18.01 pairs\n" + r"($t_4 = -0.4357$)",
        xy=(ts[3], ws[3]), xytext=(-0.29, 18.7),
        fontsize=7.9, color="#1d3557",
        arrowprops=dict(arrowstyle="->", color="#1d3557", lw=0.9, connectionstyle="arc3,rad=-0.10"),
    )
    ax2.annotate(
        "21.87 pairs\n(14.10 + 7.76)",
        xy=(0.445, 14.3), xytext=(0.06, 15.6),
        fontsize=7.9, color="#1d3557",
        arrowprops=dict(arrowstyle="->", color="#1d3557", lw=0.9, connectionstyle="arc3,rad=0.14"),
    )

    box_txt = (
        r"$(12,12)$ harmonic parity:" + "\n"
        r"$\mathrm{tr}\,F_9 = 3.4\times 10^{-20}$ (off)" + "\n"
        r"$\mathrm{tr}\,F_{10} = 1.05\times 10^{-4}$ (on)" + "\n"
        r"$\mathrm{tr}\,F_{11} = 5.7\times 10^{-23}$ (off)"
    )
    ax2.text(
        -0.96, 19.6, box_txt, fontsize=7.3, color="#1e293b", va="top", ha="left",
        bbox=dict(boxstyle="round,pad=0.35", facecolor="#f8fafc", edgecolor="#cbd5e1", linewidth=0.75),
    )

    ax2.set_xlim(-1.08, 0.80)
    ax2.set_ylim(0, 23.0)
    ax2.set_xlabel(r"Quadrature atom location $t \in [-1, 1]$")
    ax2.set_ylabel("Effective pair weight (sum = 55)")
    ax2.set_title(r"(b) Dual $(10,10)$ 9-atom fractional-icosahedral pseudo-measure")
    ax2.grid(axis="y", alpha=0.25, linewidth=0.6)
    ax2.spines["top"].set_visible(False)
    ax2.spines["right"].set_visible(False)

    fig.tight_layout(w_pad=2.0)
    for ext in ("pdf", "png"):
        fig.savefig(HERE / f"fig_sdp_obstruction.{ext}", dpi=240, bbox_inches="tight")
    plt.close(fig)


def make_fig_4pt_probe(cand: dict, diag: dict, probe: dict) -> None:
    E_star = float(cand["E_star"])
    ladder = diag["k_antipodal_energy_ladder"]
    ks = [r["k_antipodal_pairs"] for r in ladder]
    es_k = [r["E_min"] for r in ladder]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.4, 4.4))

    # --- Panel (a): k-antipodal true S^2 energy wall vs 3-point pseudo-measure ---
    ax1.plot(ks, es_k, color="#1d3557", marker="o", markersize=6.2, linewidth=1.8, label=r"True $\mathbb{S}^2$ min with $k$ antipodal pairs")
    ax1.axhline(E_star, color="#64748b", linestyle=":", linewidth=1.0)
    ax1.fill_between(ks, 40.52, es_k, color="#e2e8f0", alpha=0.45, zorder=1)

    k_eff = diag["gauss_9_atoms"][0]["eff_pairs"]
    e_m10 = diag["e_certified_M10"]
    ax1.scatter(
        [k_eff], [e_m10], marker="*", s=165, color="#c1121f",
        edgecolors="white", linewidths=0.6, zorder=6,
        label=r"3-pt SDP $(10,10)$ pseudo-measure",
    )
    ax1.vlines(k_eff, e_m10, float(np.interp(k_eff, ks, es_k)), color="#c1121f", linestyle="--", linewidth=1.1, zorder=4)

    ax1.annotate(
        r"$k=1,2$: $+4.6\times 10^{-4},\; +1.2\times 10^{-3}$" + "\n(blocks single-pair strip)",
        xy=(1.5, 40.5973), xytext=(0.12, 40.695),
        fontsize=7.8, color="#1e293b",
        arrowprops=dict(arrowstyle="->", color="#475569", lw=0.9, connectionstyle="arc3,rad=0.12"),
    )
    ax1.annotate(
        r"$k=3$: $+0.0293$",
        xy=(3, es_k[3]), xytext=(1.90, 40.642),
        fontsize=7.8, color="#1d3557",
        arrowprops=dict(arrowstyle="->", color="#1d3557", lw=0.85),
    )
    ax1.annotate(
        r"$k=4$: $+0.1840$",
        xy=(4, es_k[4]), xytext=(2.55, 40.790),
        fontsize=7.8, color="#1d3557",
        arrowprops=dict(arrowstyle="->", color="#1d3557", lw=0.85),
    )
    ax1.annotate(
        r"$k_{\mathrm{eff}} = 3.395$" + "\n" + r"$E = 40.5555$" + "\n" + r"(bypasses $\det G_4 = 0$)",
        xy=(k_eff, e_m10), xytext=(3.68, 40.562),
        va="center", fontsize=7.7, color="#c1121f", fontweight="bold",
        arrowprops=dict(arrowstyle="->", color="#c1121f", lw=0.95),
    )

    ax1.set_xlim(-0.25, 5.25)
    ax1.set_ylim(40.525, 40.935)
    ax1.set_xticks([0, 1, 2, 3, 4, 5])
    ax1.set_xlabel(r"Number of antipodal pairs $k$ ($x_{2r-1} = -x_{2r}$)")
    ax1.set_ylabel("Minimum Coulomb energy")
    ax1.set_title(r"(a) True $\mathbb{R}^3$ antipodal frustration vs. 3-pt pseudo-measure")
    ax1.grid(True, alpha=0.25, linewidth=0.6)
    ax1.spines["top"].set_visible(False)
    ax1.spines["right"].set_visible(False)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94, edgecolor="#cbd5e1", fontsize=7.6)

    # --- Panel (b): Coupled S_11 x O(3) 4-point SDP hierarchy probe ---
    runs = probe["runs"]
    by_key = {(r["M"], r["D4"]): r["e_raw"] for r in runs}

    labels = [
        r"$M=4$" + "\n" + r"($D_3=6$)",
        r"$M=5$" + "\n" + r"($D_3=8$)",
        r"$M=8$" + "\n" + r"($D_3=14$)",
    ]
    x = np.arange(len(labels))
    w = 0.22

    # Monotonic left-to-right ordering of D4 within each group
    ax2.bar([0 - 0.5 * w, 1 - w, 2 - w],
            [by_key[(4, 0)], by_key[(5, 0)], by_key[(8, 0)]],
            width=w, color="#94a3b8", edgecolor="white", label=r"3-pt SDP ($D_4 = 0$)")
    ax2.bar([2],
            [by_key[(8, 4)]],
            width=w, color="#457b9d", edgecolor="white", hatch="///", label=r"Coupled 3+4-pt ($D_4 = 4$)")
    ax2.bar([0 + 0.5 * w, 1, 2 + w],
            [by_key[(4, 6)], by_key[(5, 6)], by_key[(8, 6)]],
            width=w, color="#2a9d8f", edgecolor="white", label=r"Coupled 3+4-pt ($D_4 = 6$)")
    ax2.bar([1 + w],
            [by_key[(5, 8)]],
            width=w, color="#1d3557", edgecolor="white", label=r"Coupled 3+4-pt ($D_4 = 8$)")

    ax2.axhline(E_star, color="#c1121f", linewidth=1.25, label=rf"$E^*(11) = {E_star:.5f}$")
    ax2.axhline(diag["e_certified_M12"], color="#d97706", linestyle="--", linewidth=1.1, label=r"3-pt $(12,12)$: $40.55696$")

    ax2.annotate(
        r"$+0.1631$",
        xy=(0.5 * w, by_key[(4, 6)]), xytext=(0.5 * w, by_key[(4, 6)] + 0.023),
        ha="center", fontsize=8.1, fontweight="bold", color="#0f766e",
        arrowprops=dict(arrowstyle="->", color="#0f766e", lw=0.85),
    )
    ax2.annotate(
        r"$+0.00782$",
        xy=(1 + w, by_key[(5, 8)]), xytext=(1 + w, by_key[(5, 8)] + 0.024),
        ha="center", fontsize=8.1, fontweight="bold", color="#1d3557",
        arrowprops=dict(arrowstyle="->", color="#1d3557", lw=0.85),
    )
    ax2.text(
        2.0, 40.576, r"gain $< 10^{-11}$" + "\n" + r"(need $D_4 \geq 14$)",
        ha="center", va="center", fontsize=7.8, color="#334155",
    )

    ax2.set_xticks(x)
    ax2.set_xticklabels(labels)
    ax2.set_ylim(40.295, 40.665)
    ax2.set_ylabel("SDP lower bound")
    ax2.set_title(r"(b) Coupled $S_{11} \times O(3)$ 4-point SDP hierarchy probe")
    ax2.grid(axis="y", alpha=0.25, linewidth=0.6)
    ax2.spines["top"].set_visible(False)
    ax2.spines["right"].set_visible(False)
    # Place legend cleanly in the wide headroom above E*(11) across the top
    ax2.legend(
        loc="upper center", bbox_to_anchor=(0.5, 0.995),
        ncol=2, frameon=True, framealpha=0.95, edgecolor="#cbd5e1",
        columnspacing=0.9, handletextpad=0.45, fontsize=7.1,
    )

    fig.tight_layout(w_pad=2.0)
    for ext in ("pdf", "png"):
        fig.savefig(HERE / f"fig_4pt_probe.{ext}", dpi=240, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    cand, sweep, diag, probe = load_results()
    make_fig_c2v(cand)
    make_fig_sdp_obstruction(cand, sweep, diag)
    make_fig_4pt_probe(cand, diag, probe)
    print(f"Generated figures in {HERE}")


if __name__ == "__main__":
    main()
