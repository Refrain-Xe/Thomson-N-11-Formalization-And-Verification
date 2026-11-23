#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""export_lean_upper.py — Exports an exact rational stereographic C2v configuration
`c2vWitness : Fin 11 → R3` on S^2 (zero square roots in coordinates!) and a Lean 4 proof
that `c2vWitness ∈ SphereConfig 11` and `coulombEnergy11 c2vWitness ≤ 2029822525409531 / 50000000000000`
(`= 40.59645050819062`, within `1.47e-14` of `E*(11)`).

Uses 100% pure `ℤ` arithmetic (`Int.ofNat`/`Int.negSucc` and `List.finRange 11`) inside
`decide +kernel` — zero `ℚ` GCD normalization and zero `Finset`/`Multiset` kernel reduction.
"""
from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
LEAN_STAGEB = REPO / "formal" / "lean" / "ThomsonN11" / "StageB"


def c2v_rational_points(t1: Fraction, t2: Fraction, t3: Fraction, u4: Fraction, v4: Fraction):
    pts = []
    # 0: south pole
    pts.append((Fraction(0), Fraction(0), Fraction(-1)))
    # 1, 2: xz mirror
    d1 = 1 + t1 * t1
    x1, z1 = 2 * t1 / d1, (1 - t1 * t1) / d1
    pts.append((x1, Fraction(0), z1))
    pts.append((-x1, Fraction(0), z1))
    # 3, 4: yz upper
    d2 = 1 + t2 * t2
    y2, z2 = 2 * t2 / d2, (1 - t2 * t2) / d2
    pts.append((Fraction(0), y2, z2))
    pts.append((Fraction(0), -y2, z2))
    # 5, 6: yz lower
    d3 = 1 + t3 * t3
    y3, z3 = 2 * t3 / d3, (1 - t3 * t3) / d3
    pts.append((Fraction(0), y3, z3))
    pts.append((Fraction(0), -y3, z3))
    # 7..10: general 4-orbit
    d4 = 1 + u4 * u4 + v4 * v4
    x4, y4, z4 = 2 * u4 / d4, 2 * v4 / d4, (1 - u4 * u4 - v4 * v4) / d4
    pts.append((x4, y4, z4))
    pts.append((x4, -y4, z4))
    pts.append((-x4, y4, z4))
    pts.append((-x4, -y4, z4))
    for x, y, z in pts:
        assert x * x + y * y + z * z == 1
    return pts


def fmt_z(n: int) -> str:
    return f"Int.ofNat {n}" if n >= 0 else f"Int.negSucc {-n - 1}"


def main():
    mp.mp.dps = 60
    cand = json.loads((HERE / "results" / "phase0_candidate.json").read_text())
    sp = cand["stereographic_params"]
    D_param = 10 ** 9
    rfrac = lambda s: Fraction(int(mp.nint(mp.mpf(s) * D_param)), D_param)
    t1 = rfrac(sp["t1"])
    t2 = rfrac(sp["t2"])
    t3 = rfrac(sp["t3"])
    u4 = rfrac(sp["u4"])
    v4 = rfrac(sp["v4"])

    pts = c2v_rational_points(t1, t2, t3, u4, v4)

    # Convert each rational point (x, y, z) to integer quadruple (X, Y, Z, D) with D > 0, X^2+Y^2+Z^2 = D^2
    pts_z: list[tuple[int, int, int, int]] = []
    for x, y, z in pts:
        D = math.lcm(x.denominator, y.denominator, z.denominator)
        X = int(x * D)
        Y = int(y * D)
        Z = int(z * D)
        assert D > 0 and X * X + Y * Y + Z * Z == D * D
        pts_z.append((X, Y, Z, D))

    # Common inverse-distance scale S_inv = 5 * 10^16 = 1000 * ub_den
    ub_num = 2029822525409531
    ub_den = 50000000000000
    ub_target = Fraction(ub_num, ub_den)  # = 40.59645050819062
    mult_S = 1000
    S_inv = ub_den * mult_S  # = 50_000_000_000_000_000

    u_mat = [[0 for _ in range(11)] for _ in range(11)]
    E_true = mp.mpf(0)
    u_sum = 0
    for i in range(11):
        Xi, Yi, Zi, Di = pts_z[i]
        for j in range(i + 1, 11):
            Xj, Yj, Zj, Dj = pts_z[j]
            dist_num_sq = (Xi * Dj - Xj * Di) ** 2 + (Yi * Dj - Yj * Di) ** 2 + (Zi * Dj - Zj * Di) ** 2
            assert dist_num_sq > 0
            lhs = (S_inv * Di * Dj) ** 2
            # Smallest integer u_ij > 0 with lhs <= u_ij^2 * dist_num_sq
            u_ij = math.isqrt((lhs - 1) // dist_num_sq) + 1
            while u_ij * u_ij * dist_num_sq < lhs:
                u_ij += 1
            while (u_ij - 1) > 0 and (u_ij - 1) ** 2 * dist_num_sq >= lhs:
                u_ij -= 1
            assert u_ij > 0 and lhs <= u_ij * u_ij * dist_num_sq
            u_mat[i][j] = u_ij
            u_sum += u_ij
            E_true += mp.mpf(Di * Dj) / mp.sqrt(mp.mpf(dist_num_sq))

    assert u_sum <= ub_num * mult_S, f"u_sum={u_sum} > {ub_num * mult_S}"
    E_ub_rat = Fraction(u_sum, S_inv)
    print(f"[export_lean_upper] E(c2vWitness) = {mp.nstr(E_true, 25)}")
    print(f"[export_lean_upper] Pure-Z UB     = {float(E_ub_rat):.16f} <= {ub_target} ({float(ub_target):.16f})")

    pts_z_str = ",\n  ".join(f"({fmt_z(X)}, {fmt_z(Y)}, {fmt_z(Z)}, {fmt_z(D)})" for X, Y, Z, D in pts_z)
    u_rows_str = ",\n  ".join("#[" + ", ".join(fmt_z(u_mat[i][j]) for j in range(11)) + "]" for i in range(11))

    lean_src = "\n".join([
        "import ThomsonN11.StageB.ThreePoint",
        "",
        "/-!",
        "# Thomson N = 11 — Exact Rational Stereographic C2v Witness & Upper Bound",
        "",
        "Constructs an explicit rational C2v configuration `c2vWitness : Fin 11 → R3` on the unit",
        "sphere (via rational stereographic parameters, stored as pure integer projective tuples",
        "`(X, Y, Z, D)` with `X² + Y² + Z² = D²`) and proves",
        "`coulombEnergy11 c2vWitness ≤ 2029822525409531 / 50000000000000`",
        "(`= 40.59645050819062`, within `1.5 × 10⁻¹⁴` of `E₁(11)`).",
        "-/",
        "",
        "set_option maxHeartbeats 4000000",
        "",
        "namespace ThomsonN11.StageB.UpperBound",
        "",
        "open Finset ThomsonN11.StageB",
        "",
        "def S_inv : ℤ := Int.ofNat 50000000000000000",
        "def ub_scaled : ℤ := Int.ofNat 2029822525409531000",
        "",
        "def c2vPtsZ : Array (ℤ × ℤ × ℤ × ℤ) := #[",
        f"  {pts_z_str}",
        "]",
        "",
        "def uUpperZ : Array (Array ℤ) := #[",
        f"  {u_rows_str}",
        "]",
        "",
        "def ptZ (i : Fin 11) : ℤ × ℤ × ℤ × ℤ := c2vPtsZ.getD i.val (0, 0, 1, 1)",
        "def ptX (i : Fin 11) : ℤ := (ptZ i).1",
        "def ptY (i : Fin 11) : ℤ := (ptZ i).2.1",
        "def ptZc (i : Fin 11) : ℤ := (ptZ i).2.2.1",
        "def ptD (i : Fin 11) : ℤ := (ptZ i).2.2.2",
        "def uZ (i j : Fin 11) : ℤ := (uUpperZ.getD i.val #[]).getD j.val 0",
        "",
        "def distNumSqZ (i j : Fin 11) : ℤ :=",
        "  (ptX i * ptD j - ptX j * ptD i) ^ 2 +",
        "  (ptY i * ptD j - ptY j * ptD i) ^ 2 +",
        "  (ptZc i * ptD j - ptZc j * ptD i) ^ 2",
        "",
        "theorem unit_ok : (List.finRange 11).all (fun i =>",
        "    decide (0 < ptD i ∧ (ptX i) ^ 2 + (ptY i) ^ 2 + (ptZc i) ^ 2 = (ptD i) ^ 2)) = true := by",
        "  decide +kernel",
        "",
        "theorem pair_u_ok : (List.finRange 11).all (fun i =>",
        "    (List.finRange 11).all (fun j =>",
        "      if i < j then",
        "        decide (0 < uZ i j ∧ S_inv ^ 2 * (ptD i) ^ 2 * (ptD j) ^ 2 ≤ (uZ i j) ^ 2 * distNumSqZ i j)",
        "      else",
        "        decide (uZ i j = 0))) = true := by",
        "  decide +kernel",
        "",
        "theorem energy_sum_ok :",
        "    decide ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum) ≤",
        "      ub_scaled) = true := by",
        "  decide +kernel",
        "",
        "noncomputable def c2vWitness (i : Fin 11) : R3 :=",
        "  !₂[(ptX i : ℝ) / (ptD i : ℝ), (ptY i : ℝ) / (ptD i : ℝ), (ptZc i : ℝ) / (ptD i : ℝ)]",
        "",
        "lemma ptD_pos_and_unit (i : Fin 11) :",
        "    0 < ptD i ∧ (ptX i) ^ 2 + (ptY i) ^ 2 + (ptZc i) ^ 2 = (ptD i) ^ 2 := by",
        "  have hall := unit_ok",
        "  simp only [List.all_eq_true, decide_eq_true_eq] at hall",
        "  exact hall i (List.mem_finRange i)",
        "",
        "lemma c2vWitness_unit (i : Fin 11) : ‖c2vWitness i‖ = 1 := by",
        "  obtain ⟨hdpos, hsq⟩ := ptD_pos_and_unit i",
        "  have hdR : (0 : ℝ) < (ptD i : ℝ) := by exact_mod_cast hdpos",
        "  have hdne : (ptD i : ℝ) ≠ 0 := ne_of_gt hdR",
        "  have hsqR : ((ptX i : ℝ) ^ 2 + (ptY i : ℝ) ^ 2 + (ptZc i : ℝ) ^ 2) = (ptD i : ℝ) ^ 2 := by",
        "    exact_mod_cast hsq",
        "  have hnsq : ‖c2vWitness i‖ ^ 2 = 1 := by",
        "    rw [norm_sq_R3_expand]",
        "    change ((ptX i : ℝ) / (ptD i : ℝ)) ^ 2 + ((ptY i : ℝ) / (ptD i : ℝ)) ^ 2 + ((ptZc i : ℝ) / (ptD i : ℝ)) ^ 2 = 1",
        "    field_simp [hdne]",
        "    exact hsqR",
        "  nlinarith [norm_nonneg (c2vWitness i)]",
        "",
        "lemma c2vWitness_dist_num_sq (i j : Fin 11) :",
        "    ‖c2vWitness i - c2vWitness j‖ ^ 2 * ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) =",
        "      (distNumSqZ i j : ℝ) := by",
        "  have hdi : (ptD i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (ptD_pos_and_unit i).1)",
        "  have hdj : (ptD j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (ptD_pos_and_unit j).1)",
        "  rw [norm_sq_R3_expand]",
        "  change (((ptX i : ℝ) / (ptD i : ℝ) - (ptX j : ℝ) / (ptD j : ℝ)) ^ 2 +",
        "          ((ptY i : ℝ) / (ptD i : ℝ) - (ptY j : ℝ) / (ptD j : ℝ)) ^ 2 +",
        "          ((ptZc i : ℝ) / (ptD i : ℝ) - (ptZc j : ℝ) / (ptD j : ℝ)) ^ 2) *",
        "         ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) = (distNumSqZ i j : ℝ)",
        "  unfold distNumSqZ",
        "  push_cast",
        "  field_simp [hdi, hdj]",
        "",
        "lemma pair_u_lt {i j : Fin 11} (hij : i < j) :",
        "    0 < uZ i j ∧ S_inv ^ 2 * (ptD i) ^ 2 * (ptD j) ^ 2 ≤ (uZ i j) ^ 2 * distNumSqZ i j := by",
        "  have hall := pair_u_ok",
        "  simp only [List.all_eq_true] at hall",
        "  have h1 := hall i (List.mem_finRange i) j (List.mem_finRange j)",
        "  simpa [hij] using h1",
        "",
        "lemma pair_u_not_lt {i j : Fin 11} (hnij : ¬ (i < j)) : uZ i j = 0 := by",
        "  have hall := pair_u_ok",
        "  simp only [List.all_eq_true] at hall",
        "  have h1 := hall i (List.mem_finRange i) j (List.mem_finRange j)",
        "  simpa [hnij] using h1",
        "",
        "lemma pair_prod_ge {i j : Fin 11} (hij : i < j) :",
        "    (S_inv : ℝ) ≤ (uZ i j : ℝ) * ‖c2vWitness i - c2vWitness j‖ := by",
        "  obtain ⟨hupos, hule⟩ := pair_u_lt hij",
        "  have hdi : (0 : ℝ) < (ptD i : ℝ) := by exact_mod_cast (ptD_pos_and_unit i).1",
        "  have hdj : (0 : ℝ) < (ptD j : ℝ) := by exact_mod_cast (ptD_pos_and_unit j).1",
        "  have hd2pos : (0 : ℝ) < (ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2 := by positivity",
        "  have huleR : (S_inv : ℝ) ^ 2 * ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) ≤",
        "      ((uZ i j : ℝ) ^ 2 * ‖c2vWitness i - c2vWitness j‖ ^ 2) * ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) := by",
        "    have hcast : ((S_inv ^ 2 * (ptD i) ^ 2 * (ptD j) ^ 2 : ℤ) : ℝ) ≤",
        "        (((uZ i j) ^ 2 * distNumSqZ i j : ℤ) : ℝ) := by exact_mod_cast hule",
        "    push_cast at hcast",
        "    rw [← c2vWitness_dist_num_sq i j] at hcast",
        "    linarith",
        "  have hsq : (S_inv : ℝ) ^ 2 ≤ ((uZ i j : ℝ) * ‖c2vWitness i - c2vWitness j‖) ^ 2 := by",
        "    have hcancel := le_of_mul_le_mul_right huleR hd2pos",
        "    linarith",
        "  have huR : (0 : ℝ) ≤ (uZ i j : ℝ) := le_of_lt (by exact_mod_cast hupos)",
        "  have hprod_nn : (0 : ℝ) ≤ (uZ i j : ℝ) * ‖c2vWitness i - c2vWitness j‖ :=",
        "    mul_nonneg huR (norm_nonneg _)",
        "  have hSpos : (0 : ℝ) < (S_inv : ℝ) := by norm_num [S_inv]",
        "  nlinarith",
        "",
        "lemma c2vWitness_injective : Function.Injective c2vWitness := by",
        "  intro i j heq",
        "  have hSpos : (0 : ℝ) < (S_inv : ℝ) := by norm_num [S_inv]",
        "  rcases lt_trichotomy i j with hij | rfl | hji",
        "  · have hp := pair_prod_ge hij",
        "    rw [heq, sub_self, norm_zero, mul_zero] at hp",
        "    linarith",
        "  · rfl",
        "  · have hp := pair_prod_ge hji",
        "    rw [heq, sub_self, norm_zero, mul_zero] at hp",
        "    linarith",
        "",
        "theorem c2vWitness_energy_le :",
        f"    coulombEnergy11 c2vWitness ≤ ({ub_num} / {ub_den} : ℝ) := by",
        "  have hSpos : (0 : ℝ) < (S_inv : ℝ) := by norm_num [S_inv]",
        "  have hpair : ∀ i : Fin 11, ∀ j ∈ Finset.Ioi i,",
        "      ‖c2vWitness i - c2vWitness j‖⁻¹ ≤ (uZ i j : ℝ) / (S_inv : ℝ) := by",
        "    intro i j hj",
        "    have hij : i < j := Finset.mem_Ioi.mp hj",
        "    have hp := pair_prod_ge hij",
        "    obtain ⟨hupos, _⟩ := pair_u_lt hij",
        "    have huR : (0 : ℝ) < (uZ i j : ℝ) := by exact_mod_cast hupos",
        "    have hdpos : (0 : ℝ) < ‖c2vWitness i - c2vWitness j‖ := by",
        "      by_contra hle",
        "      have hd0 : ‖c2vWitness i - c2vWitness j‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)",
        "      rw [hd0, mul_zero] at hp; linarith",
        "    rw [inv_eq_one_div, div_le_div_iff₀ hdpos hSpos]",
        "    linarith",
        "  have hsum1 : coulombEnergy11 c2vWitness ≤ ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, (uZ i j : ℝ) / (S_inv : ℝ) :=",
        "    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpair i j hj",
        "  have hIoi : ∀ i : Fin 11,",
        "      (∑ j ∈ Finset.Ioi i, (uZ i j : ℝ) / (S_inv : ℝ)) = ∑ j : Fin 11, (uZ i j : ℝ) / (S_inv : ℝ) := by",
        "    intro i",
        "    have hfilt : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp",
        "    rw [hfilt, Finset.sum_filter]",
        "    refine Finset.sum_congr rfl fun j _ => ?_",
        "    split_ifs with hij",
        "    · rfl",
        "    · rw [pair_u_not_lt hij]; simp",
        "  simp_rw [hIoi, ← Finset.sum_div] at hsum1",
        "  have hfin_sum : (∑ i : Fin 11, ∑ j : Fin 11, (uZ i j : ℝ)) =",
        "      ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum : ℤ) : ℝ) := by",
        "    simp only [Fin.sum_univ_def, Int.cast_list_sum, List.map_map, Function.comp_def]",
        "  rw [hfin_sum] at hsum1",
        "  have hsumZ : (((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum) ≤",
        "      ub_scaled := of_decide_eq_true energy_sum_ok",
        "  have hsumR : ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum : ℤ) : ℝ) ≤",
        "      (ub_scaled : ℝ) := by exact_mod_cast hsumZ",
        "  have hdiv : ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum : ℤ) : ℝ) / (S_inv : ℝ) ≤",
        "      (ub_scaled : ℝ) / (S_inv : ℝ) := div_le_div_of_nonneg_right hsumR (le_of_lt hSpos)",
        f"  have hval : (ub_scaled : ℝ) / (S_inv : ℝ) = ({ub_num} / {ub_den} : ℝ) := by norm_num [ub_scaled, S_inv]",
        "  linarith",
        "",
        "end ThomsonN11.StageB.UpperBound",
        "",
    ])
    out_p = LEAN_STAGEB / "UpperBound.lean"
    out_p.write_text(lean_src)
    print(f"[export_lean_upper] Wrote {out_p}")


if __name__ == "__main__":
    main()
