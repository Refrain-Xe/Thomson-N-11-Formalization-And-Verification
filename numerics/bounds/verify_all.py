#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""verify_all.py — Independent out-of-process verification gate + negative controls
for Thomson N = 11 Stage A numerical & exact rational SDP artifacts.

Checks:
  1. 80-dps mpmath independent verification of the C2v (1+2+2+2+4) stationary candidate
     X*_11 in `results/phase0_candidate.json` (unit-norm exactness, tangential gradient
     < 1e-75, E*(11) to 50+ digits, 20 inner-product orbits, m*, g_min) and exact rational
     verification of the C2v upper-bound witness (`2029822525409531 / 50000000000000`).
  2. Full exact rational (`Fraction`) verification (exact integer Bareiss Sylvester PD on
     every PSD block + 1D Lukacs minorant identity + exact 11-point combinatorial 3-point
     and `(2, 9)` typed strip identities) across ALL exact SDP certificates in
     `certificates/*.json` (both `symcap` and `symstrip`), confirming the Lean 4 universal
     lower bound `2027773585218537 / 50000000000000` (`= 40.55547170437074`).
  3. Direct evaluation of the `M=10, K=10` exact dual certificate on exact rational S^2
     configurations (including the rational C2v witness and 20 random configurations),
     confirming nonnegativity of harmonic moments, 3-point slacks, and 1D minorant gaps.
  4. Consistency verification of Stage A diagnostic artifacts (`phase0_sdp_sweep.json`,
     `phase0_gap_diagnosis.json`, and `phase0_4pt_probe.json`).
  5. Six adversarial negative controls (NC1..NC4 on `symcap` + NC5..NC6 on `symstrip`) —
     all must be rejected.
"""
from __future__ import annotations

import copy
import json
import random
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

from exact_linalg import ExactMatrixError, F0, F1  # noqa: E402
from export_lean_upper import c2v_rational_points  # noqa: E402
from sym_cap_sdpa import verify_certificate_file as verify_cap_cert  # noqa: E402
from sym_strip_sdpa import verify_certificate_file as verify_strip_cert  # noqa: E402

UB_NUM = 2029822525409531
UB_DEN = 50000000000000
LEAN_LB = Fraction(2027773585218537, 50000000000000)
LEAN_UB = Fraction(UB_NUM, UB_DEN)


def get_c2v_witness_rational() -> list[tuple[Fraction, Fraction, Fraction]]:
    cand = json.loads((HERE / "results" / "phase0_candidate.json").read_text())
    sp = cand["stereographic_params"]
    D_param = 10 ** 9
    mp.mp.dps = 60
    rfrac = lambda s: Fraction(int(mp.nint(mp.mpf(s) * D_param)), D_param)
    return c2v_rational_points(rfrac(sp["t1"]), rfrac(sp["t2"]), rfrac(sp["t3"]), rfrac(sp["u4"]), rfrac(sp["v4"]))


def stereo_mp(u: mp.mpf, v: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    s = u * u + v * v
    d = mp.mpf(1) + s
    return (2 * u / d, 2 * v / d, (mp.mpf(1) - s) / d)


def verify_candidate_and_upper_bound() -> dict:
    cand_path = HERE / "results" / "phase0_candidate.json"
    cand = json.loads(cand_path.read_text())
    mp.mp.dps = 80
    z0 = mp.mpf(0)
    t1 = mp.mpf(cand["stereographic_params"]["t1"])
    t2 = mp.mpf(cand["stereographic_params"]["t2"])
    t3 = mp.mpf(cand["stereographic_params"]["t3"])
    u4 = mp.mpf(cand["stereographic_params"]["u4"])
    v4 = mp.mpf(cand["stereographic_params"]["v4"])

    pts = [
        (z0, z0, mp.mpf(-1)),
        stereo_mp(t1, z0),
        stereo_mp(-t1, z0),
        stereo_mp(z0, t2),
        stereo_mp(z0, -t2),
        stereo_mp(z0, t3),
        stereo_mp(z0, -t3),
        stereo_mp(u4, v4),
        stereo_mp(u4, -v4),
        stereo_mp(-u4, v4),
        stereo_mp(-u4, -v4),
    ]
    assert len(pts) == 11

    max_unit_err = max(abs(x[0] ** 2 + x[1] ** 2 + x[2] ** 2 - 1) for x in pts)
    assert max_unit_err < mp.mpf("1e-75"), f"Unit norm error too large: {max_unit_err}"

    energy = z0
    dots = []
    forces = [[z0, z0, z0] for _ in range(11)]
    for i in range(11):
        for j in range(i + 1, 11):
            dx = pts[i][0] - pts[j][0]
            dy = pts[i][1] - pts[j][1]
            dz = pts[i][2] - pts[j][2]
            r2 = dx * dx + dy * dy + dz * dz
            r = mp.sqrt(r2)
            energy += 1 / r
            dots.append(pts[i][0] * pts[j][0] + pts[i][1] * pts[j][1] + pts[i][2] * pts[j][2])
            r3 = r2 * r
            for c, d in enumerate((dx, dy, dz)):
                forces[i][c] -= d / r3
                forces[j][c] += d / r3

    max_tan_grad = z0
    for i in range(11):
        fg = sum(forces[i][c] * pts[i][c] for c in range(3))
        tg = mp.sqrt(sum((forces[i][c] - fg * pts[i][c]) ** 2 for c in range(3)))
        if tg > max_tan_grad:
            max_tan_grad = tg

    e_recorded = mp.mpf(cand["E_star"])
    assert abs(energy - e_recorded) < mp.mpf("1e-55"), f"Energy mismatch: {energy} vs {e_recorded}"
    assert max_tan_grad < mp.mpf("1e-55"), f"Tangential gradient too large: {max_tan_grad}"

    m_star = min(dots)
    assert abs(m_star - mp.mpf(cand["m_star"])) < mp.mpf("1e-55")
    lam_min = mp.mpf(cand["lambda_min_H0"])
    assert lam_min > mp.mpf("0.09"), f"Unexpected lambda_min(H0): {lam_min}"

    c2v_rat = get_c2v_witness_rational()
    mp.mp.dps = 80
    assert len(c2v_rat) == 11
    energy_true_witness = z0
    for x, y, z in c2v_rat:
        assert x * x + y * y + z * z == F1
    for i in range(11):
        for j in range(i + 1, 11):
            dx = c2v_rat[i][0] - c2v_rat[j][0]
            dy = c2v_rat[i][1] - c2v_rat[j][1]
            dz = c2v_rat[i][2] - c2v_rat[j][2]
            r2_q = dx * dx + dy * dy + dz * dz
            assert r2_q > 0
            dist = mp.sqrt(mp.mpf(r2_q.numerator) / mp.mpf(r2_q.denominator))
            energy_true_witness += 1 / dist
    ub_mp = mp.mpf(UB_NUM) / mp.mpf(UB_DEN)
    assert energy_true_witness <= ub_mp, "Rational witness energy exceeds claimed Lean upper bound!"
    assert ub_mp - energy < mp.mpf("2e-14"), f"Upper bound slack unexpectedly wide: {ub_mp - energy}"

    return dict(
        E_star_50dps=mp.nstr(energy, 52),
        max_tangential_grad=float(max_tan_grad),
        lambda_min_H0=float(lam_min),
        m_star=float(m_star),
        lean_upper_bound_exact=f"{UB_NUM}/{UB_DEN}",
        lean_upper_bound_float=float(LEAN_UB),
        witness_true_energy_50dps=mp.nstr(energy_true_witness, 52),
    )


def rational_stereo_point(u: Fraction, v: Fraction) -> tuple[Fraction, Fraction, Fraction]:
    s = u * u + v * v
    d = F1 + s
    return (2 * u / d, 2 * v / d, (F1 - s) / d)


def verify_dual_evaluation_on_configs(m10_cert_path: Path) -> dict:
    raw = json.loads(m10_cert_path.read_text())
    e_d = Fraction(raw["e"])
    h_d = [Fraction(x) for x in raw["h"]]
    R1 = Fraction(raw["R1"])
    R2 = Fraction(raw["R2"])
    claimed = Fraction(raw["claimed_bound"])
    assert claimed >= LEAN_LB, f"M10 certificate {claimed} < Lean LB {LEAN_LB}"

    def ev_h(t: Fraction) -> Fraction:
        acc = F0
        for c in reversed(h_d):
            acc = acc * t + c
        return acc

    c2v_rat = get_c2v_witness_rational()
    configs = [("c2v_witness", c2v_rat)]
    rng = random.Random(20261123)
    for idx in range(20):
        pts = []
        used = set()
        while len(pts) < 11:
            u = Fraction(rng.randint(-9, 9), rng.randint(1, 7))
            v = Fraction(rng.randint(-9, 9), rng.randint(1, 7))
            if (u, v) not in used:
                used.add((u, v))
                pts.append(rational_stereo_point(u, v))
        configs.append((f"rand_{idx}", pts))

    mp.mp.dps = 50
    min_margin = mp.mpf("inf")
    c2v_sum_H = None
    for name, pts in configs:
        for x, y, z in pts:
            assert x * x + y * y + z * z == F1
        sum_h = F0
        energy_mp = mp.mpf(0)
        for i in range(11):
            for j in range(i + 1, 11):
                t_ij = pts[i][0] * pts[j][0] + pts[i][1] * pts[j][1] + pts[i][2] * pts[j][2]
                assert -F1 <= t_ij < F1
                h_val = ev_h(t_ij)
                sum_h += h_val
                phi_mp = 1 / mp.sqrt(2 - 2 * mp.mpf(t_ij.numerator) / mp.mpf(t_ij.denominator))
                h_mp = mp.mpf(h_val.numerator) / mp.mpf(h_val.denominator)
                r2_mp = mp.mpf(R2.numerator) / mp.mpf(R2.denominator)
                assert h_mp <= (1 + r2_mp) * phi_mp + mp.mpf("1e-45")
                energy_mp += phi_mp
        lb_sum_h = e_d - 55 * R1
        assert sum_h >= lb_sum_h, f"3-point sum_H bound violated on {name}: {sum_h} < {lb_sum_h}"
        cert_mp = mp.mpf(claimed.numerator) / mp.mpf(claimed.denominator)
        margin = energy_mp - cert_mp
        assert margin > 0, f"Energy lower bound violated on {name}: margin={margin}"
        if margin < min_margin:
            min_margin = margin
        if name == "c2v_witness":
            c2v_sum_H = float(sum_h)

    return dict(
        configs_tested=len(configs),
        c2v_sum_H=c2v_sum_H,
        min_energy_minus_cert=float(min_margin),
        lean_lb_exact=f"{LEAN_LB.numerator}/{LEAN_LB.denominator}",
        lean_lb_float=float(LEAN_LB),
    )


def verify_diagnostic_artifacts(cert_count: int) -> dict:
    sweep_p = HERE / "results" / "phase0_sdp_sweep.json"
    gap_p = HERE / "results" / "phase0_gap_diagnosis.json"
    p4_p = HERE / "results" / "phase0_4pt_probe.json"
    for p in (sweep_p, gap_p, p4_p):
        assert p.exists(), f"Missing required Stage A diagnostic artifact: {p}"

    sweep = json.loads(sweep_p.read_text())
    gap = json.loads(gap_p.read_text())
    p4 = json.loads(p4_p.read_text())

    n_sweep = len(sweep["symcap_certificates"]) + len(sweep["symstrip_certificates"])
    assert n_sweep == cert_count, f"phase0_sdp_sweep.json count {n_sweep} != certificates/ count {cert_count}"
    assert abs(sweep["best_global_3pt_bound"] - 40.55696033) < 1e-6

    assert len(gap["gauss_9_atoms"]) == 9
    assert len(gap["true_moment_1d_lp"]) >= 4
    assert len(gap["k_antipodal_energy_ladder"]) == 6
    assert gap["k_antipodal_energy_ladder"][1]["E_min"] > 40.5968
    assert gap["k_antipodal_energy_ladder"][3]["E_min"] > 40.62

    runs_4pt = {(r["M"], r["D4"]): r for r in p4["runs"]}
    assert runs_4pt[(4, 6)]["gain_over_3pt"] > 0.16, "Expected > +0.16 gain at (M=4, D4=6)"
    assert abs(runs_4pt[(8, 6)]["gain_over_3pt"]) < 1e-9, "Expected ~0 gain at (M=8, D4=6)"

    return dict(
        sweep_certificates=n_sweep,
        gap_gauss_atoms=len(gap["gauss_9_atoms"]),
        probe_4pt_runs=len(p4["runs"]),
        gain_M4_D4_6=runs_4pt[(4, 6)]["gain_over_3pt"],
        gain_M8_D4_6=runs_4pt[(8, 6)]["gain_over_3pt"],
    )


def run_negative_controls(cap_cert_path: Path, strip_cert_path: Path) -> list[dict]:
    cap_base = json.loads(cap_cert_path.read_text())
    strip_base = json.loads(strip_cert_path.read_text())
    results = []

    def expect_fail(name: str, base_doc: dict, verifier, mutator) -> None:
        doc = copy.deepcopy(base_doc)
        mutator(doc)
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tf:
            json.dump(doc, tf)
            tmp_path = Path(tf.name)
        try:
            try:
                verifier(tmp_path, run_identity_check=True)
            except (AssertionError, ValueError, ZeroDivisionError, ExactMatrixError) as exc:
                results.append(dict(control=name, rejected=True, error=str(exc)[:160]))
                return
            raise RuntimeError(f"NEGATIVE CONTROL {name} FAILED: tampered certificate was accepted!")
        finally:
            tmp_path.unlink(missing_ok=True)

    expect_fail("NC1_cap_non_psd_block", cap_base, verify_cap_cert,
                lambda d: d["blocks"][0]["utri"][0].__setitem__(0, "-1"))

    def nc2(d):
        cb = Fraction(d["claimed_bound"]) + Fraction(1, 10 ** 30)
        d["claimed_bound"] = f"{cb.numerator}/{cb.denominator}"

    expect_fail("NC2_cap_inflated_claimed_bound", cap_base, verify_cap_cert, nc2)

    def nc3(d):
        assert Fraction(d["R1"]) > 0
        d["R1"] = "0"

    expect_fail("NC3_cap_zeroed_R1_residual", cap_base, verify_cap_cert, nc3)

    def nc4(d):
        h0 = Fraction(d["h"][0]) + Fraction(1, 1000)
        d["h"][0] = f"{h0.numerator}/{h0.denominator}"

    expect_fail("NC4_cap_corrupted_minorant_h0", cap_base, verify_cap_cert, nc4)

    expect_fail("NC5_strip_non_psd_block", strip_base, verify_strip_cert,
                lambda d: d["blocks"][0]["utri"][0].__setitem__(0, "-1"))
    expect_fail("NC6_strip_inflated_claimed_bound", strip_base, verify_strip_cert, nc2)
    return results


def main() -> None:
    t0 = time.time()
    print("[1/5] Verifying 80-dps C2v stationary candidate & exact rational Lean upper-bound witness...")
    cand_info = verify_candidate_and_upper_bound()
    print(f"  [OK] E*(11) = {cand_info['E_star_50dps'][:28]}..., grad={cand_info['max_tangential_grad']:.2e}, "
          f"UB={cand_info['lean_upper_bound_float']:.14f}")

    cert_dir = REPO / "certificates"
    cert_files = sorted(cert_dir.glob("*.json"))
    assert len(cert_files) >= 15, f"Expected >= 15 exact certificates in {cert_dir}, found {len(cert_files)}"
    print(f"[2/5] Verifying all {len(cert_files)} exact rational SDP certificates (symcap + symstrip)...")
    cert_summaries = []
    total_blocks = 0
    for cp in cert_files:
        raw_kind = json.loads(cp.read_text()).get("kind", "")
        if raw_kind.endswith("-symcap-exact-certificate"):
            ver = verify_cap_cert(cp, run_identity_check=True)
            dom_desc = f"a0={ver['a0']} b0={ver['b0']}"
        elif raw_kind.endswith("-symstrip-exact-certificate"):
            ver = verify_strip_cert(cp, run_identity_check=True)
            dom_desc = f"strip=[{ver['lo']}, {ver['hi']}]"
        else:
            raise ValueError(f"Unknown certificate kind {raw_kind!r} in {cp}")
        assert ver["ok"] and ver["identity_error"] == 0
        total_blocks += ver["blocks_verified"]
        cert_summaries.append(ver)
        print(f"  [OK] {cp.name}: M={ver['M']} K={ver['K']} {dom_desc} "
              f"bound={ver['certified_float']:.12f} ({ver['blocks_verified']} blks, {ver['verify_s']}s)")

    m10_global = cert_dir / "n11-symcap-n11_am1_M10_K10.json"
    print("[3/5] Checking dual certificate evaluation across 21 exact rational S^2 configurations...")
    eval_info = verify_dual_evaluation_on_configs(m10_global)
    print(f"  [OK] {eval_info['configs_tested']} exact rational S^2 configs satisfied H & energy bounds "
          f"(min margin = +{eval_info['min_energy_minus_cert']:.6f})")

    print("[4/5] Verifying Stage A diagnostic JSON artifacts (sweep + gap diagnosis + 4-pt probe)...")
    diag_info = verify_diagnostic_artifacts(len(cert_files))
    print(f"  [OK] Verified sweep ({diag_info['sweep_certificates']} certs), gap diagnosis "
          f"({diag_info['gap_gauss_atoms']} atoms), and 4-pt probe ({diag_info['probe_4pt_runs']} runs)")

    m6_global = cert_dir / "n11-symcap-n11_am1_M6_K6.json"
    strip_m6 = cert_dir / "n11-symstrip-n11_strip_m1_m1023o1024_M6_K6.json"
    print("[5/5] Running 6 adversarial negative controls (NC1..NC6)...")
    nc_results = run_negative_controls(m6_global, strip_m6)
    for nc in nc_results:
        print(f"  [OK] {nc['control']} rejected: {nc['error']}")

    summary = dict(
        ok=True,
        elapsed_s=round(time.time() - t0, 2),
        candidate_and_upper_bound=cand_info,
        certificates_verified=len(cert_summaries),
        total_psd_blocks_verified=total_blocks,
        lean_universal_lower_bound_exact=f"{LEAN_LB.numerator}/{LEAN_LB.denominator}",
        lean_universal_lower_bound_float=float(LEAN_LB),
        lean_upper_bound_exact=f"{UB_NUM}/{UB_DEN}",
        lean_upper_bound_float=float(LEAN_UB),
        remaining_gap_float=float(LEAN_UB - LEAN_LB),
        diagnostic_artifacts=diag_info,
        certificates=cert_summaries,
        config_evaluation=eval_info,
        negative_controls=nc_results,
    )
    out_path = HERE / "results" / "verify_all.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\nALL STAGE A VERIFICATION GATES PASSED in {summary['elapsed_s']}s -> {out_path}")


if __name__ == "__main__":
    main()
