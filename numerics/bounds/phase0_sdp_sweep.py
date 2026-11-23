#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""phase0_sdp_sweep.py — Exact-certified S3 3-point cap & (2, 9) typed strip SDP sweep
summary and live runner for Thomson N = 11.

Default mode (`python3 numerics/bounds/phase0_sdp_sweep.py`) inspects and exact-verifies
every committed certificate in `certificates/*.json` (13 S3 cap/interval certificates across
(M, K) = (6,6)..(12,12) plus 2 (2, 9) typed polar strip certificates) and writes
`numerics/bounds/results/phase0_sdp_sweep.json`.

Pass `--run-live` to re-solve a fresh sweep via SDPA-GMP in an isolated TemporaryDirectory.
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

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))

from exact_linalg import frac_str  # noqa: E402
from sym_cap_sdpa import SymCapModel, verify_certificate_file as verify_cap_cert  # noqa: E402
from sym_strip_sdpa import verify_certificate_file as verify_strip_cert  # noqa: E402

E_STAR_FLOAT = 40.596450508190605


def make_param_sdpa(eps: str = "1.0E-14", precision: int = 96, max_iter: int = 200) -> str:
    return f"""{max_iter}\tunsigned int maxIteration;
{eps}\tdouble 0.0 < epsilonStar;
1.0E4\tdouble 0.0 < lambdaStar;
2.0\tdouble 1.0 < omegaStar;
-1.0E5\tdouble lowerBound;
1.0E5\tdouble upperBound;
0.1\tdouble 0.0 <= betaStar <  1.0;
0.3\tdouble 0.0 <= betaBar  <  1.0, betaStar <= betaBar;
0.9\tdouble 0.0 < gammaStar <  1.0;
{eps}\tdouble 0.0 < epsilonDash;
{precision}\tprecision
"""


def run_live_case(n: int, a0_str: str, M: int, K: int, eps: str, precision: int, k_bits: int,
                  sdpa_bin: str) -> dict:
    a0 = Fraction(a0_str)
    tag = f"diag_n{n}_a{str(a0).replace('/','o').replace('-','m')}_M{M}_K{K}_p{precision}"
    model = SymCapModel(n, a0, M, K)
    with tempfile.TemporaryDirectory() as td:
        wdir = Path(td)
        dat_path = wdir / f"{tag}.dat-s"
        res_path = wdir / f"{tag}.result"
        param_path = wdir / "param.sdpa"
        param_path.write_text(make_param_sdpa(eps=eps, precision=precision))
        info = model.write_dat(dat_path)
        t0 = time.time()
        proc = subprocess.run([sdpa_bin, "-ds", str(dat_path), "-o", str(res_path), "-p", str(param_path)],
                              capture_output=True, text=True)
        solve_s = time.time() - t0
        if proc.returncode != 0:
            raise RuntimeError(f"SDPA-GMP failed ({proc.returncode}): {proc.stderr[-800:]}")
        cert = model.certify_from_result(res_path, k_bits=k_bits)
        cert_path = wdir / f"n{n}-symcap-{tag}.json"
        model.write_certificate(cert, cert_path, solve_s)
        ver = verify_cap_cert(cert_path, run_identity_check=False)

    e_raw = float(cert["e_raw"])
    e_cert = float(cert["certified"])
    f_traces = {f"F_{k}": cert["block_traces"].get(f"F_{k}", 0.0) for k in range(K)}
    print(f"[{tag}] DONE in {solve_s:.1f}s: e_raw={e_raw:.14f}  e_cert={e_cert:.14f}  gap={E_STAR_FLOAT - e_cert:.6e}",
          flush=True)
    return {
        "family": "symcap-live",
        "tag": tag,
        "a0": frac_str(a0),
        "b0": "1",
        "M": M,
        "K": K,
        "m_rows": info["m"],
        "solve_s": round(solve_s, 2),
        "e_raw": e_raw,
        "e_certified": e_cert,
        "e_certified_exact": frac_str(cert["certified"]),
        "gap_to_E_star_certified": E_STAR_FLOAT - e_cert,
        "R1": float(cert["R1"]),
        "R2": float(cert["R2"]),
        "F_traces": f_traces,
        "cert_sha256": ver["sha256"],
    }


def summarize_committed_certificates() -> dict:
    cert_dir = REPO / "certificates"
    cert_files = sorted(cert_dir.glob("*.json"))
    cap_rows = []
    strip_rows = []
    for cp in cert_files:
        raw = json.loads(cp.read_text())
        kind = raw.get("kind", "")
        if kind.endswith("-symcap-exact-certificate"):
            ver = verify_cap_cert(cp, run_identity_check=False)
            prov = raw.get("provenance", {})
            e_cert = ver["certified_float"]
            cap_rows.append({
                "certificate": cp.name,
                "a0": ver["a0"],
                "b0": ver["b0"],
                "M": ver["M"],
                "K": ver["K"],
                "round_bits": raw["round_bits"],
                "blocks_verified": ver["blocks_verified"],
                "solve_s": prov.get("solve_s"),
                "e_raw": float(Fraction(prov["e_raw_exact"])) if "e_raw_exact" in prov else e_cert,
                "e_certified": e_cert,
                "e_certified_exact": ver["certified_exact"],
                "gap_to_E_star_certified": E_STAR_FLOAT - e_cert,
                "R1": ver["R1"],
                "R2": ver["R2"],
                "F_traces": {k: v for k, v in raw.get("block_traces", {}).items() if k.startswith("F_")},
                "sha256": ver["sha256"],
            })
        elif kind.endswith("-symstrip-exact-certificate"):
            ver = verify_strip_cert(cp, run_identity_check=False)
            prov = raw.get("provenance", {})
            e_cert = ver["certified_float"]
            strip_rows.append({
                "certificate": cp.name,
                "lo": ver["lo"],
                "hi": ver["hi"],
                "a_other": ver["a_other"],
                "M": ver["M"],
                "K": ver["K"],
                "round_bits": raw["round_bits"],
                "blocks_verified": ver["blocks_verified"],
                "solve_s": prov.get("solve_s"),
                "e_raw": float(Fraction(prov["e_raw_exact"])) if "e_raw_exact" in prov else e_cert,
                "e_certified": e_cert,
                "e_certified_exact": ver["certified_exact"],
                "gap_to_E_star_certified": E_STAR_FLOAT - e_cert,
                "R2max": ver["R2max"],
                "sha256": ver["sha256"],
            })
        else:
            raise ValueError(f"Unknown certificate kind {kind!r} in {cp}")

    cap_rows.sort(key=lambda r: (r["a0"], r["b0"], r["M"], r["K"], r["certificate"]))
    strip_rows.sort(key=lambda r: (r["M"], r["K"], r["certificate"]))
    best_global = max(
        (r for r in cap_rows if r["a0"] == "-1" and r["b0"] == "1"),
        key=lambda r: r["e_certified"],
    )
    return {
        "n": 11,
        "E_star": E_STAR_FLOAT,
        "best_global_3pt_bound": best_global["e_certified"],
        "best_global_3pt_bound_exact": best_global["e_certified_exact"],
        "best_global_3pt_gap": best_global["gap_to_E_star_certified"],
        "best_global_certificate": best_global["certificate"],
        "symcap_certificates": cap_rows,
        "symstrip_certificates": strip_rows,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-live", action="store_true")
    ap.add_argument("--a0", type=str, default="-1")
    ap.add_argument("--orders", type=str, default="6,8,10,12")
    ap.add_argument("--eps", type=str, default="1.0E-14")
    ap.add_argument("--precision", type=int, default=96)
    ap.add_argument("--k-bits", type=int, default=48)
    ap.add_argument("--sdpa-bin", type=str, default="/tmp/hpbuild/sdpa-gmp-7.1.3/sdpa_gmp")
    ap.add_argument("--out", type=str, default=str(HERE / "results" / "phase0_sdp_sweep.json"))
    args = ap.parse_args()

    out_p = Path(args.out)
    out_p.parent.mkdir(parents=True, exist_ok=True)

    if args.run_live:
        orders = [int(x) for x in args.orders.split(",") if x.strip()]
        rows = [
            run_live_case(11, args.a0, M, M, args.eps, args.precision, args.k_bits, args.sdpa_bin)
            for M in orders
        ]
        out_p.write_text(json.dumps({"n": 11, "E_star": E_STAR_FLOAT, "live_runs": rows}, indent=2) + "\n")
        print(f"Wrote live sweep -> {out_p}")
        return

    summary = summarize_committed_certificates()
    out_p.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Verified & summarized {len(summary['symcap_certificates'])} symcap + "
          f"{len(summary['symstrip_certificates'])} symstrip exact certificates -> {out_p}")
    print(f"  Best global 3-pt bound: {summary['best_global_3pt_bound']:.12f} "
          f"(gap = {summary['best_global_3pt_gap']:.8f}, cert = {summary['best_global_certificate']})")


if __name__ == "__main__":
    main()
