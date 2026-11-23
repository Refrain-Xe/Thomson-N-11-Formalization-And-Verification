# Reproducing the Thomson N = 11 Formal Proofs, Exact SDP Certificates, and Paper Artifacts

This guide documents how to independently reproduce (1) the kernel-checked **Lean 4** formal proofs (Stage B), (2) the exact rational Python SDP certificate and diagnostic suite (Stage A), and (3) the LaTeX paper figures and arXiv upload archive.

## Requirements

- **Lean 4 formal proof (Stage B):** `elan`, `git`, `python3`, ~4 GB RAM for incremental checks (or ~8 GB RAM for a full cold rebuild; each zero-Mathlib `SdpCertSosSlice*.lean` process uses `< 300 MB` RAM), and ~10 GB disk for the prebuilt Mathlib cache.
  - Pinned Lean toolchain: `leanprover/lean4:v4.34.1` (`formal/lean/lean-toolchain`)
  - Pinned Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612` (`formal/lean/lake-manifest.json`)
  - **Never run `lake update`**, as that modifies dependency pins.
- **Stage A exact rational verifier & paper figures:** Python 3.10+ with `mpmath`, `numpy`, `scipy`, `matplotlib`.
- **Optional (only if re-solving SDPs from scratch rather than verifying the committed certificates):** `sdpa_gmp` (200/224-bit arbitrary-precision semidefinite solver).

## 1. One-Command Lean 4 Verification (Stage B Official Gate)

From the repository root (`thomson-n11/`):

```sh
export PATH="$HOME/.elan/bin:$PATH"
bash formal/lean/scripts/check.sh
```

This script executes every gate in sequence and exits non-zero on any failure:
1. **File-identity pin (`SHA256SUMS.txt`):** verifies the SHA-256 digest of all **40** package files in `formal/lean/` (enforcing in particular that `ComparatorChallenges/ThomsonN11.lean` has digest `3cfcae28bc938bc374d35088f86134a35ff476f805b5645e288e67ca9c415fa7`) and rejects any unpinned on-disk or git-tracked package file.
2. **Base definitions check:** verifies byte-for-byte identity of the 32-line shared base definitions block (`open Real` through `norm_sq_cyl`) between `ComparatorChallenges/ThomsonN11.lean` and `ThomsonN11/Solution.lean`.
3. **Full-cone soundness token scan:** enforces zero forbidden tokens in `ThomsonN11/Solution.lean` and runs a string- and comment-aware scan over all supporting modules in `ThomsonN11/` (`29` solution modules, `7,925` lines) and `lakefile.toml`, allowing only `set_option maxHeartbeats`, `set_option maxRecDepth`, and `linter.*` switches outside `Solution.lean`.
4. **Repository hygiene (Step 3b):** rejects any tracked `__pycache__`, `*.pyc`, `.DS_Store`, `.lake/`, or `logs/` artifacts.
5. **Toolchain, cache, and build (Steps 4–5):** fetches the prebuilt Mathlib cache (`lake exe cache get`) and runs `lake build ThomsonN11 ComparatorChallenges` (`8,955` jobs), enforcing exactly **2** `sorry`s in `ComparatorChallenges/ThomsonN11.lean` and **0** in `ThomsonN11/Solution.lean`.
6. **Strict axiom whitelist (Step 6):** runs `lake env lean scripts/CheckAxioms.lean` and verifies that all five exported theorems (`thomson_eleven_M0`, `thomson_eleven_M1`, `thomson_eleven_sdp_M10`, `thomson_eleven_upper_bound`, `thomson_eleven_bounds_sandwich`) depend solely on subsets of:
   ```text
   [propext, Classical.choice, Quot.sound]
   ```
7. **Statement fidelity (Step 7):** dumps all declarations of `ComparatorChallenges.ThomsonN11` and `ThomsonN11.Solution` under `pp.all` + `pp.universes` and runs `scripts/compare_statements.py` (`SKIP = set()`, zero exemptions), confirming an exact **10/10** match (`STATEMENT COMPARISON: OK`, digest `402f5633c493f1603faa936d22ae5faff83ac5504d7cc1eb27243d565ffc04d2`).

*Verification boundary:* All checks above run on the reference Lean `v4.34.1` kernel (`compare_statements.py` enforces declaration-level statement fidelity directly; independent replay in a second kernel such as `lean4export + nanoda` is optional future hardening).

### Cold rebuild from zero `.olean` cache

To rebuild all 29 solution modules and all 19 parallel 2D-Kronecker slices from scratch (keeping the Mathlib cache intact):

```sh
rm -rf formal/lean/.lake/build/lib/lean/ThomsonN11* \
       formal/lean/.lake/build/ir/ThomsonN11* \
       formal/lean/.lake/build/lib/lean/ComparatorChallenges* \
       formal/lean/.lake/build/ir/ComparatorChallenges*
export PATH="$HOME/.elan/bin:$PATH"
bash formal/lean/scripts/check.sh
```

Because `PolyKronDefs.lean`, `SdpCertHarmData.lean`, `SdpCertSosData.lean`, and all 19 `SdpCertSosSlice*.lean` modules do not import Mathlib, each slice process uses `< 300 MB` RAM and all 19 slices compile cleanly in parallel.

### Negative controls (NC1–NC3)

Run after `check.sh`:

```sh
export PATH="$HOME/.elan/bin:$PATH"
bash formal/lean/scripts/negative-control.sh
```

This runs three automated negative controls:
- **NC1 (statement fidelity):** flips the inequality in `thomson_eleven_M1` on a scratch copy of `ComparatorChallenges/ThomsonN11.lean` and confirms `compare_statements.py` rejects it, naming solely `ThomsonN11.thomson_eleven_M1`.
- **NC2 (kernel certificate soundness):** attempts to certify an inflated SDP bound (`bound_num + 100000000000`) via `decide +kernel` and confirms the Lean 4 kernel rejects it.
- **NC3 (scanner robustness):** wraps a forbidden `set_option debug.skipKernelTC true` between string literals `"/-"` and `"-/"` and confirms the `check.sh` Step 3 scanner rejects it.

## 2. Stage A Exact Rational Verification & Diagnostics

```sh
python3 numerics/optimize.py
python3 numerics/optimize.py --selftest
python3 numerics/bounds/sym_cap_sdpa.py --selftest
python3 numerics/bounds/sym_strip_sdpa.py --selftest
python3 numerics/bounds/verify_all.py
```

`verify_all.py` (~2.5 minutes) independently verifies:
- the 80-digit $C_{2v}$ stationary point and pure-integer upper-bound witness (`40.59645050819062`),
- all **15** committed exact rational SDP certificates in `certificates/` (13 `symcap` + 2 `(2,9)` `symstrip` certificates, **410** positive-definite blocks checked via exact integer Bareiss Sylvester sequential principal minors, exact 1D Lukács residuals, and zero-error 3-point / `(2,9)` combinatorial identities),
- consistency of the committed diagnostic JSON ledgers (`phase0_sdp_sweep.json`, `phase0_gap_diagnosis.json`, `phase0_4pt_probe.json`),
- dual evaluation on 21 rational spherical 11-point configurations, and
- **6** tamper negative controls (NC1–NC6: non-PSD cap block, inflated cap bound, zeroed $R_1$ residual, corrupted minorant $h_0$, non-PSD strip block, and inflated strip bound).

Optional regeneration of diagnostic ledgers (requires `sdpa_gmp` on `PATH`):
```sh
python3 numerics/bounds/phase0_candidate.py
python3 numerics/bounds/phase0_sdp_sweep.py
python3 numerics/bounds/phase0_gap_diagnosis.py
python3 numerics/bounds/phase0_4pt_probe.py
```

## 3. Regenerating Paper Figures and the arXiv Upload Archive

```sh
python3 paper/figures/make_paper_figures.py
bash paper/build_arxiv_tarball.sh
```

This regenerates `paper/figures/fig_{c2v,sdp_obstruction,4pt_probe}.{pdf,png}` directly from `numerics/bounds/results/*.json` and packages `paper/arxiv-submission.tar.gz` (`main.tex` plus the three vector PDF figures).
