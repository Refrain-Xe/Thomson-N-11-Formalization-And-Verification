# PROGRESS (Chronological Campaign & Verification Log)

This file records each run in chronological order:
- **Founding run, 2026-10-02** (Sections 1–5): repository scaffold, multi-start numerical verification, and reference-energy erratum (`39.783856229` $\to$ `40.596450508`).
- **Hardening run v2 / v2.1, 2026-10-02** (Section 6): negative controls, `check.sh` hardening, and first live Lean 4 build of the frozen challenge file.
- **Phase 0–2 campaign, 2026-11-23** (Section 7): 80-digit $C_{2v}$ stationary-point & Riemannian spectrum analysis, exact rational $S_3$ / $(2,9)$ three-point SDP sweeps, obstruction diagnosis, and Lean 4 formal proofs of `M0`, `M1`, `thomson_eleven_sdp_M10`, `thomson_eleven_upper_bound`, and `thomson_eleven_bounds_sandwich`.
- **Independent audit hardening & 4-point SDP probe, 2026-11-24** (Section 8): Bareiss exact PD acceleration, `(2,9)` strip certificates, `check.sh` string-aware scanner & NC3, and coupled $S_{11} \times O(3)$ four-point SDP hierarchy experiments.
- **International release & paper preparation, 2026-11-24** (Section 9): full English documentation (`README.md`, `REPRODUCE.md`, `info/THEOREM_MAP.md`, `notes/strategy.md`, `PROGRESS.md`) and publication-grade manuscript package (`paper/`).

---

## 1. Founding Run (2026-10-02)

### 1.1 Repository Scaffold
- Created the `thomson-n11` directory layout (`numerics/`, `formal/lean/`, `notes/`).
- Copied `lake-manifest.json`, `lean-toolchain` (`leanprover/lean4:v4.34.1`), and `.gitignore` verbatim from the reference $N = 7$ Lean package (pinning Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; never running `lake update`), and configured `lakefile.toml` for package `ThomsonN11`.
- Fixed `formal/lean/ComparatorChallenges/ThomsonN11.lean` carrying verbatim the shared base definitions (`R3`, `SphereConfig`, `coulombEnergy`, `cyl`, `norm_sq_cyl_sub`, `norm_sq_cyl`) plus the two rational lower-bound milestones `thomson_eleven_M0` ($55/2 = 27.5$) and `thomson_eleven_M1` ($155/4 = 38.75$) with `sorry` placeholders.
- Added verification scripts (`check.sh`, `DumpBody.lean`, `compare_statements.py` with `SKIP = set()`, `CheckAxioms.lean`, `negative-control.sh`, `pin_hashes.sh`).

### 1.2 Numerical Verification and Reference-Energy Erratum
- `numerics/energy.py` (`coulomb_energy(X)`) reproduced benchmark energies: $N=7$ pentagonal bipyramid `14.452977414221344`, $N=8$ square antiprism `19.67528786123276`, $N=12$ icosahedron `49.16525305762881`.
- `numerics/optimize.py` (60 seeded random starts, seed `20261002`, L-BFGS-B + SLSQP polish + 12 polish rounds): all 60/60 starts converged to `E = 40.596450508190578` (`max|tangential gradient| = 2.10e-10`, `max|row norm - 1| = 1.11e-16`), deterministic `reference_config.json` SHA-256 `90ae9afd2acf6893613309e737a266e28031e669dc769baf8125e475a838be53` (gitignored regeneration artifact).

### 1.3 Optimal Configuration Structure (Numerically Verified)
- **$C_{2v}$ symmetry** with orbit decomposition $11 = 1 + 2 + 2 + 2 + 4$ and **20 distinct pairwise inner-product orbits** across the 55 pairs (minimum distance `0.977844807...`).
- **Origin:** edge-contracted icosahedron (unrelaxed energy `40.79434661663611`, relaxing to `40.59645050819061`). The vertex-removed icosahedron ($C_{5v}$, $5+5+1$) is a distinct local minimum at `40.615117337` ($+0.01867$); the $5+6$ two-ring family optimizes at `41.044302330`.

## 2. Initial Acceptance Gates (2026-10-02)
- `python3 numerics/optimize.py` exited `0` (`|gap| = 1.9e-10 < 1e-5`), clean `git status`, `ComparatorChallenges/ThomsonN11.lean` present.

## 3. Erratum: Project Brief Reference Energy `39.783856229` $\to$ `40.596450508`
- Initial brief listed `39.783856229`, which lies below the true minimum. Cross-checking our optimizer on $N = 7, 8, 9, 10, 12$, exhaustive $N = 11$ searches (L-BFGS-B, SLSQP, 100 insertion starts from $N = 9, 10$, 300-step basin-hopping, structural family scans), and external tables (Wales–Ulker Cambridge Cluster Database, Wikipedia Thomson table, UBC lecture notes) confirmed $E_1(11) = 40.596450508\ldots$; `optimize.py`, documentation, and challenge comments were updated accordingly while leaving the Lean milestone statements (`M0 = 55/2`, `M1 = 155/4`) untouched.

## 4–5. Founding Review Fixes (2026-10-02)
- Updated comments in `ComparatorChallenges/ThomsonN11.lean` to reflect the erratum (`40.596450508` and `M1` margin `1.85`), verified verbatim preservation of all 6 base definitions/lemmas and both milestone statements, and independently cross-checked both global (`40.596450508191`) and runner-up (`40.615117336946`) minima.

## 6. Hardening Run v2 & v2.1 (2026-10-02)
- Added `load_reference_energy()` + `--selftest` negative controls (`±0.5` shifted targets rejected, true target accepted) to `numerics/optimize.py`.
- Hardened `formal/lean/scripts/check.sh` with binding verdicts for preamble identity, forbidden tokens, git bytecode hygiene (Step 3b), build exit code and source/log `sorry` counts, and axiom/statement checks.
- Verified live Lean 4 build (`leanprover/lean4:v4.34.1`, Mathlib `d13f23b7`, `lake build ThomsonN11 ComparatorChallenges` exit `0`, 2 expected `sorry` warnings in `ComparatorChallenges/ThomsonN11.lean`) and `negative-control.sh` (`NEGATIVE CONTROL OK`, exit `0`).

---

## 7. Phase 0–2 Campaign (2026-11-23)

### 7.1 Phase 0A: 80-Digit $C_{2v}$ Stationary Point and Riemannian Hessian Spectrum
- Added `numerics/bounds/phase0_candidate.py` $\to$ `numerics/bounds/results/phase0_candidate.json`.
- Rational north-pole stereographic Newton solver converged to $\|\nabla_{S^2} E(X^*_{11})\|_\infty = 8.52 \times 10^{-81}$, $E^*(11) = 40.59645050819060538663553135833447301835336406781920\ldots$, $C_{5v}$ runner-up $40.61511733694649722478\ldots$ ($+0.0186668288$).
- Full $22 \times 22$ Riemannian Hessian: 3 $\mathfrak{so}(3)$ zero modes ($\le 1.73 \times 10^{-80}$), 19 positive modes with $\lambda_{\min}(H_0) = 0.090673217656229\ldots$, $\lambda_{\max}(H_0) = 7.6248624744517\ldots$.
- 55 pairs split into 20 inner-product orbits: $m^* = -0.999022793459447612728\ldots$ (multiplicity 2, disjoint pairs `(3,6)` and `(4,5)`), $g_{\min} = 0.00369731146725\ldots$ (levels 6 and 7).

### 7.2 Phase 0B: Exact Rational $S_3$ / $(2,9)$ Three-Point SDP Sweep & Obstruction Diagnosis
- Built pure-`Fraction` engines `exact_linalg.py`, `sym_cap_sdpa.py`, `sym_strip_sdpa.py`, `phase0_sdp_sweep.py`, `phase0_gap_diagnosis.py`, and `verify_all.py`.
- Global $S_3$ ($a_0 = -1$) certified ladder:
  - $(6,6): 40.533315701817$, $(7,7): 40.545314785703$, $(8,8): 40.551494289332$, $(9,9): 40.554160636831$,
  - **$(10,10): 40.555471704371$** ($\Delta = 0.040979$, formalized in Lean 4 as `thomson_eleven_sdp_M10`),
  - **$(12,12): 40.556960329409$** ($\Delta = 0.039490$, 224-bit `SDPA-GMP` `9541.6s` `pdOPT`, $F_9 \sim 3.44\times 10^{-20}$ and $F_{11} \sim 5.72\times 10^{-23}$ inactive while even icosahedral $F_{10} = 1.05\times 10^{-4}$ activates).
- Cap cuts (`-1023/1024`, `53/100`, `-49/50`, `-9/10`) and `(2,9)` pole-ring strips (`[-1,-1023/1024]` at $(6,6)$, `[-9991/10000,-999/1000]` at $(7,7)$) confirmed persistence of the $\approx 0.0395$ relaxation gap.
- Identified the fractional-icosahedral dual pseudo-measure ($3.3946$ fractional antipodal pairs at $t_1 = -0.999637$, $18.01$ and $21.87$ icosahedral-angle pairs near $\mp 1/\sqrt{5}$) vs. the true $k$-antipodal $\mathbb{R}^3$ energy barrier ($k=1: +4.57\times 10^{-4}$, $k=2: +1.23\times 10^{-3}$, $k=3: +0.02933$, $k=4: +0.18398$, $k=5: +0.30422$).

### 7.3 Phase 1 & Phase 2: Lean 4 Stage B Formalization (Path B)
- Formalized `thomson_eleven_M0` (`55/2`), `thomson_eleven_M1` (`155/4`, proving `583/15` via 6-square Lukács quadratic minorant), `thomson_eleven_sdp_M10` (`2027773585218537/50000000000000 = 40.55547170437074` via zero-Mathlib `Init` data layer + 19 parallel 2D-Kronecker slices), `thomson_eleven_upper_bound` (`2029822525409531/50000000000000 = 40.59645050819062` via pure-$\mathbb{Z}$ projective stereographic witness `c2vWitness`), and `thomson_eleven_bounds_sandwich`.

---

## 8. Independent Audit Hardening & Four-Point SDP Probe (2026-11-24)

### 8.1 Reproducibility Fixes, Strip Certificates, and Gate Hardening
1. Removed scratch-file dependencies from `phase0_gap_diagnosis.py`, reading `(10,10)` and `(12,12)` harmonic blocks directly from committed certificates and solving dual moments inside an isolated `TemporaryDirectory`, plus integrated reproducible 1D true-moment LP ($M=4,6,8,10,12$) and $k$-antipodal ladder ($k=0\dots 5$) computations.
2. Replaced rational $LDL^\top$ GCD bottlenecks in `exact_linalg.py:is_positive_definite` with exact integer Bareiss Sylvester sequential principal minor elimination and pre-contracted 3-point identity tensors, reducing full `verify_all.py` runtime from `1322.8s` to `145.9s` with zero floating-point compromise.
3. Added `write_certificate` and `verify_certificate_file` to `sym_strip_sdpa.py`, committed both `(2,9)` strip certificates (total **15** certificates, **410** PSD blocks), generated `results/phase0_sdp_sweep.json`, and expanded `verify_all.py` to cover all 15 certificates plus **6** tamper negative controls (NC1–NC6).
4. Hardened `check.sh` Step 1 (on-disk + git-tracked package coverage, ignoring `__pycache__`/`*.pyc`/`.DS_Store`) and Step 3 (string-literal-aware comment stripping), added **NC3** to `negative-control.sh`, normalized relative `cert_path` entries across JSON/Python files, and added Apache-2.0 `LICENSE`.

### 8.2 Phase 0C: Coupled $S_{11} \times O(3)$ Four-Point SDP Hierarchy Probe
- Added `numerics/bounds/phase0_4pt_probe.py` $\to$ `numerics/bounds/results/phase0_4pt_probe.json` implementing $\det G_4 = 0$ ideal multipliers, $\mathbb{Z}_2\times\mathbb{Z}_2$ 4-point Putinar and face-Gram SOS, `Harm4_odd`, `Flag2_even`, and global $(\mathbb{R}^3)^{\otimes d}$ pair-tensor blocks `GlobNat`/`GlobAx` (zero exact `Fraction` identity error on random rational sphere configurations):
  - $M = 4$ ($D_3 = D_4 = 6$): `40.32802558` $\to$ **`40.49109850`** (`+0.16307292`);
  - $M = 5$ ($D_3 = D_4 = 8$): `40.50635763` $\to$ `40.50651291` at $D_4=6$ (`+0.00015528`), **`40.51417969`** at $D_4=8$ (`+0.00782206`);
  - $M = 8$ ($D_3 = 14$): coupling $D_4 = 4, 6$ yields zero lift (`< 10^{-11}`), establishing that surpassing the $\approx 40.557$ three-point ceiling requires $D_4 \ge 14\text{--}18$ or multi-pair matching branch-and-bound.

---

## 9. International Release & Paper Package (2026-11-24)

- Converted all repository documentation to international academic English (`README.md`, `notes/strategy.md`, `PROGRESS.md`), added `REPRODUCE.md` and `info/THEOREM_MAP.md`, and verified zero non-English text across the repository.
- Authored the complete LaTeX paper package in `paper/` (`main.tex`, `references.bib`, `figures/make_paper_figures.py` + three vector figures `fig_c2v.pdf`, `fig_sdp_obstruction.pdf`, `fig_4pt_probe.pdf`, `arxiv_metadata.txt`, `build_arxiv_tarball.sh`, compiled `thomson-n11-paper.pdf`, and `arxiv-submission.tar.gz`), subjected both the manuscript and Lean 4 trust boundary to an independent zero-context adversarial audit, resolved every finding, and re-verified all Stage A and Stage B gates.
