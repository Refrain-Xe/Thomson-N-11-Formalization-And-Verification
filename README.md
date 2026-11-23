# The Thomson Problem for $N = 11$: Certified Lean 4 Energy Bounds and the Three-Point SDP Obstruction

Among all configurations of eleven distinct points on the unit sphere $S^2 \subset \mathbb{R}^3$, the conjectured minimizer of the Coulomb energy $E(x) = \sum_{0 \le i < j < 11} \|x_i - x_j\|^{-1}$ is the $C_{2v}$ **edge-contracted icosahedron** $X^*_{11}$ ($1+2+2+2+4$ vertex-orbit decomposition, $E^*(11) \approx 40.59645050819060538664$).

This repository contains the arXiv/Zenodo LaTeX paper, a complete kernel-checked **Lean 4** formalization (Stage B) establishing two-sided certified rational energy bounds
$$40.55547170437074 \;\le\; E_1(11) \;\le\; 40.59645050819062,$$
an exact rational Stage A certificate suite (15 certificates, 410 positive-definite blocks) pushing the three-point semidefinite programming (SDP) relaxation up to degree $22$ ($(M,K)=(12,12): 40.556960329409$), a quantitative diagnosis of the intrinsic three-point SDP relaxation obstruction ($\Delta \approx 0.03949$), and an exact rational $S_{11} \times O(3)$-reduced coupled four-point SDP hierarchy probe.

## Start Here

- **[paper/main.tex](paper/main.tex)**: publication-ready LaTeX manuscript (compiled PDF [paper/thomson-n11-paper.pdf](paper/thomson-n11-paper.pdf), vector figures in `paper/figures/`, arXiv source archive `paper/arxiv-submission.tar.gz`, metadata in [paper/arxiv_metadata.txt](paper/arxiv_metadata.txt)).
- **[info/THEOREM_MAP.md](info/THEOREM_MAP.md)**: exact section-by-section map from every claim in the paper to Lean 4 declarations, namespaces, visibility, and line numbers.
- **[REPRODUCE.md](REPRODUCE.md)**: step-by-step build and verification instructions (Lean 4 Stage B + Python Stage A + paper artifacts).
- **[formal/lean/ThomsonN11/Solution.lean](formal/lean/ThomsonN11/Solution.lean)**: complete formal proofs of both fixed milestone theorems (`thomson_eleven_M0`, `thomson_eleven_M1`) and the strengthened bounds (`thomson_eleven_sdp_M10`, `thomson_eleven_upper_bound`, `thomson_eleven_bounds_sandwich`).
- **[formal/lean/ComparatorChallenges/ThomsonN11.lean](formal/lean/ComparatorChallenges/ThomsonN11.lean)**: unmodified fixed challenge statements (SHA-256 `3cfcae28...a7`).

## Main Theorems Proved in Lean 4

All declarations are mechanically verified by the Lean 4 kernel on pinned **Lean `v4.34.1`** and **Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`** with zero `sorry`s, zero `native_decide`, and dependence solely on Lean's three standard axioms:

| Lean Theorem (`namespace ThomsonN11`) | Formal Statement | Bound & Proof Method | Axioms |
|---|---|---|---|
| `thomson_eleven_M0` | $\forall x \in \mathrm{SphereConfig}\;11,\; 55/2 \le E(x)$ | `27.5` (diameter bound $\|x_i - x_j\| \le 2$) | `[propext, Classical.choice, Quot.sound]` |
| `thomson_eleven_M1` | $\forall x \in \mathrm{SphereConfig}\;11,\; 155/4 \le E(x)$ | `38.75` (quadratic minorant $f_{M_1}(t)=\frac{7}{10}+\frac{2}{5}t+\frac{7}{40}t^2$ + 6-square Lukács identity + $\ell=1,2$ spherical moments, giving $583/15 = 38.866\ldots$) | `[propext, Classical.choice, Quot.sound]` |
| `thomson_eleven_sdp_M10` | $\forall x \in \mathrm{SphereConfig}\;11,\; \frac{2027773585218537}{50000000000000} \le E(x)$ | **`40.55547170437074`** ($(M,K)=(10,10)$ degree-$18$ $S_3$-equivariant 3-point SDP + zero-Mathlib `Init` data layer + 19 parallel 2D-Kronecker slices) | `[propext, Classical.choice, Quot.sound]` |
| `thomson_eleven_upper_bound` | $\exists x \in \mathrm{SphereConfig}\;11,\; E(x) \le \frac{2029822525409531}{50000000000000}$ | **`40.59645050819062`** (pure-$\mathbb{Z}$ projective stereographic $C_{2v}$ witness `StageB.UpperBound.c2vWitness`, within $1.46 \times 10^{-14}$ of $E^*(11)$) | `[propext, Classical.choice, Quot.sound]` |
| `thomson_eleven_bounds_sandwich` | Conjunction of `thomson_eleven_sdp_M10` and `thomson_eleven_upper_bound` | Certifies $E_1(11) \in [40.55547170437074,\; 40.59645050819062]$ (bracket width `0.04097880381988`) | `[propext, Classical.choice, Quot.sound]` |

## Key Scientific Findings: The Three-Point SDP Obstruction and Four-Point Probe

High-precision 80-digit stationary-point analysis (`numerics/bounds/phase0_candidate.py`), exact rational `SDPA-GMP` certificate sweeps (`sym_cap_sdpa.py`, `sym_strip_sdpa.py`, `phase0_sdp_sweep.py`), dual moment diagnostics (`phase0_gap_diagnosis.py`), and coupled four-point SDP experiments (`phase0_4pt_probe.py`) establish the sharp mathematical boundary between $N = 11$ and the resolved cases $N = 7, 8, 9$:

1. **80-Digit $C_{2v}$ Stationary-Point Geometry:** Using rational north-pole stereographic projection on the 5-dimensional $C_{2v}$ manifold ($1+2+2+2+4$ orbits), Newton's method converges to $\|\nabla_{S^2} E(X^*_{11})\|_\infty = 8.52 \times 10^{-81}$ with
   $$E^*(11) = 40.59645050819060538663553135833447301835336406781920\ldots$$
   The full $22 \times 22$ Riemannian Hessian has 3 $\mathfrak{so}(3)$ rotational zero modes ($\le 1.73 \times 10^{-80}$) and 19 strictly positive eigenvalues ($\lambda_{\min}(H_0) = 0.090673217656\ldots > 0$). The 55 pairs split into **20 distinct inner-product orbits** with minimum inner product $m^* = -0.9990227934594476\ldots$ (multiplicity 2, two disjoint nearly antipodal pairs) and minimum adjacent level gap $g_{\min} = 0.0036973115\ldots$. The next lowest local minimum ($C_{5v}$ vertex-removed icosahedron) has energy $40.615117336946\ldots$ ($+0.0186668$).
2. **Exact Rational Three-Point SDP Saturation Ladder:** Across $(M,K) = (6,6)$ through $(12,12)$, exact rational global ($a_0 = -1$) $S_3$ three-point SDP certificates saturate sharply below $E^*(11)$:
   - $(6,6): 40.533315701817$ ($\Delta = 0.063135$)
   - $(7,7): 40.545314785703$ ($\Delta = 0.051136$)
   - $(8,8): 40.551494289332$ ($\Delta = 0.044956$)
   - $(9,9): 40.554160636831$ ($\Delta = 0.042290$)
   - $(10,10): 40.555471704371$ ($\Delta = 0.040979$, formalized in Lean 4 as `thomson_eleven_sdp_M10`)
   - **$(12,12): 40.556960329409$** ($\Delta = 0.039490$, strongest Stage A global certificate `certificates/n11-symcap-n11_am1_M12_K12.json`; odd harmonic blocks $F_9 \sim 3.4\times 10^{-20}$ and $F_{11} \sim 5.7\times 10^{-23}$ are inactive while the even icosahedral harmonic $F_{10} = 1.05\times 10^{-4}$ activates).
   Cap truncations ($a_0 = -1023/1024 < m^*$ giving $40.556970864736$ at $(12,12)$; $b_0 = 53/100$; $a_0 = -49/50$; even $a_0 = -9/10$ giving $40.58493495 < E^*(11)$) and $(2,9)$-typed pole-ring strips (`[-1, -1023/1024]` at $(6,6): 40.53687092$; `[-9991/10000, -999/1000]` at $(7,7): 40.54800350$) all leave a stubborn $\approx 0.0395$ relaxation gap.
3. **Geometric Root Cause (Fractional-Icosahedral Pseudo-Moment Obstruction):**
   - A discrete-grid 1D polynomial minorant LP evaluated on the true moments of $X^*_{11}$ already reaches $40.59645006$ at $M = 8$ ($\deg H = 14$, gap $4.52 \times 10^{-7}$), ruling out polynomial degree as the bottleneck.
   - The optimal $(10,10)$ dual 9-atom Gauss–Christoffel pseudo-measure places **$3.3946$ fractional antipodal pairs** at $t_1 = -0.999637$ alongside $18.01$ and $21.87$ icosahedral-angle pairs near $\mp 1/\sqrt{5}$.
   - On the true sphere $(S^2)^{11}$, forcing $k$ exact antipodal pairs yields minimal energies $k=0: 40.596451$, $k=1: 40.596907$ ($+4.57\times 10^{-4}$), $k=2: 40.597677$ ($+1.23\times 10^{-3}$), $k=3: 40.625784$ ($+0.02933$), $k=4: 40.780435$ ($+0.18398$), $k=5: 40.900671$ ($+0.30422$). The small $k=1,2$ penalties prevent single-pair strip exclusion near $t = -1$, while the absence of the four-point rank-3 constraint $\det G_4 = 0$ allows the three-point SDP to smear the missing-vertex icosahedral defect over $\approx 3.4$ fractional antipodal pairs without paying the 3D frustration cost.
4. **Coupled $S_{11} \times O(3)$ Four-Point SDP Hierarchy Probe:** Combining $\det G_4 = 0$ ideal multipliers, $\mathbb{Z}_2\times\mathbb{Z}_2$ four-point Putinar and face-Gram SOS, Binet–Cauchy cross-product blocks (`Harm4_odd`), pair-flag blocks (`Flag2_even`), and global $(\mathbb{R}^3)^{\otimes d}$ pair-tensor blocks (`GlobNat`/`GlobAx`) strictly improves matched-degree three-point bounds:
   - $M = 4$ ($D_3 = D_4 = 6$): $40.32802558 \to 40.49109850$ (**$+0.16307292$**),
   - $M = 5$ ($D_3 = D_4 = 8$): $40.50635763 \to 40.51417969$ (**$+0.00782206$**).
   Coupling low-degree $D_4 \in \{4, 6\}$ onto high-degree three-point $M = 8$ ($D_3 = 14$, $40.55149429$) gives zero lift ($< 10^{-11}$), demonstrating that surpassing the $\approx 40.557$ ceiling requires $D_4 \ge 14\text{--}18$ (full $S_4$-isotypic four-point reduction) or multi-pair matching branch-and-bound.

## Verification Summary

- **`bash formal/lean/scripts/check.sh`** — exits `0`:
  - `SHA256SUMS.txt` pins all **40** package files in `formal/lean/` (checked against both on-disk files and `git ls-files`);
  - Byte-for-byte match of the 32-line shared base definitions block between `ComparatorChallenges/ThomsonN11.lean` and `ThomsonN11/Solution.lean`;
  - String-aware, comment-stripping soundness token scan passes across all **29** solution modules (`7,925` lines; `StageB/` is 27 files, `7,509` lines, `11.42 MiB`, `353` `decide +kernel` sites) and `lakefile.toml` (`0` forbidden tokens in `Solution.lean`; only `maxHeartbeats` and `maxRecDepth` outside `Solution.lean`; zero `sorry`, `native_decide`, `ofReduceBool`, `skipKernelTC`, `axiom`, `opaque`, `unsafe`, `partial`, or macros);
  - `lake build ThomsonN11 ComparatorChallenges` passes (`8,955` jobs; exactly `2` expected `sorry`s in `ComparatorChallenges/ThomsonN11.lean`, `0` in `Solution.lean`);
  - `#print axioms` strict whitelist confirms `[propext, Classical.choice, Quot.sound]` across all 5 exported theorems;
  - `scripts/compare_statements.py` (`SKIP = set()`) confirms **10/10** challenge constants match verbatim (`STATEMENT COMPARISON: OK`, digest `402f5633...4d2`).
- **`bash formal/lean/scripts/negative-control.sh`** — exits `0`: passes NC1 (statement inequality flip detection), NC2 (Lean kernel rejection of inflated SDP bound), and NC3 (rejection of string-smuggled `skipKernelTC` by the `check.sh` scanner).
- **Stage A exact rational verification (`python3 numerics/bounds/verify_all.py`)** — exits `0`: independently verifies the 80-dps $C_{2v}$ stationary point, all **15** exact rational certificates (**410** PSD blocks via exact integer Bareiss Sylvester principal minors, zero polynomial identity error), diagnostic ledger consistency, 21 rational spherical test configurations, and **6** tamper negative controls (NC1–NC6).

## Repository Layout

```text
thomson-n11/
├── README.md                    This overview
├── REPRODUCE.md                 Step-by-step reproduction guide (Stage B + Stage A + paper)
├── PROGRESS.md                  Chronological research and verification log
├── LICENSE                      Apache-2.0 license (Copyright 2026 Yang Li)
├── info/THEOREM_MAP.md          Paper-to-Lean theorem & line-number index
├── paper/                       LaTeX manuscript (main.tex), BibTeX, figures, compiled PDF, arXiv tarball
├── notes/strategy.md            Obstruction diagnosis, Lean 4 architecture, and closure roadmap
├── certificates/                15 exact rational SDP certificates (13 symcap + 2 symstrip)
├── numerics/
│   ├── energy.py / optimize.py  Multi-start spherical optimizer and reference-energy self-test
│   └── bounds/                  Exact integer linear algebra, S3 / (2,9) SDP engines, Phase 0 diagnostics,
│                                4-point SDP probe, Lean exporters, verify_all.py, and JSON ledgers
└── formal/lean/                 Self-contained Lake package (Lean v4.34.1, Mathlib d13f23b7; 29 solution modules)
    ├── SHA256SUMS.txt           40-file package SHA-256 manifest
    ├── ComparatorChallenges/    Unmodified frozen challenge file (M0 = 55/2, M1 = 155/4)
    ├── ThomsonN11/Solution.lean Formal proofs of M0, M1, sdp_M10, upper_bound, bounds_sandwich (404 lines)
    ├── ThomsonN11/StageB/       Zero-Mathlib Init data layer, 19 Kronecker slices, SdpCert, UpperBound (27 files)
    └── scripts/                 check.sh, negative-control.sh, CheckAxioms.lean, compare_statements.py, pin_hashes.sh
```

## Quick Verification Commands

```sh
# Stage B: Lean 4 kernel verification gate + negative controls (NC1–NC3)
export PATH="$HOME/.elan/bin:$PATH"
bash formal/lean/scripts/check.sh
bash formal/lean/scripts/negative-control.sh

# Stage A: optimizer, exact SDP engines, and 15-certificate verifier + negative controls (NC1–NC6)
python3 numerics/optimize.py
python3 numerics/optimize.py --selftest
python3 numerics/bounds/sym_cap_sdpa.py --selftest
python3 numerics/bounds/sym_strip_sdpa.py --selftest
python3 numerics/bounds/verify_all.py
```

## References

- J. J. Thomson (1904), *On the structure of the atom*, Phil. Mag. (6) 7, 237–265.
- C. Bachoc, F. Vallentin (2008), *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc. 21, 909–924.
- H. Cohn, J. Woo (2012), *Three-point bounds for energy minimization*, J. Amer. Math. Soc. 25, 929–958.
- D. J. Wales, S. Ulker (2006), *Structure and dynamics of spherical crystals characterized for the Thomson problem*, Phys. Rev. B 74, 212101.
- L. Kryvonos, L. Liehr, M. A. Taylor (2026), *Energy minimization for eight points on the sphere*, arXiv:2609.22077.
- Vals AI (2026), *The pentagonal bipyramid is the unique minimiser of the Coulomb energy of seven points on the sphere*, https://github.com/huwngtran/thomson-n7-lean.
- Y. Li (2026), *The Tricapped Trigonal Prism Is the Unique Minimizer of the Coulomb Energy of Nine Points on the Sphere*, Zenodo preprint, DOI [10.5281/zenodo.24453172](https://doi.org/10.5281/zenodo.24453172), https://github.com/Refrain-Xe/Thomson-N-9-Formalization-And-Verification.

## License

Licensed under the [Apache License, Version 2.0](LICENSE) (Copyright 2026 Yang Li).
