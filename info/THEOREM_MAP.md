# Theorem Map: Paper Claims to Lean 4 Declarations

Every declaration below is checked by the Lean 4 kernel (`leanprover/lean4:v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`) with zero `sorry`s, zero `native_decide`, and dependence solely on Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.

## 1. Fixed Challenge Statements and Main Certified Theorems (`formal/lean/ThomsonN11/Solution.lean`)

All **10** declarations of `ComparatorChallenges/ThomsonN11.lean` (SHA-256 `3cfcae28bc938bc374d35088f86134a35ff476f805b5645e288e67ca9c415fa7`) are matched verbatim under `pp.all` + `pp.universes` by `scripts/compare_statements.py` (`SKIP = set()`, compared-text digest `402f5633c493f1603faa936d22ae5faff83ac5504d7cc1eb27243d565ffc04d2`). `Solution.lean` additionally exports the strengthened degree-$18$ three-point SDP lower bound, the explicit rational $C_{2v}$ upper bound, and their combined two-sided sandwich theorem matching Theorem 1.1 verbatim.

| Mathematical Object / Claim | Lean Declaration | File & Line (`formal/lean/ThomsonN11/`) |
|---|---|---|
| Euclidean space $\mathbb{R}^3$ | `ThomsonN11.R3` | `Solution.lean:30` |
| Admissible $n$-point unit-sphere configurations | `ThomsonN11.SphereConfig` | `Solution.lean:34` |
| Coulomb energy $\sum_{0 \le i < j < n}\|x_i - x_j\|^{-1}$ | `ThomsonN11.coulombEnergy` | `Solution.lean:38` |
| Cylindrical coordinates $(\rho,\theta,h)$ | `ThomsonN11.cyl` | `Solution.lean:42` |
| Cylindrical chord-length & norm identities | `ThomsonN11.norm_sq_cyl_sub`, `ThomsonN11.norm_sq_cyl` | `Solution.lean:46`, `Solution.lean:52` |
| **Challenge Milestone M0** ($E(x) \ge 55/2 = 27.5$) | `ThomsonN11.thomson_eleven_M0` | `Solution.lean:61` |
| **Challenge Milestone M1** ($E(x) \ge 155/4 = 38.75$) | `ThomsonN11.thomson_eleven_M1` | `Solution.lean:279` |
| **Theorem 1.1(a): Strengthened $(10,10)$ 3-Point SDP Lower Bound** ($E(x) \ge 40.55547170437074$) | `ThomsonN11.thomson_eleven_sdp_M10` | `Solution.lean:373` |
| **Theorem 1.1(b): Certified Rational $C_{2v}$ Upper Bound** ($\exists x,\; E(x) \le 40.59645050819062$) | `ThomsonN11.thomson_eleven_upper_bound` | `Solution.lean:388` |
| **Theorem 1.1(c): Combined Two-Sided Energy Sandwich** | `ThomsonN11.thomson_eleven_bounds_sandwich` | `Solution.lean:399` |

## 2. Proof Spine (`formal/lean/ThomsonN11/`)

| Paper Section | Mathematical Step | Lean Declaration | File & Line (`formal/lean/ThomsonN11/`) |
|---|---|---|---|
| §3 | Quadratic minorant $f_{M_1}(t) = \frac{7}{10}+\frac{2}{5}t+\frac{7}{40}t^2$ | `ThomsonN11.fM1` *(private)* | `Solution.lean:196` |
| §3 | 6-square Lukács identity $1 - 2(1-t)f_{M_1}(t)^2 \ge 0$ | `ThomsonN11.fM1_minorant_nonneg` *(private)* | `Solution.lean:198` |
| §3 | First & second spherical harmonic moment bounds | `ThomsonN11.double_sum_dot_nonneg`, `ThomsonN11.double_sum_dot_sq_ge` *(private)* | `Solution.lean:214`, `Solution.lean:226` |
| §4.1 | Three-point Gram positivity $\det G \ge 0$ | `StageB.detG_nonneg_of_unit` | `StageB/ThreePoint.lean:86` |
| §6.3 / §7.1 | Four-point Euclidean realizability identity $\det G_4 = 0$ in $\mathbb{R}^3$ | `StageB.det4_eq_zero_of_unit` | `StageB/ThreePoint.lean:105` |
| §4.1 | Chebyshev–Gegenbauer three-point kernels $Q_k(u,v,t)$ & complex de Moivre formula | `StageB.Q3`, `StageB.Q3_eq_re` | `StageB/ThreePoint.lean:141`, `StageB/ThreePoint.lean:147` |
| §4.1 | Generic rank-1 Bachoc–Vallentin positivity | `StageB.sum_Y3_sq_nonneg_finset`, `StageB.sum_cholesky_Y3_nonneg_finset` | `StageB/ThreePoint.lean:268`, `StageB/ThreePoint.lean:284` |
| §4.1 | Exact 11-point $S_3$-symmetric 3-point assembly identity | `StageB.cap_assembly_11` | `StageB/ThreePoint.lean:336` |
| §6.1 | Exact 11-point $(2,9)$-typed pole-ring assembly identity | `StageB.slab_assembly_11` | `StageB/ThreePoint.lean:770` |
| §8.1 | Pure-`Init` polynomial evaluators, bit-trie `Trie`, and fast 2D-Kronecker structures | `StageB.PolyKronFast.{Trie, kev2T, cholPlainKev2T, cholStdKev2T, harmListKev2T}` | `StageB/PolyKronDefs.lean:168–235` |
| §4.2 / §8.1 | Trivariate polynomial representation & 3D Kronecker zero theorem | `StageB.PolyKron.HasPolyRep3`, `StageB.PolyKron.eq_zero_of_kev3_zero` | `StageB/PolyKron.lean:258`, `StageB/PolyKron.lean:355` |
| §4.1 | Multi-block integer Cholesky harmonic positivity | `StageB.PolyKron.sum_harmListEv_nonneg` | `StageB/PolyKron.lean:1290` |
| §8.1 | Binary bit-trie correctness & 2D-Kronecker multi-slice zero theorem | `StageB.PolyKronFast.Trie.get_ofList`, `StageB.PolyKronFast.eq_zero_of_kev2_slices` | `StageB/PolyKronFast.lean:59`, `StageB/PolyKronFast.lean:468` |
| §4.2 | Harmonic degree check & 1D minorant identity ($y = \sqrt{(1-t)/2}$) | `StageB.SdpCertHarmData.{harm_deg_ok, minor_ok}` | `StageB/SdpCertHarmData.lean:195`, `StageB/SdpCertHarmData.lean:197` |
| §4.2 | SOS block degrees, $\ell^1$ cap, and cross-multiplied integer bound check | `StageB.SdpCertSosData.{l1_fast_ok, basis_l1_ok, res_deg_ok, basis_len_ok, sos_exact_deg_ok, bound_ok}` | `StageB/SdpCertSosData.lean:1402–1427` |
| §4.2 / §8.1 | 19 parallel 2D-Kronecker slice certificates ($T \in \{-9,\dots,9\}$) | `StageB.SdpCertSosSlice{M9..9}.kron_t_{m9..9}` | `StageB/SdpCertSosSlice*.lean` |
| §4.2 | Trivariate slack identity via 19 Kronecker slices | `StageB.SdpCert.id_slack` *(private)* | `StageB/SdpCert.lean:191` |
| §4.2 | SOS slack nonnegativity & 1D minorant upper bound | `StageB.SdpCert.sosCap_ev_nonneg`, `StageB.SdpCert.minorCap_bound` *(private)* | `StageB/SdpCert.lean:361`, `StageB/SdpCert.lean:397` |
| **§4.2** | **Universal $(10,10)$ 3-point SDP lower bound** | `StageB.SdpCert.global_sdp_lower_bound` | `StageB/SdpCert.lean:435` |
| §5 | Pure-$\mathbb{Z}$ projective $C_{2v}$ witness & kernel checks | `StageB.UpperBound.{c2vPtsZ, uUpperZ, unit_ok, pair_u_ok, energy_sum_ok}` | `StageB/UpperBound.lean:22–77` |
| §5 | Witness admissibility (unit norm & injectivity) | `StageB.UpperBound.{c2vWitness, c2vWitness_unit, c2vWitness_injective}` | `StageB/UpperBound.lean:79`, `:88`, `:150` |
| **§5** | **Certified rational $C_{2v}$ upper bound** | `StageB.UpperBound.c2vWitness_energy_le` | `StageB/UpperBound.lean:162` |

## 3. Kernel Decision Sites (`decide +kernel`)

Total comment-stripped `decide +kernel` invocations across all **29** solution modules (`ThomsonN11.lean` + `ThomsonN11/Solution.lean` + 27 `StageB/*.lean`, `7,925` lines): **353**
- `StageB/SdpCertHarmData.lean`: **2** (`harm_deg_ok`, `minor_ok`)
- `StageB/SdpCertSosData.lean`: **6** (`l1_fast_ok`, `basis_l1_ok`, `res_deg_ok`, `basis_len_ok`, `sos_exact_deg_ok`, `bound_ok`)
- `StageB/SdpCertSosSlice{M9..9}.lean` (19 files): **342** ($19 \times 18$: per slice, 17 sub-block integer evaluations `p_lhs`, `p_plain`, `p_s1`, `p_s2`, `p_le1..3`, `p_lo1..3`, `p_he1..3`, `p_ho1..3`, `p_res` plus final sum check `p_sum`)
- `StageB/UpperBound.lean`: **3** (`unit_ok`, `pair_u_ok`, `energy_sum_ok`)

Zero occurrences of `native_decide`.
