# Proof Strategy, Obstruction Analysis, and Closure Roadmap (`notes/strategy.md`)

This note records the algebraic-geometric structure of the conjectured $N = 11$ Thomson minimizer, our exact three-point semidefinite programming (SDP) relaxation diagnosis, the Lean 4 Stage B architecture, the coupled four-point SDP hierarchy probe, and the roadmap toward a complete uniqueness proof.

---

## 1. Algebraic-Geometric Structure of the Conjectured Minimizer (Phase 0A)

Using **rational north-pole stereographic projection**
$$(u,v) \;\longmapsto\; \left(\frac{2u}{1+u^2+v^2},\; \frac{2v}{1+u^2+v^2},\; \frac{1-u^2-v^2}{1+u^2+v^2}\right),$$
with vertex $0$ fixed at the south pole $(0,0,-1)$, the conjectured global minimizer for $N = 11$---the $C_{2v}$ **edge-contracted icosahedron** with vertex-orbit decomposition $11 = 1 + 2 + 2 + 2 + 4$---is parameterized without square roots by five free real parameters $(t_1, t_2, t_3, u_4, v_4)$:

- **80-dps Newton stationary point** (`numerics/bounds/results/phase0_candidate.json`):
  - $t_1 = 0.327791655942445260192283\ldots$
  - $t_2 = 0.536744080969946669690331\ldots$
  - $t_3 = 1.768141527819571963164698\ldots$
  - $u_4 = 1.029202574133262161829355\ldots$
  - $v_4 = 0.587901288444605685653989\ldots$
- **Stationarity & energy:** $\|\nabla_{S^2} E(X^*_{11})\|_\infty = 8.52 \times 10^{-81}$,
  $$E^*(11) = 40.59645050819060538663553135833447301835336406781920\ldots$$
  The next lowest local minimum ($C_{5v}$ vertex-removed icosahedron, $1+5+5$) has energy $40.615117336946\ldots$ ($+0.0186668$).
- **Full $22 \times 22$ Riemannian Hessian spectrum:** 3 $\mathfrak{so}(3)$ rotational zero modes ($\le 1.73 \times 10^{-80}$) and 19 strictly positive eigenvalues with $\lambda_{\min}(H_0) = 0.090673217656229\ldots$ ($\lambda_{\max}(H_0) = 7.6248624744517\ldots$; smallest eigenvalue on the 5D $C_{2v}$ subspace is $0.8103354558\ldots$).
- **Pairwise inner-product spectrum:** The $\binom{11}{2} = 55$ pairs split into **20 distinct inner-product orbits**:
  - Minimum inner product $m^* = -0.99902279345944761272\ldots$ (multiplicity 2, disjoint nearly antipodal pairs $(3,6)$ and $(4,5)$, angle $177.467^\circ$); **no exact antipodal pairs**.
  - Second-smallest level $-0.94331002254210\ldots$ (multiplicity 2); maximum inner product $+0.52190976643867\ldots$ (multiplicity 2).
  - Minimum adjacent level separation $g_{\min} = 0.00369731146725\ldots$ (between levels 6 and 7: $-0.46891710$ and $-0.46521979$).
- **Zero-square-root Lean 4 advantage:** Any rational parameters $(t_1, t_2, t_3, u_4, v_4) \in \mathbb{Q}^5$ map to 11 points lying **identically** on $S^2$ as integer projective quadruples $(X_i, Y_i, Z_i, D_i)$ with $X_i^2 + Y_i^2 + Z_i^2 = D_i^2$. Rounding the parameters to denominator $10^9$ perturbs the energy only at second order ($+1.78 \times 10^{-18}$), allowing `StageB.UpperBound.c2vWitness` to certify $E_1(11) \le 2029822525409531 / 50000000000000 = 40.59645050819062$ inside Lean 4 using pure integer arithmetic.

---

## 2. Three-Point SDP Tightness Sweep and Intrinsic Obstruction Diagnosis (Phase 0B)

### 2.1 Exact Rational Certificate Summary

Using the pure-`Fraction` $S_3$-isotypic engine `sym_cap_sdpa.py` (with uncapped harmonic order $K = M$) and the $(2,9)$-typed pole-ring strip engine `sym_strip_sdpa.py`, together with high-precision `SDPA-GMP` solves and exact integer Bareiss Sylvester PD verification, we obtain **15** exact rational certificates (410 PSD blocks, zero identity error):

| Model & Inner-Product Domain | $(M, K)$ | Poly. Deg. $D$ | Certified Lower Bound $e_{\mathrm{cert}}$ | Gap $\Delta = E^*(11) - e_{\mathrm{cert}}$ |
|---|---:|---:|---:|---:|
| Global $S_3$, $t \in [-1, 1]$ | $(6, 6)$ | $10$ | `40.533315701817` | `0.06313481` |
| Global $S_3$, $t \in [-1, 1]$ | $(7, 7)$ | $12$ | `40.545314785703` | `0.05113572` |
| Global $S_3$, $t \in [-1, 1]$ | $(8, 8)$ | $14$ | `40.551494289332` | `0.04495622` |
| Global $S_3$, $t \in [-1, 1]$ | $(9, 9)$ | $16$ | `40.554160636831` | `0.04228987` |
| **Global $S_3$, $t \in [-1, 1]$ (formalized in Lean 4)** | **$(10, 10)$** | **$18$** | **`40.555471704371`** | **`0.04097880`** |
| **Global $S_3$, $t \in [-1, 1]$ (strongest Stage A cert)** | **$(12, 12)$** | **$22$** | **`40.556960329409`** | **`0.03949018`** |
| Lower cap cut $S_3$, $t \in [-1023/1024, 1]$ | $(6, 6)$ | $10$ | `40.533320366836` | `0.06313014` |
| Lower cap cut $S_3$, $t \in [-1023/1024, 1]$ | $(8, 8)$ | $14$ | `40.551516085750` | `0.04493442` |
| Lower cap cut $S_3$, $t \in [-1023/1024, 1]$ | $(10, 10)$ | $18$ | `40.555539579695` | `0.04091093` |
| Lower cap cut $S_3$, $t \in [-1023/1024, 1]$ | $(12, 12)$ | $22$ | `40.556970864736` | `0.03947964` |
| Upper cap cut $S_3$, $t \in [-1, 53/100]$ | $(8, 8)$ | $14$ | `40.551787212256` | `0.04466330` |
| Deep cap cut $S_3$, $t \in [-49/50, 1]$ | $(8, 8)$ | $14$ | `40.554952399256` | `0.04149811` |
| Strong cap cut $S_3$, $t \in [-9/10, 1]$ | $(8, 8)$ | $14$ | `40.584934945776` | `0.01151556` (still $< E^*(11)$ despite excluding $X^*_{11}$) |
| $(2,9)$ typed strip, $t_{01} \in [-1, -1023/1024]$ | $(6, 6)$ | $10$ | `40.536870920686` | `0.05957959` |
| $(2,9)$ typed narrow strip, $t_{01} \in [-9991/10000, -999/1000]$ | $(7, 7)$ | $12$ | `40.548003495494` | `0.04844701` |

*Harmonic parity selection rule:* At $(M,K)=(12,12)$ (224-bit `SDPA-GMP`, `pdOPT` in $9{,}541.6\,\mathrm{s}$), blocks $F_0, \dots, F_8$ are active ($\operatorname{tr} F_8 = 0.02057$), odd orders $F_9 \approx 3.44 \times 10^{-20}$ and $F_{11} \approx 5.72 \times 10^{-23}$ are strictly inactive, while the even order $F_{10} = 1.05 \times 10^{-4}$ activates---matching the exact spherical-harmonic invariant degrees $\ell \in \{0, 6, 10, 12, \dots\}$ of the icosahedral group $I_h$ (which has no $\ell = 9$ or $\ell = 11$ invariants). Raising $(10,10) \to (12,12)$ adds only $+0.0014886$ (`0.0037%`) while expanding SOS block sizes and kernel Kronecker widths dramatically, so Stage A preserves and verifies the full ladder through $(12,12)$ while Stage B formalizes the clean $(10,10)$ global certificate (`40.55547170437074`).

### 2.2 First-Principles Diagnosis of the $\Delta \approx 0.0395$ Obstruction

1. **Polynomial degree is not the bottleneck:** Solving the discrete-grid 1D minorant LP $\max \sum_{i<j} H(t^*_{ij})$ subject to $2y H(1 - 2y^2) \le 1$ on $20{,}001$ nodes in $y \in [10^{-4}, 1]$ evaluated on the true moments of $X^*_{11}$ yields `40.586405` at $M=4$, `40.596353` at $M=6$, and **`40.59645006` at $M = 8$ ($\deg H = 14$, gap $4.52 \times 10^{-7}$)**---five orders of magnitude tighter than the same-degree three-point SDP (`40.551494`).
2. **Fractional-icosahedral dual pseudo-measure:** Extracting the optimal $(10,10)$ dual pair pseudo-moments $(\mu_0, \dots, \mu_{18})$ reveals a positive-definite $10 \times 10$ Hankel matrix whose 9-atom Gauss–Christoffel quadrature measure (total mass $55$ pairs) places:
   - **$3.3946$ effective pairs at $t_1 = -0.999637$** (with exact endpoint tangency $H^*(-1) = \varphi(-1) = 0.5$ to $5 \times 10^{-16}$),
   - **$18.0106$ effective pairs at $t_4 = -0.435716 \approx -1/\sqrt{5}$**, and
   - **$21.8655$ effective pairs** split across $t_7 = +0.413865$ ($14.1025$) and $t_8 = +0.481741$ ($7.7630$) around $+1/\sqrt{5}$.
   Compared with the 12-vertex icosahedron ($-1 \times 6,\; -1/\sqrt{5} \times 30,\; +1/\sqrt{5} \times 30$), the three-point SDP fabricates a **fractional 11-point icosahedral pseudo-configuration** carrying $\approx 3.4$ antipodal pairs.
3. **Why single-pair slab+cap splitting fails (dual lock-in):** Minimizing the true Coulomb energy on $(S^2)^{11}$ subject to $k$ exact antipodal pairs yields:
   - $k = 0$: `40.59645051` (unconstrained $X^*_{11}$)
   - $k = 1$: `40.59690735` ($+0.000457$)
   - $k = 2$: `40.59767735` ($+0.001227$)
   - $k = 3$: `40.62578443` ($+0.029334$)
   - $k = 4$: `40.78043465` ($+0.183984$)
   - $k = 5$: `40.90067129` ($+0.304221$)
   Thus (a) true $k=1, 2$ configurations sit only $4.6 \times 10^{-4}$ above $E^*(11)$, preventing single-pair $(2,9)$ slab exclusion near $t = -1$, while (b) three-point SDP enforces only $3\times 3$ Gram positivity ($\det G_3 \ge 0$) and misses the four-point Euclidean realizability identity $\det G_4 = 0$ that enforces the $+0.03\text{--}+0.18$ 3D frustration jump for $k \ge 3$.

---

## 3. Lean 4 Engineering Architecture (Stage B)

Two engineering innovations keep the kernel verification fast and memory-frugal with zero external trust:

1. **Zero-Mathlib pure-`Init` certificate layer (`StageB/PolyKronDefs.lean`):** Polynomial evaluators, the binary bit-trie `Trie Int`, and 2D-Kronecker slice checkers depend solely on Lean's `Init` library. `SdpCertHarmData.lean`, `SdpCertSosData.lean`, and all 19 parallel slice modules `SdpCertSosSlice{M9..9}.lean` import zero Mathlib modules, cutting per-process memory from `~3.5 GB` to `< 300 MB` and eliminating Mathlib `.olean` load latency.
2. **100% pure-`ℤ` projective upper-bound witness (`StageB/UpperBound.lean`):** Rational stereographic coordinates are stored as integer quadruples $(X_i, Y_i, Z_i, D_i)$ satisfying $X_i^2 + Y_i^2 + Z_i^2 = D_i^2$, and pairwise inverse-distance upper bounds $u_{ij} / S_{\mathrm{inv}}$ ($S_{\mathrm{inv}} = 5 \times 10^{16}$) are checked by 55 pure integer squarings inside `decide +kernel`, avoiding all rational GCD normalization and `Finset` expansion overhead.

---

## 4. Coupled Four-Point SDP Hierarchy Probe (Phase 0C) and Closure Roadmap

In `numerics/bounds/phase0_4pt_probe.py` (`results/phase0_4pt_probe.json`), we implement all three $S_{11} \times O(3)$-invariant four-point constraint families (every column and block entry verified with exact zero `Fraction` error on a random rational 11-point sphere configuration):
- **Case 4 (4 free vertices):** ideal multipliers $q(e)\det G_4(e) = 0$ ($\deg q \le D_4 - 4$), $\mathbb{Z}_2 \times \mathbb{Z}_2$-block-diagonalized Putinar SOS on $1, 1 \pm t_{01}$, and $\mathbb{Z}_2$-block-diagonalized face-Gram SOS on $\det G_3(0,1,2) \ge 0$.
- **Case 2 (2 free vertices + 1 summed neighbor):** Binet–Cauchy cross-product block `Harm4_odd` and pair-flag block `Flag2_even`.
- **Case 0 (0 free vertices + 2 summed vertices):** global $(\mathbb{R}^3)^{\otimes d}$ pair-tensor blocks `GlobNat_d*` and `GlobAx_d*` coupling disjoint pairs, 3-edge paths, and $I_3$ dimension contractions ($\|I_3\|^2 = 3$).

### 4.1 Probe Findings
1. **Strict matched-degree strengthening:** Four-point constraints strictly lift same-degree three-point bounds:
   - $D_3 = D_4 = 6$ ($M = 4$): `40.32802558` $\to$ **`40.49109850`** (**`+0.16307292`**);
   - $D_3 = D_4 = 8$ ($M = 5$): `40.50635763` $\to$ `40.50651291` at $D_4 = 6$ (`+0.00015528`), and **`40.51417969`** at $D_4 = 8$ (**`+0.00782206`**).
2. **Low-degree resolution bottleneck ($D_4 \le 8$):** Coupling $D_4 \in \{4, 6\}$ onto high-degree three-point $M = 8$ ($D_3 = 14$, `40.55149429`) yields zero gain (`< 10^{-11}`), showing that the 9-atom pseudo-measure admits a feasible degree-6 four-point moment extension.

### 4.2 Roadmap to Full Closure of $N = 11$
1. **High-degree full $S_4$-isotypic four-point SDP ($D_4 \ge 14\text{--}18$):** Upgrade four-point SOS and tensor blocks from $\mathbb{Z}_2 \times \mathbb{Z}_2$ to full $S_4$ irreducible representation block-diagonalization (~6x reduction in matrix dimension) so four-point polynomial degree reaches the resolution regime needed to separate the 9 fractional-icosahedral atoms.
2. **Multi-pair matching branch-and-bound + SDP pruning:** Branch on the matching number $k \in \{0, 1, 2, \ge 3\}$ of the near-antipodal graph $G_{\le -0.95}$ (using $(2k, 11-2k)$-typed SDP for $k \ge 3$, lower-dimensional interval branch-and-bound for $k = 1, 2$, and Krawczyk + $33 \times 33$ integer-Cholesky Riemannian Hessian certification in a neighborhood of $X^*_{11}$).
