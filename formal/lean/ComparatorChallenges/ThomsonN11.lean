import Mathlib

/-!
# Thomson problem for N = 11 (challenge file)

Minimise the Coulomb energy `E(x) = ∑_{i<j} 1 / ‖x i - x j‖` over configurations of `N` pairwise
distinct points on the unit sphere `S² ⊂ ℝ³`, for `N = 11`.

* The (numerically known) minimum is `E₁(11) ≈ 40.596450508` (erratum: the project brief's
  original figure `39.783856229` was wrong — it lies below the true minimum; see `README.md`
  section 2 and `PROGRESS.md` section 3); the conjectured minimiser (C2v, edge-contracted
  icosahedron) and its provenance are described in `README.md` and `notes/strategy.md`.
* `N = 11` has no known simple one-parameter closed-form family, so unlike the `N = 7` challenge
  this file fixes NO candidate configuration. It only carries the base definitions and the two
  rational milestone lower bounds. The shape of the final theorem (the minimiser implicitly
  characterised as the unique solution of a stationarity system, in the style of the KLT `N = 8`
  paper's treatment of the square-antiprism height) is deliberately NOT part of this file; it is
  documented in `notes/strategy.md` and will be added here once the numerical structure of the
  candidate is settled.

## Provenance

`R3`, `SphereConfig`, `coulombEnergy`, `cyl` and the two auxiliary lemmas `norm_sq_cyl_sub`,
`norm_sq_cyl` are carried over verbatim from the N = 7 proof package
`references/thomson-n7-lean/formal/lean/ComparatorChallenges/ThomsonN7.lean` (only the namespace
and this header differ), so that the two projects state the problem in the same terms.

## Status

Everything below the base definitions is `sorry` by design: this is the fixed statement file
against which a future solution (`ThomsonN11/Solution.lean`) will be compared; see
`scripts/check.sh` and `scripts/compare_statements.py`.
-/

open Real

namespace ThomsonN11

/-- Euclidean 3-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- `n` pairwise distinct points on the unit sphere of `ℝ³`.
Injectivity is essential: with `1 / 0 = 0` in Lean, coincident points would otherwise be free. -/
def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}

/-- Coulomb (Riesz `s = 1`) energy `∑_{i<j} 1 / ‖x i - x j‖`. -/
noncomputable def coulombEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

/-- The point with cylindrical coordinates `(ρ, θ, h)`. -/
noncomputable def cyl (ρ θ h : ℝ) : R3 := !₂[ρ * cos θ, ρ * sin θ, h]

/-! ## Auxiliary facts (already proved; they show the definitions are well-posed) -/

lemma norm_sq_cyl_sub (ρ θ h ρ' θ' h' : ℝ) :
    ‖cyl ρ θ h - cyl ρ' θ' h'‖ ^ 2 = ρ ^ 2 + ρ' ^ 2 - 2 * ρ * ρ' * cos (θ - θ') + (h - h') ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, cos_sub]
  nlinarith [sin_sq_add_cos_sq θ, sin_sq_add_cos_sq θ']

lemma norm_sq_cyl (ρ θ h : ℝ) : ‖cyl ρ θ h‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, mul_pow]
  nlinarith [sin_sq_add_cos_sq θ]

/-! ## Challenge statements (to be proved)

The two milestones below are rational lower bounds for the Coulomb energy of any 11-point
configuration on the unit sphere. `M0` is a first weak bound that any serious method (even a
two-point / Yudin-style bound) should clear; `M1` is within `1.85` of the numerically known
optimum `≈ 40.596450508`, and is calibrated to be reachable by the planned three-point
semidefinite method (see `notes/strategy.md`). Both are milestones on the way to the eventual
theorem `E₁(11) = 40.596450508…` with its equality case; that theorem is not stated here yet. -/

/-- **Milestone M0 (Thomson, N = 11).** Every configuration of 11 distinct points on the unit
sphere has Coulomb energy at least `55 / 2 = 27.5`. -/
theorem thomson_eleven_M0 :
    ∀ x ∈ SphereConfig 11, (55 / 2 : ℝ) ≤ coulombEnergy x := by
  sorry

/-- **Milestone M1 (Thomson, N = 11).** Every configuration of 11 distinct points on the unit
sphere has Coulomb energy at least `155 / 4 = 38.75`. -/
theorem thomson_eleven_M1 :
    ∀ x ∈ SphereConfig 11, (155 / 4 : ℝ) ≤ coulombEnergy x := by
  sorry

end ThomsonN11
