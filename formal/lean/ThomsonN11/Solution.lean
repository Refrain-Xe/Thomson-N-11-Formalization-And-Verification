import Mathlib
import ThomsonN11.StageB.SdpCert
import ThomsonN11.StageB.UpperBound

/-!
# Thomson problem for N = 11 — formal proofs of M0, M1, M10 SDP lower bound, and C2v upper bound

This module proves the fixed milestone lower bounds in `ComparatorChallenges/ThomsonN11.lean`
together with the strengthened universal 3-point SDP lower bound and rational C2v upper bound:

* `ThomsonN11.thomson_eleven_M0` : every 11-point configuration on the unit sphere has
  Coulomb energy at least `55 / 2 = 27.5`.
* `ThomsonN11.thomson_eleven_M1` : every 11-point configuration on the unit sphere has
  Coulomb energy at least `155 / 4 = 38.75`.
* `ThomsonN11.thomson_eleven_sdp_M10` : every 11-point configuration on the unit sphere has
  Coulomb energy at least `2027773585218537 / 50000000000000 = 40.55547170437074`
  (certified via the degree-18 `S₃` three-point SDP relaxation at `M = 10, K = 10`).
* `ThomsonN11.thomson_eleven_upper_bound` : there exists an explicit rational C2v 11-point
  configuration on the unit sphere with Coulomb energy at most
  `2029822525409531 / 50000000000000 = 40.59645050819062`.
* `ThomsonN11.thomson_eleven_bounds_sandwich` : combined two-sided rigorous energy bracket
  for Thomson `N = 11` (residual three-point relaxation gap `0.0409788…`).
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

/-! ## Milestone M0 -/

/-- **Milestone M0 (Thomson, N = 11).** Every configuration of 11 distinct points on the unit
sphere has Coulomb energy at least `55 / 2 = 27.5`. -/
theorem thomson_eleven_M0 :
    ∀ x ∈ SphereConfig 11, (55 / 2 : ℝ) ≤ coulombEnergy x := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have key : ∀ i : Fin 11, ∀ j ∈ Finset.Ioi i, (2 : ℝ)⁻¹ ≤ ‖x i - x j‖⁻¹ := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hne : x i ≠ x j := fun he => (ne_of_lt hij) (hx2 he)
    have hpos : 0 < ‖x i - x j‖ := norm_sub_pos_iff.mpr hne
    have hle : ‖x i - x j‖ ≤ 2 := by
      have h := norm_sub_le (x i) (x j)
      rw [hx1 i, hx1 j] at h
      linarith
    exact inv_anti₀ hpos hle
  have hcount : ∑ i : Fin 11, ((Finset.Ioi i).card : ℝ) = 55 := by
    have h : ∑ i : Fin 11, (Finset.Ioi i).card = 55 := by decide
    exact_mod_cast h
  have hinner : ∀ i : Fin 11,
      ∑ j ∈ Finset.Ioi i, (2 : ℝ)⁻¹ = ((Finset.Ioi i).card : ℝ) * (2 : ℝ)⁻¹ := by
    intro i
    simp [Finset.sum_const]
  show (55 / 2 : ℝ) ≤ ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹
  calc (55 / 2 : ℝ) = 55 * (2 : ℝ)⁻¹ := by norm_num
    _ = (∑ i : Fin 11, ((Finset.Ioi i).card : ℝ)) * (2 : ℝ)⁻¹ := by rw [hcount]
    _ = ∑ i : Fin 11, ((Finset.Ioi i).card : ℝ) * (2 : ℝ)⁻¹ := by rw [Finset.sum_mul]
    _ = ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, (2 : ℝ)⁻¹ := by simp only [← hinner]
    _ ≤ ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => key i j hj

/-! ## Helpers for Milestone M1 -/

private def dot (v w : R3) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

private lemma dot_symm (v w : R3) : dot v w = dot w v := by
  unfold dot; ring

private lemma norm_sq_coords (v : R3) :
    ‖v‖ ^ 2 = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, pow_two]

private lemma norm_sub_sq_coords (v w : R3) :
    ‖v - w‖ ^ 2 = (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) + (w 0 * w 0 + w 1 * w 1 + w 2 * w 2)
      - 2 * dot v w := by
  rw [norm_sq_coords]
  simp only [PiLp.sub_apply]
  unfold dot
  ring

private lemma norm_add_sq_coords (v w : R3) :
    ‖v + w‖ ^ 2 = (v 0 * v 0 + v 1 * v 1 + v 2 * v 2) + (w 0 * w 0 + w 1 * w 1 + w 2 * w 2)
      + 2 * dot v w := by
  rw [norm_sq_coords]
  simp only [PiLp.add_apply]
  unfold dot
  ring

private lemma sum_Ioi_half {n : ℕ} {g : Fin n → Fin n → ℝ} (hsym : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j ∈ Finset.Ioi i, g i j = (∑ i, ∑ j, g i j - ∑ i, g i i) / 2 := by
  have hpart : ∀ i : Fin n, ∑ j : Fin n, g i j
      = (∑ j ∈ Finset.Ioi i, g i j) + (∑ j ∈ Finset.Iio i, g i j) + g i i := by
    intro i
    have hdisj1 : Disjoint (Finset.Ioi i) (Finset.Iio i ∪ ({i} : Finset (Fin n))) := by
      rw [Finset.disjoint_right]
      intro x hx h2
      rcases Finset.mem_union.mp hx with h | h
      · simp only [Finset.mem_Iio] at h; simp only [Finset.mem_Ioi] at h2; omega
      · simp only [Finset.mem_singleton] at h; subst h
        simp only [Finset.mem_Ioi] at h2; omega
    have hdisj2 : Disjoint (Finset.Iio i) ({i} : Finset (Fin n)) := by
      rw [Finset.disjoint_right]
      intro x hx h2
      simp only [Finset.mem_singleton] at hx
      simp only [Finset.mem_Iio] at h2
      subst hx
      omega
    have huniv : (Finset.univ : Finset (Fin n))
        = Finset.Ioi i ∪ (Finset.Iio i ∪ ({i} : Finset (Fin n))) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio,
        Finset.mem_singleton]
      rcases lt_trichotomy j i with h | h | h <;> simp [h]
    rw [huniv, Finset.sum_union hdisj1, Finset.sum_union hdisj2, Finset.sum_singleton]
    ring
  have htot : ∑ i, ∑ j, g i j
      = (∑ i, ∑ j ∈ Finset.Ioi i, g i j) + (∑ i, ∑ j ∈ Finset.Iio i, g i j) + ∑ i, g i i := by
    rw [Finset.sum_congr rfl (fun i _ => hpart i)]
    simp only [Finset.sum_add_distrib]
  have htri : (∑ i, ∑ j ∈ Finset.Iio i, g i j) = (∑ i, ∑ j ∈ Finset.Ioi i, g i j) := by
    have eIio : ∀ i : Fin n, (∑ j ∈ Finset.Iio i, g i j)
        = ∑ j : Fin n, if j < i then g i j else 0 := by
      intro i
      have hf : Finset.Iio i = (Finset.univ : Finset (Fin n)).filter (fun j => j < i) := by
        ext j; simp [Finset.mem_filter, Finset.mem_Iio]
      rw [hf, Finset.sum_filter]
    have eIoi : ∀ i : Fin n, (∑ j ∈ Finset.Ioi i, g i j)
        = ∑ j : Fin n, if i < j then g i j else 0 := by
      intro i
      have hf : Finset.Ioi i = (Finset.univ : Finset (Fin n)).filter (fun j => i < j) := by
        ext j; simp [Finset.mem_filter, Finset.mem_Ioi]
      rw [hf, Finset.sum_filter]
    have hL : (∑ i, ∑ j ∈ Finset.Iio i, g i j)
        = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ,
            if p.2 < p.1 then g p.1 p.2 else 0 :=
      calc (∑ i, ∑ j ∈ Finset.Iio i, g i j)
          = ∑ i, ∑ j : Fin n, if j < i then g i j else 0 :=
              Finset.sum_congr rfl (fun i _ => eIio i)
        _ = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ,
              if p.2 < p.1 then g p.1 p.2 else 0 :=
              (Finset.sum_product (Finset.univ : Finset (Fin n))
                (Finset.univ : Finset (Fin n))
                (fun p => if p.2 < p.1 then g p.1 p.2 else 0)).symm
    have hR : (∑ i, ∑ j ∈ Finset.Ioi i, g i j)
        = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ,
            if p.2 < p.1 then g p.1 p.2 else 0 :=
      calc (∑ i, ∑ j ∈ Finset.Ioi i, g i j)
          = ∑ i, ∑ j : Fin n, if i < j then g i j else 0 :=
              Finset.sum_congr rfl (fun i _ => eIoi i)
        _ = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ,
              if p.1 < p.2 then g p.1 p.2 else 0 :=
              (Finset.sum_product (Finset.univ : Finset (Fin n))
                (Finset.univ : Finset (Fin n))
                (fun p => if p.1 < p.2 then g p.1 p.2 else 0)).symm
        _ = ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.univ,
              if p.2 < p.1 then g p.1 p.2 else 0 := by
              refine Finset.sum_nbij (fun p => (p.2, p.1))
                (fun a _ => Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
                (fun a _ b _ h => Prod.swap_injective h)
                (fun b _ => ⟨(b.2, b.1),
                  Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, Prod.mk.eta⟩)
                (fun a _ => by rw [hsym a.2 a.1])
    rw [hL, hR]
  rw [htot, htri]
  ring

private noncomputable def fM1 (t : ℝ) : ℝ := 7 / 10 + 2 / 5 * t + 7 / 40 * t ^ 2

private lemma fM1_minorant_nonneg {t : ℝ} (hm : -1 ≤ t) (h1 : t ≤ 1) :
    (0 : ℝ) ≤ 1 - 2 * (1 - t) * (fM1 t) ^ 2 := by
  have h1p : (0 : ℝ) ≤ 1 + t := by linarith
  have h1m : (0 : ℝ) ≤ 1 - t := by linarith
  have hid : 1 - 2 * (1 - t) * (fM1 t) ^ 2 =
      (1 + t) * ((1 / 32 : ℝ) * (-19 / 40 + 1291 / 400 * t + 499 / 400 * t ^ 2) ^ 2
        + (157279 / 20480000 : ℝ) * (4580 / 157279 + 305398 / 157279 * t - 309978 / 157279 * t ^ 2) ^ 2
        + (3053833 / 503292800 : ℝ) * (1 - 2 * t + t ^ 2) ^ 2)
      + (1 - t) * ((11 / 1600 : ℝ) * (-17 / 44 + 29 / 11 * t + 7 / 4 * t ^ 2) ^ 2
        + (19 / 11264 : ℝ) * (146 / 95 - 102 / 95 * t - 44 / 95 * t ^ 2) ^ 2
        + (907 / 486400 : ℝ) * (1 - 2 * t + t ^ 2) ^ 2) := by
    unfold fM1
    ring
  rw [hid]
  positivity

private lemma double_sum_dot_nonneg {n : ℕ} (x : Fin n → R3) :
    (0 : ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, dot (x i) (x j) := by
  have hcoord : ∀ a : Fin 3,
      ∑ i : Fin n, ∑ j : Fin n, x i a * x j a = (∑ i : Fin n, x i a) ^ 2 := by
    intro a
    rw [sq, Finset.sum_mul_sum]
  have hexp : (∑ i : Fin n, ∑ j : Fin n, dot (x i) (x j)) =
      (∑ i : Fin n, x i 0) ^ 2 + (∑ i : Fin n, x i 1) ^ 2 + (∑ i : Fin n, x i 2) ^ 2 := by
    simp only [dot, Finset.sum_add_distrib, hcoord]
  rw [hexp]
  positivity

private lemma double_sum_dot_sq_ge {n : ℕ} (x : Fin n → R3)
    (hn : ∀ i : Fin n, x i 0 * x i 0 + x i 1 * x i 1 + x i 2 * x i 2 = 1) :
    ((n : ℝ) ^ 2) ≤ 3 * ∑ i : Fin n, ∑ j : Fin n, (dot (x i) (x j)) ^ 2 := by
  let M : Fin 3 → Fin 3 → ℝ := fun a b => ∑ i : Fin n, x i a * x i b
  have hpair : ∀ a b : Fin 3,
      ∑ i : Fin n, ∑ j : Fin n, (x i a * x j a) * (x i b * x j b) = (M a b) ^ 2 := by
    intro a b
    have hrew : ∀ i j : Fin n,
        (x i a * x j a) * (x i b * x j b) = (x i a * x i b) * (x j a * x j b) := by
      intro i j; ring
    simp only [hrew]
    rw [sq, ← Finset.sum_mul_sum]
  have hdot2 : ∀ i j : Fin n, (dot (x i) (x j)) ^ 2 =
      (x i 0 * x j 0) * (x i 0 * x j 0)
      + (x i 1 * x j 1) * (x i 1 * x j 1)
      + (x i 2 * x j 2) * (x i 2 * x j 2)
      + 2 * ((x i 0 * x j 0) * (x i 1 * x j 1))
      + 2 * ((x i 0 * x j 0) * (x i 2 * x j 2))
      + 2 * ((x i 1 * x j 1) * (x i 2 * x j 2)) := by
    intro i j; unfold dot; ring
  have hmul2 : ∀ a b : Fin 3,
      ∑ i : Fin n, ∑ j : Fin n, 2 * ((x i a * x j a) * (x i b * x j b)) = 2 * (M a b) ^ 2 := by
    intro a b
    calc ∑ i : Fin n, ∑ j : Fin n, 2 * ((x i a * x j a) * (x i b * x j b))
        = ∑ i : Fin n, 2 * ∑ j : Fin n, (x i a * x j a) * (x i b * x j b) :=
            Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ 2).symm
      _ = 2 * ∑ i : Fin n, ∑ j : Fin n, (x i a * x j a) * (x i b * x j b) :=
            (Finset.mul_sum _ _ 2).symm
      _ = 2 * (M a b) ^ 2 := by rw [hpair a b]
  have hsum2 : (∑ i : Fin n, ∑ j : Fin n, (dot (x i) (x j)) ^ 2) =
      (M 0 0) ^ 2 + (M 1 1) ^ 2 + (M 2 2) ^ 2
      + 2 * (M 0 1) ^ 2 + 2 * (M 0 2) ^ 2 + 2 * (M 1 2) ^ 2 := by
    simp only [hdot2, Finset.sum_add_distrib, hpair, hmul2]
  have htr : M 0 0 + M 1 1 + M 2 2 = (n : ℝ) := by
    dsimp [M]
    calc (∑ i : Fin n, x i 0 * x i 0) + (∑ i : Fin n, x i 1 * x i 1) + (∑ i : Fin n, x i 2 * x i 2)
        = ∑ i : Fin n, (x i 0 * x i 0 + x i 1 * x i 1 + x i 2 * x i 2) := by
            simp only [Finset.sum_add_distrib]
      _ = ∑ _i : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun i _ => hn i
      _ = (n : ℝ) := by simp
  have hdiff : 3 * (∑ i : Fin n, ∑ j : Fin n, (dot (x i) (x j)) ^ 2) - (n : ℝ) ^ 2 =
      (M 0 0 - M 1 1) ^ 2 + (M 1 1 - M 2 2) ^ 2 + (M 2 2 - M 0 0) ^ 2
      + 6 * (M 0 1) ^ 2 + 6 * (M 0 2) ^ 2 + 6 * (M 1 2) ^ 2 := by
    rw [hsum2, ← htr]
    ring
  have hnn : (0 : ℝ) ≤ (M 0 0 - M 1 1) ^ 2 + (M 1 1 - M 2 2) ^ 2 + (M 2 2 - M 0 0) ^ 2
      + 6 * (M 0 1) ^ 2 + 6 * (M 0 2) ^ 2 + 6 * (M 1 2) ^ 2 := by positivity
  linarith

/-! ## Milestone M1 -/

/-- **Milestone M1 (Thomson, N = 11).** Every configuration of 11 distinct points on the unit
sphere has Coulomb energy at least `155 / 4 = 38.75`. -/
theorem thomson_eleven_M1 :
    ∀ x ∈ SphereConfig 11, (155 / 4 : ℝ) ≤ coulombEnergy x := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hn : ∀ i : Fin 11, x i 0 * x i 0 + x i 1 * x i 1 + x i 2 * x i 2 = 1 := by
    intro i
    have h := norm_sq_coords (x i)
    rw [hx1 i, one_pow] at h
    exact h.symm
  have hsq : ∀ i j : Fin 11, ‖x i - x j‖ ^ 2 = 2 - 2 * dot (x i) (x j) := by
    intro i j
    have h := norm_sub_sq_coords (x i) (x j)
    rw [hn i, hn j] at h
    linarith
  have hplus : ∀ i j : Fin 11, ‖x i + x j‖ ^ 2 = 2 + 2 * dot (x i) (x j) := by
    intro i j
    have h := norm_add_sq_coords (x i) (x j)
    rw [hn i, hn j] at h
    linarith
  have pairwise : ∀ i : Fin 11, ∀ j ∈ Finset.Ioi i,
      fM1 (dot (x i) (x j)) ≤ (‖x i - x j‖)⁻¹ := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hne : x i ≠ x j := fun he => (ne_of_lt hij) (hx2 he)
    have hd : (0 : ℝ) < ‖x i - x j‖ := norm_sub_pos_iff.mpr hne
    have hT1 : dot (x i) (x j) ≤ 1 := by
      have h : (0 : ℝ) ≤ ‖x i - x j‖ ^ 2 := sq_nonneg _
      rw [hsq i j] at h
      linarith
    have hTm1 : -1 ≤ dot (x i) (x j) := by
      have h : (0 : ℝ) ≤ ‖x i + x j‖ ^ 2 := sq_nonneg _
      rw [hplus i j] at h
      linarith
    have hp := fM1_minorant_nonneg hTm1 hT1
    have hf : (fM1 (dot (x i) (x j))) ^ 2 * ‖x i - x j‖ ^ 2 ≤ 1 := by
      rw [hsq i j]
      nlinarith
    have hfd : fM1 (dot (x i) (x j)) * ‖x i - x j‖ ≤ 1 := by
      have h2 : (fM1 (dot (x i) (x j)) * ‖x i - x j‖) ^ 2 ≤ (1 : ℝ) ^ 2 := by
        rw [mul_pow]
        linarith
      exact (abs_le_of_sq_le_sq' h2 zero_le_one).2
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hd).mpr hfd
  have hsum_le : ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, fM1 (dot (x i) (x j)) ≤ coulombEnergy x :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => pairwise i j hj
  have hhalf : ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, fM1 (dot (x i) (x j)) =
      ((∑ i : Fin 11, ∑ j : Fin 11, fM1 (dot (x i) (x j)))
        - ∑ i : Fin 11, fM1 (dot (x i) (x i))) / 2 :=
    sum_Ioi_half fun i j => by rw [dot_symm]
  have hdiag : ∑ i : Fin 11, fM1 (dot (x i) (x i)) = 561 / 40 := by
    have h1 : ∀ i : Fin 11, fM1 (dot (x i) (x i)) = 51 / 40 := by
      intro i
      have hdii : dot (x i) (x i) = 1 := hn i
      rw [hdii]
      unfold fM1
      norm_num
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  have hfull : (11011 / 120 : ℝ) ≤ ∑ i : Fin 11, ∑ j : Fin 11, fM1 (dot (x i) (x j)) := by
    have hm1 := double_sum_dot_nonneg x
    have hm2 := double_sum_dot_sq_ge x hn
    have hconst : ∑ _i : Fin 11, ∑ _j : Fin 11, (7 / 10 : ℝ) = 847 / 10 := by
      simp [Finset.sum_const]
      norm_num
    have hlin : ∑ i : Fin 11, ∑ j : Fin 11, (2 / 5 : ℝ) * dot (x i) (x j) =
        (2 / 5 : ℝ) * ∑ i : Fin 11, ∑ j : Fin 11, dot (x i) (x j) := by
      calc ∑ i : Fin 11, ∑ j : Fin 11, (2 / 5 : ℝ) * dot (x i) (x j)
          = ∑ i : Fin 11, (2 / 5 : ℝ) * ∑ j : Fin 11, dot (x i) (x j) :=
              Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ = (2 / 5 : ℝ) * ∑ i : Fin 11, ∑ j : Fin 11, dot (x i) (x j) :=
              (Finset.mul_sum _ _ _).symm
    have hquad : ∑ i : Fin 11, ∑ j : Fin 11, (7 / 40 : ℝ) * (dot (x i) (x j)) ^ 2 =
        (7 / 40 : ℝ) * ∑ i : Fin 11, ∑ j : Fin 11, (dot (x i) (x j)) ^ 2 := by
      calc ∑ i : Fin 11, ∑ j : Fin 11, (7 / 40 : ℝ) * (dot (x i) (x j)) ^ 2
          = ∑ i : Fin 11, (7 / 40 : ℝ) * ∑ j : Fin 11, (dot (x i) (x j)) ^ 2 :=
              Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ = (7 / 40 : ℝ) * ∑ i : Fin 11, ∑ j : Fin 11, (dot (x i) (x j)) ^ 2 :=
              (Finset.mul_sum _ _ _).symm
    have hexp : (∑ i : Fin 11, ∑ j : Fin 11, fM1 (dot (x i) (x j))) =
        (847 / 10 : ℝ)
        + (2 / 5 : ℝ) * (∑ i : Fin 11, ∑ j : Fin 11, dot (x i) (x j))
        + (7 / 40 : ℝ) * (∑ i : Fin 11, ∑ j : Fin 11, (dot (x i) (x j)) ^ 2) := by
      simp only [fM1, Finset.sum_add_distrib, hconst, hlin, hquad]
    rw [hexp]
    push_cast at hm2
    linarith
  linarith [hsum_le, hhalf, hdiag, hfull]

/-! ## Strengthened 3-Point SDP Universal Lower Bound & C2v Rational Upper Bound -/

/-- **Strengthened Universal Lower Bound (Thomson, N = 11, 3-point SDP `M = 10, K = 10`).**
Every configuration of 11 distinct points on the unit sphere has Coulomb energy at least
`2027773585218537 / 50000000000000 = 40.55547170437074`. -/
theorem thomson_eleven_sdp_M10 :
    ∀ x ∈ SphereConfig 11,
      (2027773585218537 / 50000000000000 : ℝ) ≤ coulombEnergy x := by
  intro x ⟨hu, hinj⟩
  have h := StageB.SdpCert.global_sdp_lower_bound x hu hinj
  have hc : ((StageB.SdpCertHarmData.bound_num : ℝ) / (StageB.SdpCertHarmData.bound_den : ℝ)) =
      (2027773585218537 / 50000000000000 : ℝ) := by
    norm_num [StageB.SdpCertHarmData.bound_num, StageB.SdpCertHarmData.bound_den]
  rw [hc] at h
  exact h

/-- **Certified Rational C2v Upper Bound (Thomson, N = 11).**
There exists an explicit rational 11-point configuration on the unit sphere
(`StageB.UpperBound.c2vWitness`, with C2v `1+2+2+2+4` symmetry) whose Coulomb energy is at most
`2029822525409531 / 50000000000000 = 40.59645050819062`. -/
theorem thomson_eleven_upper_bound :
    ∃ x ∈ SphereConfig 11,
      coulombEnergy x ≤ (2029822525409531 / 50000000000000 : ℝ) := by
  refine ⟨StageB.UpperBound.c2vWitness,
    ⟨StageB.UpperBound.c2vWitness_unit, StageB.UpperBound.c2vWitness_injective⟩, ?_⟩
  exact StageB.UpperBound.c2vWitness_energy_le

/-- **Certified Energy Sandwich (Thomson, N = 11).**
Combines the universal `M = 10, K = 10` three-point SDP lower bound and the explicit rational
C2v upper-bound witness, bracketing the optimal 11-electron Coulomb energy:
`40.55547170437074 ≤ E₁(11) ≤ 40.59645050819062`. -/
theorem thomson_eleven_bounds_sandwich :
    (∀ x ∈ SphereConfig 11, (2027773585218537 / 50000000000000 : ℝ) ≤ coulombEnergy x) ∧
    (∃ x ∈ SphereConfig 11, coulombEnergy x ≤ (2029822525409531 / 50000000000000 : ℝ)) :=
  ⟨thomson_eleven_sdp_M10, thomson_eleven_upper_bound⟩

end ThomsonN11
