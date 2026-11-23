import ThomsonN11.StageB.ThreePoint

/-!
# Thomson N = 11 — Exact Rational Stereographic C2v Witness & Upper Bound

Constructs an explicit rational C2v configuration `c2vWitness : Fin 11 → R3` on the unit
sphere (via rational stereographic parameters, stored as pure integer projective tuples
`(X, Y, Z, D)` with `X² + Y² + Z² = D²`) and proves
`coulombEnergy11 c2vWitness ≤ 2029822525409531 / 50000000000000`
(`= 40.59645050819062`, within `1.5 × 10⁻¹⁴` of `E₁(11)`).
-/

set_option maxHeartbeats 4000000

namespace ThomsonN11.StageB.UpperBound

open Finset ThomsonN11.StageB

def S_inv : ℤ := Int.ofNat 50000000000000000
def ub_scaled : ℤ := Int.ofNat 2029822525409531000

def c2vPtsZ : Array (ℤ × ℤ × ℤ × ℤ) := #[
  (Int.ofNat 0, Int.ofNat 0, Int.negSucc 0, Int.ofNat 1),
  (Int.ofNat 10243489250000000, Int.ofNat 0, Int.ofNat 13946134847762151, Int.ofNat 17303865152237849),
  (Int.negSucc 10243489249999999, Int.ofNat 0, Int.ofNat 13946134847762151, Int.ofNat 17303865152237849),
  (Int.ofNat 0, Int.ofNat 1073488162000000000, Int.ofNat 711905791511465439, Int.ofNat 1288094208488534561),
  (Int.ofNat 0, Int.negSucc 1073488161999999999, Int.ofNat 711905791511465439, Int.ofNat 1288094208488534561),
  (Int.ofNat 0, Int.ofNat 55254422750000000, Int.negSucc 33223819734971480, Int.ofNat 64473819734971481),
  (Int.ofNat 0, Int.negSucc 55254422749999999, Int.negSucc 33223819734971480, Int.ofNat 64473819734971481),
  (Int.ofNat 102920257400000000, Int.ofNat 58790128800000000, Int.negSucc 20244293138014220, Int.ofNat 120244293138014221),
  (Int.ofNat 102920257400000000, Int.negSucc 58790128799999999, Int.negSucc 20244293138014220, Int.ofNat 120244293138014221),
  (Int.negSucc 102920257399999999, Int.ofNat 58790128800000000, Int.negSucc 20244293138014220, Int.ofNat 120244293138014221),
  (Int.negSucc 102920257399999999, Int.negSucc 58790128799999999, Int.negSucc 20244293138014220, Int.ofNat 120244293138014221)
]

def uUpperZ : Array (Array ℤ) := #[
  #[Int.ofNat 0, Int.ofNat 26308831332644063, Int.ofNat 26308831332644063, Int.ofNat 28373559528288553, Int.ofNat 28373559528288553, Int.ofNat 50783390881260177, Int.ofNat 50783390881260177, Int.ofNat 38769236054185770, Int.ofNat 38769236054185770, Int.ofNat 38769236054185770, Int.ofNat 38769236054185770],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 42231374314757662, Int.ofNat 47476566077541098, Int.ofNat 47476566077541098, Int.ofNat 29718614401738364, Int.ofNat 29718614401738364, Int.ofNat 44578875459594653, Int.ofNat 44578875459594653, Int.ofNat 27587879281120850, Int.ofNat 27587879281120850],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 47476566077541098, Int.ofNat 47476566077541098, Int.ofNat 29718614401738364, Int.ofNat 29718614401738364, Int.ofNat 27587879281120850, Int.ofNat 27587879281120850, Int.ofNat 44578875459594653, Int.ofNat 44578875459594653],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 29997867095448571, Int.ofNat 46805540087100138, Int.ofNat 25006109779876398, Int.ofNat 42699654343256412, Int.ofNat 28862572696651414, Int.ofNat 42699654343256412, Int.ofNat 28862572696651414],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 25006109779876398, Int.ofNat 46805540087100138, Int.ofNat 28862572696651414, Int.ofNat 42699654343256412, Int.ofNat 28862572696651414, Int.ofNat 42699654343256412],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 29171338929140963, Int.ofNat 50290826857679609, Int.ofNat 30631042110443750, Int.ofNat 50290826857679609, Int.ofNat 30631042110443750],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 30631042110443750, Int.ofNat 50290826857679609, Int.ofNat 30631042110443750, Int.ofNat 50290826857679609],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 51132858352410270, Int.ofNat 29208120970462668, Int.ofNat 25362027038625442],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 25362027038625442, Int.ofNat 29208120970462668],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 51132858352410270],
  #[Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
]

def ptZ (i : Fin 11) : ℤ × ℤ × ℤ × ℤ := c2vPtsZ.getD i.val (0, 0, 1, 1)
def ptX (i : Fin 11) : ℤ := (ptZ i).1
def ptY (i : Fin 11) : ℤ := (ptZ i).2.1
def ptZc (i : Fin 11) : ℤ := (ptZ i).2.2.1
def ptD (i : Fin 11) : ℤ := (ptZ i).2.2.2
def uZ (i j : Fin 11) : ℤ := (uUpperZ.getD i.val #[]).getD j.val 0

def distNumSqZ (i j : Fin 11) : ℤ :=
  (ptX i * ptD j - ptX j * ptD i) ^ 2 +
  (ptY i * ptD j - ptY j * ptD i) ^ 2 +
  (ptZc i * ptD j - ptZc j * ptD i) ^ 2

theorem unit_ok : (List.finRange 11).all (fun i =>
    decide (0 < ptD i ∧ (ptX i) ^ 2 + (ptY i) ^ 2 + (ptZc i) ^ 2 = (ptD i) ^ 2)) = true := by
  decide +kernel

theorem pair_u_ok : (List.finRange 11).all (fun i =>
    (List.finRange 11).all (fun j =>
      if i < j then
        decide (0 < uZ i j ∧ S_inv ^ 2 * (ptD i) ^ 2 * (ptD j) ^ 2 ≤ (uZ i j) ^ 2 * distNumSqZ i j)
      else
        decide (uZ i j = 0))) = true := by
  decide +kernel

theorem energy_sum_ok :
    decide ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum) ≤
      ub_scaled) = true := by
  decide +kernel

noncomputable def c2vWitness (i : Fin 11) : R3 :=
  !₂[(ptX i : ℝ) / (ptD i : ℝ), (ptY i : ℝ) / (ptD i : ℝ), (ptZc i : ℝ) / (ptD i : ℝ)]

lemma ptD_pos_and_unit (i : Fin 11) :
    0 < ptD i ∧ (ptX i) ^ 2 + (ptY i) ^ 2 + (ptZc i) ^ 2 = (ptD i) ^ 2 := by
  have hall := unit_ok
  simp only [List.all_eq_true, decide_eq_true_eq] at hall
  exact hall i (List.mem_finRange i)

lemma c2vWitness_unit (i : Fin 11) : ‖c2vWitness i‖ = 1 := by
  obtain ⟨hdpos, hsq⟩ := ptD_pos_and_unit i
  have hdR : (0 : ℝ) < (ptD i : ℝ) := by exact_mod_cast hdpos
  have hdne : (ptD i : ℝ) ≠ 0 := ne_of_gt hdR
  have hsqR : ((ptX i : ℝ) ^ 2 + (ptY i : ℝ) ^ 2 + (ptZc i : ℝ) ^ 2) = (ptD i : ℝ) ^ 2 := by
    exact_mod_cast hsq
  have hnsq : ‖c2vWitness i‖ ^ 2 = 1 := by
    rw [norm_sq_R3_expand]
    change ((ptX i : ℝ) / (ptD i : ℝ)) ^ 2 + ((ptY i : ℝ) / (ptD i : ℝ)) ^ 2 + ((ptZc i : ℝ) / (ptD i : ℝ)) ^ 2 = 1
    field_simp [hdne]
    exact hsqR
  nlinarith [norm_nonneg (c2vWitness i)]

lemma c2vWitness_dist_num_sq (i j : Fin 11) :
    ‖c2vWitness i - c2vWitness j‖ ^ 2 * ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) =
      (distNumSqZ i j : ℝ) := by
  have hdi : (ptD i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (ptD_pos_and_unit i).1)
  have hdj : (ptD j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (ptD_pos_and_unit j).1)
  rw [norm_sq_R3_expand]
  change (((ptX i : ℝ) / (ptD i : ℝ) - (ptX j : ℝ) / (ptD j : ℝ)) ^ 2 +
          ((ptY i : ℝ) / (ptD i : ℝ) - (ptY j : ℝ) / (ptD j : ℝ)) ^ 2 +
          ((ptZc i : ℝ) / (ptD i : ℝ) - (ptZc j : ℝ) / (ptD j : ℝ)) ^ 2) *
         ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) = (distNumSqZ i j : ℝ)
  unfold distNumSqZ
  push_cast
  field_simp [hdi, hdj]

lemma pair_u_lt {i j : Fin 11} (hij : i < j) :
    0 < uZ i j ∧ S_inv ^ 2 * (ptD i) ^ 2 * (ptD j) ^ 2 ≤ (uZ i j) ^ 2 * distNumSqZ i j := by
  have hall := pair_u_ok
  simp only [List.all_eq_true] at hall
  have h1 := hall i (List.mem_finRange i) j (List.mem_finRange j)
  simpa [hij] using h1

lemma pair_u_not_lt {i j : Fin 11} (hnij : ¬ (i < j)) : uZ i j = 0 := by
  have hall := pair_u_ok
  simp only [List.all_eq_true] at hall
  have h1 := hall i (List.mem_finRange i) j (List.mem_finRange j)
  simpa [hnij] using h1

lemma pair_prod_ge {i j : Fin 11} (hij : i < j) :
    (S_inv : ℝ) ≤ (uZ i j : ℝ) * ‖c2vWitness i - c2vWitness j‖ := by
  obtain ⟨hupos, hule⟩ := pair_u_lt hij
  have hdi : (0 : ℝ) < (ptD i : ℝ) := by exact_mod_cast (ptD_pos_and_unit i).1
  have hdj : (0 : ℝ) < (ptD j : ℝ) := by exact_mod_cast (ptD_pos_and_unit j).1
  have hd2pos : (0 : ℝ) < (ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2 := by positivity
  have huleR : (S_inv : ℝ) ^ 2 * ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) ≤
      ((uZ i j : ℝ) ^ 2 * ‖c2vWitness i - c2vWitness j‖ ^ 2) * ((ptD i : ℝ) ^ 2 * (ptD j : ℝ) ^ 2) := by
    have hcast : ((S_inv ^ 2 * (ptD i) ^ 2 * (ptD j) ^ 2 : ℤ) : ℝ) ≤
        (((uZ i j) ^ 2 * distNumSqZ i j : ℤ) : ℝ) := by exact_mod_cast hule
    push_cast at hcast
    rw [← c2vWitness_dist_num_sq i j] at hcast
    linarith
  have hsq : (S_inv : ℝ) ^ 2 ≤ ((uZ i j : ℝ) * ‖c2vWitness i - c2vWitness j‖) ^ 2 := by
    have hcancel := le_of_mul_le_mul_right huleR hd2pos
    linarith
  have huR : (0 : ℝ) ≤ (uZ i j : ℝ) := le_of_lt (by exact_mod_cast hupos)
  have hprod_nn : (0 : ℝ) ≤ (uZ i j : ℝ) * ‖c2vWitness i - c2vWitness j‖ :=
    mul_nonneg huR (norm_nonneg _)
  have hSpos : (0 : ℝ) < (S_inv : ℝ) := by norm_num [S_inv]
  nlinarith

lemma c2vWitness_injective : Function.Injective c2vWitness := by
  intro i j heq
  have hSpos : (0 : ℝ) < (S_inv : ℝ) := by norm_num [S_inv]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hp := pair_prod_ge hij
    rw [heq, sub_self, norm_zero, mul_zero] at hp
    linarith
  · rfl
  · have hp := pair_prod_ge hji
    rw [heq, sub_self, norm_zero, mul_zero] at hp
    linarith

theorem c2vWitness_energy_le :
    coulombEnergy11 c2vWitness ≤ (2029822525409531 / 50000000000000 : ℝ) := by
  have hSpos : (0 : ℝ) < (S_inv : ℝ) := by norm_num [S_inv]
  have hpair : ∀ i : Fin 11, ∀ j ∈ Finset.Ioi i,
      ‖c2vWitness i - c2vWitness j‖⁻¹ ≤ (uZ i j : ℝ) / (S_inv : ℝ) := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hp := pair_prod_ge hij
    obtain ⟨hupos, _⟩ := pair_u_lt hij
    have huR : (0 : ℝ) < (uZ i j : ℝ) := by exact_mod_cast hupos
    have hdpos : (0 : ℝ) < ‖c2vWitness i - c2vWitness j‖ := by
      by_contra hle
      have hd0 : ‖c2vWitness i - c2vWitness j‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
      rw [hd0, mul_zero] at hp; linarith
    rw [inv_eq_one_div, div_le_div_iff₀ hdpos hSpos]
    linarith
  have hsum1 : coulombEnergy11 c2vWitness ≤ ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, (uZ i j : ℝ) / (S_inv : ℝ) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpair i j hj
  have hIoi : ∀ i : Fin 11,
      (∑ j ∈ Finset.Ioi i, (uZ i j : ℝ) / (S_inv : ℝ)) = ∑ j : Fin 11, (uZ i j : ℝ) / (S_inv : ℝ) := by
    intro i
    have hfilt : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp
    rw [hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · rfl
    · rw [pair_u_not_lt hij]; simp
  simp_rw [hIoi, ← Finset.sum_div] at hsum1
  have hfin_sum : (∑ i : Fin 11, ∑ j : Fin 11, (uZ i j : ℝ)) =
      ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum : ℤ) : ℝ) := by
    simp only [Fin.sum_univ_def, Int.cast_list_sum, List.map_map, Function.comp_def]
  rw [hfin_sum] at hsum1
  have hsumZ : (((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum) ≤
      ub_scaled := of_decide_eq_true energy_sum_ok
  have hsumR : ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum : ℤ) : ℝ) ≤
      (ub_scaled : ℝ) := by exact_mod_cast hsumZ
  have hdiv : ((((List.finRange 11).map fun i => ((List.finRange 11).map fun j => uZ i j).sum).sum : ℤ) : ℝ) / (S_inv : ℝ) ≤
      (ub_scaled : ℝ) / (S_inv : ℝ) := div_le_div_of_nonneg_right hsumR (le_of_lt hSpos)
  have hval : (ub_scaled : ℝ) / (S_inv : ℝ) = (2029822525409531 / 50000000000000 : ℝ) := by norm_num [ub_scaled, S_inv]
  linarith

end ThomsonN11.StageB.UpperBound
