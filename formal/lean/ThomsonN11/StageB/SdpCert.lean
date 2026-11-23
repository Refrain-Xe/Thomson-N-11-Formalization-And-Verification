import ThomsonN11.StageB.PolyKronFast
import ThomsonN11.StageB.SdpCertSosData
import ThomsonN11.StageB.SdpCertSosSliceM9
import ThomsonN11.StageB.SdpCertSosSliceM8
import ThomsonN11.StageB.SdpCertSosSliceM7
import ThomsonN11.StageB.SdpCertSosSliceM6
import ThomsonN11.StageB.SdpCertSosSliceM5
import ThomsonN11.StageB.SdpCertSosSliceM4
import ThomsonN11.StageB.SdpCertSosSliceM3
import ThomsonN11.StageB.SdpCertSosSliceM2
import ThomsonN11.StageB.SdpCertSosSliceM1
import ThomsonN11.StageB.SdpCertSosSlice0
import ThomsonN11.StageB.SdpCertSosSlice1
import ThomsonN11.StageB.SdpCertSosSlice2
import ThomsonN11.StageB.SdpCertSosSlice3
import ThomsonN11.StageB.SdpCertSosSlice4
import ThomsonN11.StageB.SdpCertSosSlice5
import ThomsonN11.StageB.SdpCertSosSlice6
import ThomsonN11.StageB.SdpCertSosSlice7
import ThomsonN11.StageB.SdpCertSosSlice8
import ThomsonN11.StageB.SdpCertSosSlice9

/-!
# Thomson N = 11 — Kernel-Verified 3-Point SDP Universal Lower Bound (`M=10, K=10`)

Proves that every 11-point configuration on the unit sphere has Coulomb energy
at least `2027773585218537 / 50000000000000 = 40.555471704371…`.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN11.StageB.SdpCert

open Finset ThomsonN11.StageB ThomsonN11.StageB.PolyKron ThomsonN11.StageB.PolyKronFast
open ThomsonN11.StageB.SdpCertHarmData ThomsonN11.StageB.SdpCertSosData
open scoped RealInnerProductSpace

private lemma l1_slices_ok :
    ∀ T ∈ ([-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℤ),
      l1CapFast * (max 1 T.natAbs) ^ 18 < 2 ^ (wForT T) := by
  have h1 : l1CapFast < 2 ^ 178 := l1_fast_ok
  have h2 : ∀ T ∈ ([-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] : List ℤ),
      2 ^ 178 * (max 1 T.natAbs) ^ 18 ≤ 2 ^ (wForT T) := by decide
  intro T hT
  have hm : 0 < (max 1 T.natAbs) ^ 18 := Nat.pow_pos (by omega)
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 hm) (h2 T hT)

private lemma peval_eq_sum_zipIdx (h : List ℤ) (x : ℝ) :
    peval h x = (h.zipIdx.map fun p => (p.1 : ℝ) * x ^ p.2).sum := by
  have hgen : ∀ (l : List ℤ) (k : ℕ),
      x ^ k * peval l x = ((l.zipIdx k).map fun p => (p.1 : ℝ) * x ^ p.2).sum := by
    intro l
    induction l with
    | nil => intro k; simp [peval]
    | cons a as ih =>
      intro k
      simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, peval]
      have h1 := ih (k + 1)
      rw [pow_succ] at h1
      linarith
  simpa using hgen h 0

private lemma peval_twoYH_aux (l : List (ℤ × ℕ)) (acc : List ℤ) (y : ℝ) :
    peval (l.foldl (fun a p => padd a (pscale (2 * p.1) (pmul [0, 1] (ppow [1, 0, -2] p.2)))) acc) y =
      peval acc y + (l.map fun p => (2 : ℝ) * y * ((p.1 : ℝ) * (1 - 2 * y ^ 2) ^ p.2)).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, peval_padd, peval_pscale,
      peval_pmul, peval_ppow]
    have h01 : peval [0, 1] y = y := by simp [peval]
    have h12 : peval [1, 0, -2] y = 1 - 2 * y ^ 2 := by simp [peval]; ring
    rw [h01, h12]; push_cast; ring

private lemma peval_twoYH (h : List ℤ) (y : ℝ) :
    peval (twoYH h) y = 2 * y * peval h (1 - 2 * y ^ 2) := by
  unfold twoYH
  rw [peval_twoYH_aux, peval_eq_sum_zipIdx h, show peval [] y = 0 from rfl, zero_add]
  have hpull : ∀ (l : List (ℤ × ℕ)),
      (l.map fun p => (2 : ℝ) * y * ((p.1 : ℝ) * (1 - 2 * y ^ 2) ^ p.2)).sum =
      2 * y * (l.map fun p => (p.1 : ℝ) * (1 - 2 * y ^ 2) ^ p.2).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  exact hpull _

private lemma HasPolyRep3.of_plain_deg {blk : CholPlainBlk} {dmp db B : ℕ}
    (hok : plainDegOk blk dmp db = true) (hD : dmp + (db + db) ≤ 18)
    (hB : blk.basis.toList.all (fun p => decide (l1Poly3 p ≤ B)) = true) :
    HasPolyRep3 18 18 18 (cholPlainL1Fast B blk) (cholPlainEv blk) := by
  simp only [plainDegOk, Bool.and_eq_true] at hok
  exact (HasPolyRep3.of_cholPlain blk hok.1 hok.2).widen hD hD hD (cholPlainL1_le_fast blk hB)

private lemma HasPolyRep3.of_std_deg {blk : CholStdBlk} {dmp db B1 B2 : ℕ}
    (hok : stdDegOk blk dmp db = true) (hD : dmp + (db + db) ≤ 18)
    (hB1 : blk.e1.toList.all (fun p => decide (l1Poly3 p ≤ B1)) = true)
    (hB2 : blk.e2.toList.all (fun p => decide (l1Poly3 p ≤ B2)) = true) :
    HasPolyRep3 18 18 18 (cholStdL1Fast B1 B2 blk) (cholStdEv blk) := by
  simp only [stdDegOk, Bool.and_eq_true] at hok
  exact (HasPolyRep3.of_cholStd blk hok.1.1 hok.1.2 hok.2).widen hD hD hD (cholStdL1_le_fast blk hB1 hB2)

private lemma harm_rep : HasPolyRep3 9 9 9 (harmListL1 harmBlks) (harmListEv harmBlks) :=
  HasPolyRep3.of_harmList harmBlks harm_deg_ok

private def g_int_ev (x : ℝ) : ℝ :=
  harmListEv harmBlks 1 x x + harmListEv harmBlks x 1 x + harmListEv harmBlks x x 1

private lemma g_rep_u : HasPolyRep3 18 18 18 (3 * harmListL1 harmBlks) (fun u _ _ => g_int_ev u) := by
  have h1 := harm_rep.diag_1uu
  have h2 := harm_rep.diag_u1u
  have h3 := harm_rep.diag_uu1
  have hsum := ((h1.add h2).add h3).widen (da' := 18) (db' := 18) (dc' := 18)
    (L' := 3 * harmListL1 harmBlks) (by omega) (by omega) (by omega) (by omega)
  exact hsum.congr (g := fun u _ _ => g_int_ev u) fun u _ _ => by unfold g_int_ev; ring

private def sosCap_ev (u v t : ℝ) : ℝ :=
  (sos_plain_s3.map fun b => cholPlainEv b u v t).sum +
  (sos_std_s3.map fun b => cholStdEv b u v t).sum +
  (sos_ulo.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum +
  (sos_uhi.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum

private lemma cast_foldl_plain2T (eu ev : ℕ) (T : ℤ) (blks : List CholPlainBlk)
    (hlen : blks.all (fun b => decide (b.basis.size ≤ 256)) = true) :
    ((blks.foldl (fun a b => a + cholPlainKev2T eu ev T b) 0 : ℤ) : ℝ) =
      (blks.map fun b => cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
  have haux : ∀ (l : List CholPlainBlk),
      l.all (fun b => decide (b.basis.size ≤ 256)) = true →
      ∀ (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKev2T eu ev T b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b => cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons b bs ih =>
      intro hl acc
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih hl.2]
      push_cast; rw [cast_cholPlainKev2T eu ev T b hl.1]; ring
  rw [haux blks hlen 0]; simp

private lemma cast_foldl_plain2T3 (eu ev : ℕ) (T : ℤ) (blks : List CholPlainBlk)
    (hlen : blks.all (fun b => decide (b.basis.size ≤ 256)) = true) :
    ((blks.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b
        + cholPlainKev2T_tuv eu ev T b) 0 : ℤ) : ℝ) =
      (blks.map fun b =>
        cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) +
        cholPlainEv b ((2 : ℝ) ^ ev) ((2 : ℝ) ^ eu) (T : ℝ) +
        cholPlainEv b (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev)).sum := by
  have haux : ∀ (l : List CholPlainBlk),
      l.all (fun b => decide (b.basis.size ≤ 256)) = true →
      ∀ (acc : ℤ),
      ((l.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b
          + cholPlainKev2T_tuv eu ev T b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b =>
          cholPlainEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ) +
          cholPlainEv b ((2 : ℝ) ^ ev) ((2 : ℝ) ^ eu) (T : ℝ) +
          cholPlainEv b (T : ℝ) ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev)).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons b bs ih =>
      intro hl acc
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih hl.2]
      push_cast
      rw [cast_cholPlainKev2T eu ev T b hl.1, cast_cholPlainKev2T ev eu T b hl.1,
        cast_cholPlainKev2T_tuv eu ev T b hl.1]; ring
  rw [haux blks hlen 0]; simp

private lemma cast_foldl_std2T (eu ev : ℕ) (T : ℤ) (blks : List CholStdBlk)
    (hlen : blks.all (fun b => decide (b.e1.size ≤ 256 ∧ b.e2.size ≤ 256)) = true) :
    ((blks.foldl (fun a b => a + cholStdKev2T eu ev T b) 0 : ℤ) : ℝ) =
      (blks.map fun b => cholStdEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
  have haux : ∀ (l : List CholStdBlk),
      l.all (fun b => decide (b.e1.size ≤ 256 ∧ b.e2.size ≤ 256)) = true →
      ∀ (acc : ℤ),
      ((l.foldl (fun a b => a + cholStdKev2T eu ev T b) acc : ℤ) : ℝ) =
        (acc : ℝ) + (l.map fun b => cholStdEv b ((2 : ℝ) ^ eu) ((2 : ℝ) ^ ev) (T : ℝ)).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons b bs ih =>
      intro hl acc
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih hl.2]
      push_cast; rw [cast_cholStdKev2T eu ev T b hl.1.1 hl.1.2]; ring
  rw [haux blks hlen 0]; simp

private lemma id_slack (u v t : ℝ) :
    660 * (peval H_int u + peval H_int v + peval H_int t)
      - 36 * (e_int : ℝ) - 198 * harmListEv harmBlks 1 1 1
      - 660 * (g_int_ev u + g_int_ev v + g_int_ev t)
      - 5940 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u) =
    sosCap_ev u v t + ev3 res_slack_int u v t := by
  let f : ℝ → ℝ → ℝ → ℝ := fun u v t =>
    (660 * (peval H_int u + peval H_int v + peval H_int t)
      - 36 * (e_int : ℝ) - 198 * harmListEv harmBlks 1 1 1
      - 660 * (g_int_ev u + g_int_ev v + g_int_ev t)
      - 5940 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u))
    - (sosCap_ev u v t + ev3 res_slack_int u v t)
  suffices h0 : f u v t = 0 by dsimp only [f] at h0; linarith
  have hd := sos_exact_deg_ok
  have hbl := basis_l1_ok
  have hH_u := (HasPolyRep3.of_peval_u_tight H_int).widen (da' := 18) (db' := 18) (dc' := 18)
    (by decide) (by omega) (by omega) (le_refl _)
  have hH3 : HasPolyRep3 18 18 18 (660 * (l1List H_int + l1List H_int + l1List H_int))
      (fun u v t => 660 * (peval H_int u + peval H_int v + peval H_int t)) := by
    have h := (hH_u.add hH_u.perm_vut).add hH_u.perm_tuv
    simpa [Int.natAbs_natCast] using h.smul_int 660
  have he : HasPolyRep3 18 18 18 (36 * e_int.natAbs) (fun _ _ _ => 36 * (e_int : ℝ)) := by
    have h := (HasPolyRep3.const (36 * e_int)).widen (da' := 18) (db' := 18) (dc' := 18)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    exact h.congr fun _ _ _ => by push_cast; ring
  have hs111 : HasPolyRep3 18 18 18 (198 * (harmListKevShift 0 0 0 harmBlks).natAbs)
      (fun _ _ _ => 198 * harmListEv harmBlks 1 1 1) := by
    have h := (HasPolyRep3.const (198 * harmListKevShift 0 0 0 harmBlks)).widen (da' := 18) (db' := 18) (dc' := 18)
      (by omega) (by omega) (by omega) (by rw [Int.natAbs_mul])
    refine h.congr fun _ _ _ => ?_
    push_cast; rw [cast_harmListKevShift]; simp only [pow_zero]
  have hg3 : HasPolyRep3 18 18 18
      (660 * (3 * harmListL1 harmBlks + 3 * harmListL1 harmBlks + 3 * harmListL1 harmBlks))
      (fun u v t => 660 * (g_int_ev u + g_int_ev v + g_int_ev t)) := by
    have h := (g_rep_u.add g_rep_u.perm_vut).add g_rep_u.perm_tuv
    simpa [Int.natAbs_natCast] using h.smul_int 660
  have hs3 : HasPolyRep3 18 18 18 (5940 * (3 * harmListL1 harmBlks))
      (fun u v t => 5940 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u)) := by
    have h1 := harm_rep.widen (da' := 18) (db' := 18) (dc' := 18) (by omega) (by omega) (by omega) (le_refl _)
    have h2 := h1.perm_utv
    have h3 := h1.perm_vtu
    have h123 := ((h1.add h2).add h3).widen (L' := 3 * harmListL1 harmBlks)
      (le_refl _) (le_refl _) (le_refl _) (by omega)
    simpa [Int.natAbs_natCast] using h123.smul_int 5940
  have hrep_p : HasPolyRep3 18 18 18 (sos_plain_s3.foldl (fun a b => a + cholPlainL1Fast 6 b) 0)
      (fun u v t => (sos_plain_s3.map fun b => cholPlainEv b u v t).sum) := by
    have hp := hbl.1
    simp only [sos_plain_s3, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hp
    have b1 := HasPolyRep3.of_plain_deg hd.1 (by omega) hp.1
    have b2 := HasPolyRep3.of_plain_deg hd.2.1 (by omega) hp.2.1
    have b3 := HasPolyRep3.of_plain_deg hd.2.2.1 (by omega) hp.2.2.1
    have b4 := HasPolyRep3.of_plain_deg hd.2.2.2.1 (by omega) hp.2.2.2
    have hall := ((b1.add b2).add b3).add b4
    refine hall.widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_plain_s3, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_plain_s3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; ring
  have hrep_std : HasPolyRep3 18 18 18 (sos_std_s3.foldl (fun a b => a + cholStdL1Fast 8 4 b) 0)
      (fun u v t => (sos_std_s3.map fun b => cholStdEv b u v t).sum) := by
    have hs := hbl.2.1
    simp only [sos_std_s3, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hs
    have b1 := HasPolyRep3.of_std_deg hd.2.2.2.2.1 (by omega) hs.1.1 hs.1.2
    have b2 := HasPolyRep3.of_std_deg hd.2.2.2.2.2.1 (by omega) hs.2.1 hs.2.2
    refine (b1.add b2).widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_std_s3, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_std_s3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hrep_ulo : HasPolyRep3 18 18 18 (3 * sos_ulo.foldl (fun a b => a + cholPlainL1Fast 2 b) 0)
      (fun u v t => (sos_ulo.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum) := by
    have hu := hbl.2.2.1
    simp only [sos_ulo, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hu
    have b1 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.1 (by omega) hu.1
    have b2 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.2.1 (by omega) hu.2
    have c1 := (b1.add b1.perm_vut).add b1.perm_tuv
    have c2 := (b2.add b2.perm_vut).add b2.perm_tuv
    refine (c1.add c2).widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_ulo, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_ulo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hrep_uhi : HasPolyRep3 18 18 18 (3 * sos_uhi.foldl (fun a b => a + cholPlainL1Fast 2 b) 0)
      (fun u v t => (sos_uhi.map fun b => cholPlainEv b u v t + cholPlainEv b v u t + cholPlainEv b t u v).sum) := by
    have hu := hbl.2.2.2
    simp only [sos_uhi, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hu
    have b1 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.2.2.1 (by omega) hu.1
    have b2 := HasPolyRep3.of_plain_deg hd.2.2.2.2.2.2.2.2.2 (by omega) hu.2
    have c1 := (b1.add b1.perm_vut).add b1.perm_tuv
    have c2 := (b2.add b2.perm_vut).add b2.perm_tuv
    refine (c1.add c2).widen (le_refl _) (le_refl _) (le_refl _)
      (by simp only [sos_uhi, List.foldl_cons, List.foldl_nil, zero_add]; omega) |>.congr fun u v t => ?_
    simp only [sos_uhi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hrep_res : HasPolyRep3 18 18 18 (l1Poly3 res_slack_int) (ev3 res_slack_int) :=
    HasPolyRep3.of_poly3 res_slack_int res_deg_ok
  have hrep_f : HasPolyRep3 18 18 18 l1CapFast f := by
    have hall := ((((hH3.sub he).sub hs111).sub hg3).sub hs3).sub
      ((((hrep_p.add hrep_std).add hrep_ulo).add hrep_uhi).add hrep_res)
    refine hall.widen (le_refl _) (le_refl _) (le_refl _) (by unfold l1CapFast; omega) |>.congr fun a b c => ?_
    dsimp only [f, sosCap_ev]
  have hval_of_check : ∀ T : ℤ, checkKronCapAtT (wForT T) T = true →
      f ((2 : ℝ) ^ (wForT T)) ((2 : ℝ) ^ (wForT T * D2_kron)) (T : ℝ) = 0 := by
    intro T hk
    unfold checkKronCapAtT at hk
    simp only [beq_iff_eq] at hk
    set eu := wForT T
    set ev := wForT T * D2_kron
    have hcast :
      (((660 * (pevalZ H_int ((Nat.shiftLeft 1 eu : ℕ) : ℤ)
          + pevalZ H_int ((Nat.shiftLeft 1 ev : ℕ) : ℤ)
          + pevalZ H_int T)
        - 36 * e_int - 198 * harmListKevShift 0 0 0 harmBlks
        - 660 * ((harmListKevShift 0 eu eu harmBlks + harmListKevShift eu 0 eu harmBlks + harmListKevShift eu eu 0 harmBlks)
          + (harmListKevShift 0 ev ev harmBlks + harmListKevShift ev 0 ev harmBlks + harmListKevShift ev ev 0 harmBlks)
          + (harmListEvZ 1 T T harmBlks + harmListEvZ T 1 T harmBlks + harmListEvZ T T 1 harmBlks))
        - 5940 * (harmListKev2T eu ev T harmBlks + harmListKev2T_utv eu ev T harmBlks + harmListKev2T_utv ev eu T harmBlks) : ℤ) : ℝ)) =
      (((sos_plain_s3.foldl (fun a b => a + cholPlainKev2T eu ev T b) 0
        + sos_std_s3.foldl (fun a b => a + cholStdKev2T eu ev T b) 0
        + sos_ulo.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b + cholPlainKev2T_tuv eu ev T b) 0
        + sos_uhi.foldl (fun a b => a + cholPlainKev2T eu ev T b + cholPlainKev2T ev eu T b + cholPlainKev2T_tuv eu ev T b) 0
        + kev2T eu ev T res_slack_int : ℤ) : ℝ)) := by
      exact_mod_cast hk
    push_cast at hcast
    rw [cast_pevalZ, cast_pevalZ, cast_pevalZ,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift, cast_harmListKevShift, cast_harmListKevShift,
      cast_harmListKevShift,
      cast_harmListEvZ, cast_harmListEvZ, cast_harmListEvZ,
      cast_harmListKev2T, cast_harmListKev2T_utv, cast_harmListKev2T_utv,
      cast_foldl_plain2T eu ev T sos_plain_s3 basis_len_ok.1,
      cast_foldl_std2T eu ev T sos_std_s3 basis_len_ok.2.1,
      cast_foldl_plain2T3 eu ev T sos_ulo basis_len_ok.2.2.1,
      cast_foldl_plain2T3 eu ev T sos_uhi basis_len_ok.2.2.2,
      cast_kev2T] at hcast
    push_cast at hcast
    simp only [nat_shiftLeft_one_cast_real, pow_zero] at hcast
    dsimp only [f, sosCap_ev, g_int_ev, eu, ev] at hcast ⊢
    linarith
  let s : Finset ℤ := Finset.Icc (-9) 9
  have hs : 18 < s.card := by decide
  have hw_pos : ∀ t₀ ∈ s, 1 ≤ wForT t₀ := by
    intro t₀ ht₀; simp only [s, Finset.mem_Icc] at ht₀; obtain ⟨hlo, hhi⟩ := ht₀; interval_cases t₀ <;> decide
  have hL : ∀ t₀ ∈ s, l1CapFast * (max 1 t₀.natAbs) ^ 18 < 2 ^ (wForT t₀) := by
    intro t₀ ht₀
    apply l1_slices_ok t₀
    simp only [s, Finset.mem_Icc] at ht₀
    obtain ⟨hlo, hhi⟩ := ht₀
    interval_cases t₀ <;> decide
  have hzero : ∀ t₀ ∈ s, f ((2 : ℝ) ^ (wForT t₀)) ((2 : ℝ) ^ (wForT t₀ * D2_kron)) (t₀ : ℝ) = 0 := by
    intro t₀ ht₀
    apply hval_of_check t₀
    simp only [s, Finset.mem_Icc] at ht₀
    obtain ⟨hlo, hhi⟩ := ht₀
    interval_cases t₀
    · exact SdpCertSosSliceM9.kron_t_m9
    · exact SdpCertSosSliceM8.kron_t_m8
    · exact SdpCertSosSliceM7.kron_t_m7
    · exact SdpCertSosSliceM6.kron_t_m6
    · exact SdpCertSosSliceM5.kron_t_m5
    · exact SdpCertSosSliceM4.kron_t_m4
    · exact SdpCertSosSliceM3.kron_t_m3
    · exact SdpCertSosSliceM2.kron_t_m2
    · exact SdpCertSosSliceM1.kron_t_m1
    · exact SdpCertSosSlice0.kron_t_0
    · exact SdpCertSosSlice1.kron_t_1
    · exact SdpCertSosSlice2.kron_t_2
    · exact SdpCertSosSlice3.kron_t_3
    · exact SdpCertSosSlice4.kron_t_4
    · exact SdpCertSosSlice5.kron_t_5
    · exact SdpCertSosSlice6.kron_t_6
    · exact SdpCertSosSlice7.kron_t_7
    · exact SdpCertSosSlice8.kron_t_8
    · exact SdpCertSosSlice9.kron_t_9
  exact eq_zero_of_kev2_slices (da := 18) (db := 18) (dc := 18) (D := D2_kron)
    (by decide) (by decide) (by decide) hrep_f s hs wForT hw_pos hL hzero u v t

private lemma sosCap_ev_nonneg {u v t : ℝ} (hu_lo : -1 ≤ u) (hu_hi : u ≤ 1)
    (hv_lo : -1 ≤ v) (hv_hi : v ≤ 1) (ht_lo : -1 ≤ t) (ht_hi : t ≤ 1)
    (hd : 0 ≤ detG u v t) : 0 ≤ sosCap_ev u v t := by
  have h1 : 0 ≤ ev3 blk_SOS_1_triv.mp u v t := by simp [blk_SOS_1_triv, ev3]
  have h2 : 0 ≤ ev3 blk_SOS_1_sign.mp u v t := by simp [blk_SOS_1_sign, ev3]
  have h3 : 0 ≤ ev3 blk_SOS_detG_triv.mp u v t := by simp [blk_SOS_detG_triv, ev3]; unfold detG at hd; linarith
  have h4 : 0 ≤ ev3 blk_SOS_detG_sign.mp u v t := by simp [blk_SOS_detG_sign, ev3]; unfold detG at hd; linarith
  have h5 : 0 ≤ ev3 blk_SOS_1_std.mp u v t := by simp [blk_SOS_1_std, ev3]
  have h6 : 0 ≤ ev3 blk_SOS_detG_std.mp u v t := by simp [blk_SOS_detG_std, ev3]; unfold detG at hd; linarith
  have h7a : 0 ≤ ev3 blk_SOS_ulo_even.mp u v t := by simp [blk_SOS_ulo_even, ev3]; linarith
  have h7b : 0 ≤ ev3 blk_SOS_ulo_even.mp v u t := by simp [blk_SOS_ulo_even, ev3]; linarith
  have h7c : 0 ≤ ev3 blk_SOS_ulo_even.mp t u v := by simp [blk_SOS_ulo_even, ev3]; linarith
  have h8a : 0 ≤ ev3 blk_SOS_ulo_odd.mp u v t := by simp [blk_SOS_ulo_odd, ev3]; linarith
  have h8b : 0 ≤ ev3 blk_SOS_ulo_odd.mp v u t := by simp [blk_SOS_ulo_odd, ev3]; linarith
  have h8c : 0 ≤ ev3 blk_SOS_ulo_odd.mp t u v := by simp [blk_SOS_ulo_odd, ev3]; linarith
  have h9a : 0 ≤ ev3 blk_SOS_uhi_even.mp u v t := by simp [blk_SOS_uhi_even, ev3]; linarith
  have h9b : 0 ≤ ev3 blk_SOS_uhi_even.mp v u t := by simp [blk_SOS_uhi_even, ev3]; linarith
  have h9c : 0 ≤ ev3 blk_SOS_uhi_even.mp t u v := by simp [blk_SOS_uhi_even, ev3]; linarith
  have h10a : 0 ≤ ev3 blk_SOS_uhi_odd.mp u v t := by simp [blk_SOS_uhi_odd, ev3]; linarith
  have h10b : 0 ≤ ev3 blk_SOS_uhi_odd.mp v u t := by simp [blk_SOS_uhi_odd, ev3]; linarith
  have h10c : 0 ≤ ev3 blk_SOS_uhi_odd.mp t u v := by simp [blk_SOS_uhi_odd, ev3]; linarith
  unfold sosCap_ev
  simp only [sos_plain_s3, sos_std_s3, sos_ulo, sos_uhi, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  linarith [cholPlainEv_nonneg blk_SOS_1_triv h1, cholPlainEv_nonneg blk_SOS_1_sign h2,
    cholPlainEv_nonneg blk_SOS_detG_triv h3, cholPlainEv_nonneg blk_SOS_detG_sign h4,
    cholStdEv_nonneg blk_SOS_1_std h5, cholStdEv_nonneg blk_SOS_detG_std h6,
    cholPlainEv_nonneg blk_SOS_ulo_even h7a, cholPlainEv_nonneg blk_SOS_ulo_even h7b,
    cholPlainEv_nonneg blk_SOS_ulo_even h7c, cholPlainEv_nonneg blk_SOS_ulo_odd h8a,
    cholPlainEv_nonneg blk_SOS_ulo_odd h8b, cholPlainEv_nonneg blk_SOS_ulo_odd h8c,
    cholPlainEv_nonneg blk_SOS_uhi_even h9a, cholPlainEv_nonneg blk_SOS_uhi_even h9b,
    cholPlainEv_nonneg blk_SOS_uhi_even h9c, cholPlainEv_nonneg blk_SOS_uhi_odd h10a,
    cholPlainEv_nonneg blk_SOS_uhi_odd h10b, cholPlainEv_nonneg blk_SOS_uhi_odd h10c]

private lemma S2_pos : (0 : ℝ) < (S2 : ℝ) := by norm_num [S2]

private lemma minorCap_bound {t : ℝ} (ht_lo : -1 ≤ t) (ht_lt : t < 1) :
    peval H_int t / (S2 : ℝ) ≤ (1 + (l1List res_y_int : ℝ) / (S2 : ℝ)) * phi t := by
  set y : ℝ := Real.sqrt ((1 - t) / 2)
  have hy_sq : y ^ 2 = (1 - t) / 2 := Real.sq_sqrt (by linarith)
  have hy_pos : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hy_le1 : y ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have h1m2y : 1 - 2 * y ^ 2 = t := by linarith
  have hphi : phi t = (2 * y)⁻¹ := by
    unfold phi
    have h2 : 2 - 2 * t = (2 * y) ^ 2 := by linarith
    rw [h2, Real.sqrt_sq (by linarith)]
  have hid := peval_eq_zero_of_all _ minor_ok y
  simp only [peval_padd, peval_pmul, peval_pneg, peval_chol1DPoly, peval_twoYH] at hid
  rw [h1m2y] at hid
  have h01 : peval [0, 1] y = y := by simp only [peval]; push_cast; ring
  have h02 : peval [1, 0, -1] y = 1 - y ^ 2 := by simp only [peval]; push_cast; ring
  have h03 : peval [0, 1, 0, -1] y = y * (1 - y ^ 2) := by simp only [peval]; push_cast; ring
  have hS : peval [-S2] y = -(S2 : ℝ) := by simp only [peval]; push_cast; ring
  rw [h01, h02, h03, hS] at hid
  have h1my2 : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hnn0 : 0 ≤ chol1DEv sig_0 y := chol1DEv_nonneg _ _
  have hnn1 : 0 ≤ y * chol1DEv sig_1 y := mul_nonneg hy_pos.le (chol1DEv_nonneg _ _)
  have hnn2 : 0 ≤ (1 - y ^ 2) * chol1DEv sig_2 y := mul_nonneg h1my2 (chol1DEv_nonneg _ _)
  have hnn3 : 0 ≤ y * (1 - y ^ 2) * chol1DEv sig_3 y :=
    mul_nonneg (mul_nonneg hy_pos.le h1my2) (chol1DEv_nonneg _ _)
  have hres : peval res_y_int y ≤ (l1List res_y_int : ℝ) :=
    (le_abs_self _).trans (abs_peval_le_l1List res_y_int hy_pos.le hy_le1)
  have hkey : 2 * y * peval H_int t - (S2 : ℝ) ≤ (l1List res_y_int : ℝ) := by linarith
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  rw [hphi, div_le_iff₀ hS2]
  have h2y_pos : (0 : ℝ) < 2 * y := by linarith
  have hmul : peval H_int t * (2 * y) ≤ (1 + (l1List res_y_int : ℝ) / (S2 : ℝ)) * (S2 : ℝ) := by
    have hdiv : (l1List res_y_int : ℝ) / (S2 : ℝ) * (S2 : ℝ) = (l1List res_y_int : ℝ) :=
      div_mul_cancel₀ _ hS2.ne'
    linarith
  have := (le_mul_inv_iff₀ h2y_pos).mpr hmul
  linarith

theorem global_sdp_lower_bound (x : Fin 11 → R3) (hu : ∀ i, ‖x i‖ = 1) (hinj : Function.Injective x) :
    ((bound_num : ℝ) / (bound_den : ℝ)) ≤ coulombEnergy11 x := by
  let Tmat : Fin 11 → Fin 11 → ℝ := fun i j => ⟪x i, x j⟫
  have ht_diag : ∀ i : Fin 11, Tmat i i = 1 := fun i => by
    dsimp [Tmat]; rw [real_inner_self_eq_norm_sq, hu i]; norm_num
  have ht_sym : ∀ i j : Fin 11, Tmat i j = Tmat j i := fun i j => real_inner_comm _ _
  let H : ℝ → ℝ := fun t => peval H_int t / (S2 : ℝ)
  let s : ℝ → ℝ → ℝ → ℝ := fun u v t => harmListEv harmBlks u v t / (S2 : ℝ)
  let e_val : ℝ := (e_int : ℝ) / (S2 : ℝ)
  have hs_sym : ∀ u v t, s u v t = s v u t := fun u v t => by
    dsimp [s]; rw [harmListEv_symm]
  have hass := cap_assembly_11 Tmat ht_diag ht_sym H e_val s
  have hS2 : (0 : ℝ) < (S2 : ℝ) := S2_pos
  have h_harm_nn : 0 ≤ ∑ i : Fin 11, ∑ j : Fin 11, ∑ l : Fin 11, s (Tmat i j) (Tmat i l) (Tmat j l) := by
    have h1 := sum_harmListEv_nonneg (S := Finset.univ) harmBlks x hu
    have heq : (∑ i : Fin 11, ∑ j : Fin 11, ∑ l : Fin 11, s (Tmat i j) (Tmat i l) (Tmat j l)) =
        (∑ i ∈ (Finset.univ : Finset (Fin 11)), ∑ j : Fin 11, ∑ l : Fin 11,
          harmListEv harmBlks ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) / (S2 : ℝ) := by
      dsimp [s, Tmat]; simp only [← Finset.sum_div]
    rw [heq]; exact div_nonneg h1 hS2.le
  let g : ℝ → ℝ := fun u => s 1 u u + s u 1 u + s u u 1
  let slack : ℝ → ℝ → ℝ → ℝ := fun u v w =>
    (H u + H v + H w) / 3 - e_val / 55 - 9 * sym3 s u v w - (g u + g v + g w) / 3 - s 1 1 1 / 10
  have hslack_lb : ∀ i : Fin 11, ∀ j ∈ Finset.Ioi i, ∀ l ∈ Finset.Ioi j,
      -((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ))) ≤ slack (Tmat i j) (Tmat i l) (Tmat j l) := by
    intro i j hj l hl
    set u := Tmat i j; set v := Tmat i l; set t := Tmat j l
    have hu_lo : -1 ≤ u := neg_one_le_inner_unit (hu i) (hu j)
    have hu_hi : u ≤ 1 := inner_le_one_unit (hu i) (hu j)
    have hv_lo : -1 ≤ v := neg_one_le_inner_unit (hu i) (hu l)
    have hv_hi : v ≤ 1 := inner_le_one_unit (hu i) (hu l)
    have ht_lo : -1 ≤ t := neg_one_le_inner_unit (hu j) (hu l)
    have ht_hi : t ≤ 1 := inner_le_one_unit (hu j) (hu l)
    have hdet : 0 ≤ detG u v t := detG_nonneg_of_unit (hu i) (hu j) (hu l)
    have hsos := sosCap_ev_nonneg hu_lo hu_hi hv_lo hv_hi ht_lo ht_hi hdet
    have hres : |ev3 res_slack_int u v t| ≤ (l1Poly3 res_slack_int : ℝ) :=
      abs_ev3_le_l1Poly3 res_slack_int (abs_le.mpr ⟨hu_lo, hu_hi⟩) (abs_le.mpr ⟨hv_lo, hv_hi⟩) (abs_le.mpr ⟨ht_lo, ht_hi⟩)
    have hres_lo : -(l1Poly3 res_slack_int : ℝ) ≤ ev3 res_slack_int u v t := (abs_le.mp hres).1
    have hid := id_slack u v t
    have hsym3 : 9 * sym3 s u v t = 3 * (harmListEv harmBlks u v t + harmListEv harmBlks u t v + harmListEv harmBlks v t u) / (S2 : ℝ) := by
      unfold sym3
      rw [hs_sym v u t, hs_sym t u v, hs_sym t v u]
      dsimp [s]; ring
    have hsc : 1980 * (S2 : ℝ) * slack u v t = sosCap_ev u v t + ev3 res_slack_int u v t := by
      dsimp [slack, H, e_val, g]
      rw [hsym3]
      dsimp [s, g_int_ev] at hid ⊢
      have hS2ne : (S2 : ℝ) ≠ 0 := hS2.ne'
      generalize ev3 res_slack_int u v t = R_ev at hid ⊢
      field_simp
      linarith
    have hpos1980 : (0 : ℝ) < 1980 * (S2 : ℝ) := by positivity
    have h1 : -(l1Poly3 res_slack_int : ℝ) ≤ slack u v t * (1980 * (S2 : ℝ)) := by
      have hcomm : slack u v t * (1980 * (S2 : ℝ)) = 1980 * (S2 : ℝ) * slack u v t := by ring
      linarith
    have h2 : (-(l1Poly3 res_slack_int : ℝ)) / (1980 * (S2 : ℝ)) ≤ slack u v t :=
      (div_le_iff₀ hpos1980).mpr h1
    have hnd : -((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ))) =
        (-(l1Poly3 res_slack_int : ℝ)) / (1980 * (S2 : ℝ)) := by ring
    linarith
  have htrip_card : sumTriples11 (fun _ _ _ => (1 : ℝ)) = 165 := by
    have hc : (∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, (Finset.Ioi j).card : ℕ) = 165 := by decide
    unfold sumTriples11
    simpa [Finset.sum_const] using congrArg (Nat.cast (R := ℝ)) hc
  have htrip_lb : -(55 * ((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ)))) ≤
      (3 / 9 : ℝ) * sumTriples11 (fun i j l => slack (Tmat i j) (Tmat i l) (Tmat j l)) := by
    have hsum : sumTriples11 (fun _ _ _ => -((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ)))) ≤
        sumTriples11 (fun i j l => slack (Tmat i j) (Tmat i l) (Tmat j l)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l hl => hslack_lb i j hj l hl
    have hconst : sumTriples11 (fun _ _ _ => -((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ)))) =
        -((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ))) * sumTriples11 (fun _ _ _ => (1 : ℝ)) := by
      unfold sumTriples11; simp only [Finset.mul_sum, mul_one]
    rw [hconst, htrip_card] at hsum
    linarith
  have hsumH_lb : e_val - 55 * ((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ))) ≤
      sumPairs11 (fun i j => H (Tmat i j)) := by
    dsimp only [g, slack] at htrip_lb
    linarith [hass, h_harm_nn, htrip_lb]
  have hpair_ub : sumPairs11 (fun i j => H (Tmat i j)) ≤
      (1 + (l1List res_y_int : ℝ) / (S2 : ℝ)) * coulombEnergy11 x := by
    have hpw : ∀ i : Fin 11, ∀ j ∈ Finset.Ioi i,
        H (Tmat i j) ≤ (1 + (l1List res_y_int : ℝ) / (S2 : ℝ)) * ‖x i - x j‖⁻¹ := by
      intro i j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hne : x i ≠ x j := fun he => (ne_of_lt hij) (hinj he)
      rw [inv_norm_eq_phi (hu i) (hu j)]
      exact minorCap_bound (neg_one_le_inner_unit (hu i) (hu j)) (inner_lt_one_of_ne_unit (hu i) (hu j) hne)
    unfold sumPairs11 coulombEnergy11
    calc ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, H (Tmat i j)
        ≤ ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, (1 + (l1List res_y_int : ℝ) / (S2 : ℝ)) * ‖x i - x j‖⁻¹ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpw i j hj
      _ = (1 + (l1List res_y_int : ℝ) / (S2 : ℝ)) * ∑ i : Fin 11, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ := by
          simp only [← Finset.mul_sum]
  have hbnd : ((bound_num * 36 * (S2 + (l1List res_y_int : ℤ)) : ℤ) : ℝ) ≤
      ((bound_den * (36 * e_int - (l1Poly3 res_slack_int : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast bound_ok
  push_cast at hbnd
  have hden_pos : (0 : ℝ) < (bound_den : ℝ) := by norm_num [bound_den]
  have hchain : (36 * (e_int : ℝ) - (l1Poly3 res_slack_int : ℝ)) / (36 * (S2 : ℝ)) ≤
      ((S2 : ℝ) + (l1List res_y_int : ℝ)) / (S2 : ℝ) * coulombEnergy11 x := by
    have hL : (36 * (e_int : ℝ) - (l1Poly3 res_slack_int : ℝ)) / (36 * (S2 : ℝ)) =
        e_val - 55 * ((l1Poly3 res_slack_int : ℝ) / (1980 * (S2 : ℝ))) := by
      dsimp [e_val]
      have hSne : (S2 : ℝ) ≠ 0 := hS2.ne'
      generalize (l1Poly3 res_slack_int : ℝ) = R, (e_int : ℝ) = E, (S2 : ℝ) = S at hSne ⊢
      field_simp
      ring
    have hR : ((S2 : ℝ) + (l1List res_y_int : ℝ)) / (S2 : ℝ) =
        1 + (l1List res_y_int : ℝ) / (S2 : ℝ) := by
      rw [add_div, div_self hS2.ne']
    rw [hL, hR]; linarith [hsumH_lb, hpair_ub]
  rw [div_le_iff₀ hden_pos]
  have hmul36 : 36 * (S2 : ℝ) > 0 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hchain hmul36.le
  have h1L : 36 * (S2 : ℝ) * ((36 * (e_int : ℝ) - (l1Poly3 res_slack_int : ℝ)) / (36 * (S2 : ℝ))) =
      36 * (e_int : ℝ) - (l1Poly3 res_slack_int : ℝ) :=
    mul_div_cancel₀ _ hmul36.ne'
  have h1R : 36 * (S2 : ℝ) * (((S2 : ℝ) + (l1List res_y_int : ℝ)) / (S2 : ℝ) * coulombEnergy11 x) =
      36 * ((S2 : ℝ) + (l1List res_y_int : ℝ)) * coulombEnergy11 x := by
    have hSne : (S2 : ℝ) ≠ 0 := hS2.ne'
    generalize (l1List res_y_int : ℝ) = Ry, (S2 : ℝ) = S, coulombEnergy11 x = EC at hSne ⊢
    field_simp
  rw [h1L, h1R] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hden_pos.le
  have h3 : (bound_num : ℝ) * (36 * ((S2 : ℝ) + (l1List res_y_int : ℝ))) ≤
      (coulombEnergy11 x * (bound_den : ℝ)) * (36 * ((S2 : ℝ) + (l1List res_y_int : ℝ))) := by
    have hbnd2 := hbnd.trans h2
    generalize (l1List res_y_int : ℝ) = Ry, (S2 : ℝ) = S,
      (bound_num : ℝ) = BN, (bound_den : ℝ) = BD, coulombEnergy11 x = EC at hbnd2 ⊢
    convert hbnd2 using 1 <;> ring
  have hpos_fac : (0 : ℝ) < 36 * ((S2 : ℝ) + (l1List res_y_int : ℝ)) := by positivity
  exact le_of_mul_le_mul_right h3 hpos_fac

end ThomsonN11.StageB.SdpCert
