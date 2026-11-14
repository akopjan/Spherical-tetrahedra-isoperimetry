module

public import SphericalTetrahedron.ManuscriptGramChart
public import SphericalTetrahedron.ManuscriptMeasureBridge
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

@[expose] public section

/-!
# Gram-Chart Area Formula and Exact Area Differential

This module expresses `SphericalTetrahedron.stdArea` on `gramOpen` as `stdAreaGram`,
proves that `stdAreaGram` is `C¹` (`HasStrictFDerivAt`) on `gramOpen`, and derives
the manuscript's exact coordinate gradient formula in terms of the dual heights
and dual edge cosines.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Spherical face-angle contribution as a function of the three edge cosines
`(u, v, w) = (⟪n_r, n_a⟫, ⟪n_r, n_b⟫, ⟪n_a, n_b⟫)` incident to the corner opposite the fourth face. -/
def faceLinkAngle (u v w : ℝ) : ℝ :=
  Real.arccos ((u * v - w) / Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2)))

/-- Sum of the three `faceAngle`s at one vertex of the tetrahedron. -/
def vertexLinkSum (u v w : ℝ) : ℝ :=
  faceLinkAngle u v w + faceLinkAngle v w u + faceLinkAngle w u v

theorem faceLinkAngle_comm (u v w : ℝ) :
    faceLinkAngle u v w = faceLinkAngle v u w := by
  unfold faceLinkAngle
  rw [mul_comm u v, mul_comm (1 - u ^ 2) (1 - v ^ 2)]

/-- Total standard face area expressed purely on the six-dimensional Gram chart. -/
def stdAreaGram (x : Fin 6 → ℝ) : ℝ :=
  vertexLinkSum (x 3) (x 4) (x 5) +
    vertexLinkSum (x 1) (x 2) (x 5) +
    vertexLinkSum (x 0) (x 2) (x 4) +
    vertexLinkSum (x 0) (x 1) (x 3) - 4 * Real.pi

private lemma symUnitMat_01 (x : Fin 6 → ℝ) : symUnitMat x 0 1 = x 0 := rfl
private lemma symUnitMat_02 (x : Fin 6 → ℝ) : symUnitMat x 0 2 = x 1 := rfl
private lemma symUnitMat_03 (x : Fin 6 → ℝ) : symUnitMat x 0 3 = x 2 := rfl
private lemma symUnitMat_12 (x : Fin 6 → ℝ) : symUnitMat x 1 2 = x 3 := rfl
private lemma symUnitMat_13 (x : Fin 6 → ℝ) : symUnitMat x 1 3 = x 4 := rfl
private lemma symUnitMat_23 (x : Fin 6 → ℝ) : symUnitMat x 2 3 = x 5 := rfl
private lemma symUnitMat_10 (x : Fin 6 → ℝ) : symUnitMat x 1 0 = x 0 := rfl
private lemma symUnitMat_20 (x : Fin 6 → ℝ) : symUnitMat x 2 0 = x 1 := rfl
private lemma symUnitMat_30 (x : Fin 6 → ℝ) : symUnitMat x 3 0 = x 2 := rfl
private lemma symUnitMat_21 (x : Fin 6 → ℝ) : symUnitMat x 2 1 = x 3 := rfl
private lemma symUnitMat_31 (x : Fin 6 → ℝ) : symUnitMat x 3 1 = x 4 := rfl
private lemma symUnitMat_32 (x : Fin 6 → ℝ) : symUnitMat x 3 2 = x 5 := rfl

theorem faceAngle_eq_faceLinkAngle (T : SphericalTetrahedron) (r a b : Fin 4) :
    T.faceAngle r a b =
      faceLinkAngle (symUnitMat (gramPoint T) r a)
        (symUnitMat (gramPoint T) r b)
        (symUnitMat (gramPoint T) a b) := by
  have hnorm_a : ‖T.projNormal r a‖ ^ 2 = 1 - symUnitMat (gramPoint T) r a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, projNormal]
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, T.unit a, T.unit r]
    rw [symUnitMat_gramPoint T r a]
    have hc : ⟪T.normal a, T.normal r⟫_ℝ = ⟪T.normal r, T.normal a⟫_ℝ := real_inner_comm _ _
    rw [hc]
    ring
  have hnorm_b : ‖T.projNormal r b‖ ^ 2 = 1 - symUnitMat (gramPoint T) r b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, projNormal]
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, T.unit b, T.unit r]
    rw [symUnitMat_gramPoint T r b]
    have hc : ⟪T.normal b, T.normal r⟫_ℝ = ⟪T.normal r, T.normal b⟫_ℝ := real_inner_comm _ _
    rw [hc]
    ring
  have hdot : ⟪T.projNormal r a, T.projNormal r b⟫_ℝ =
      symUnitMat (gramPoint T) a b -
        symUnitMat (gramPoint T) r a * symUnitMat (gramPoint T) r b := by
    rw [projNormal, projNormal]
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, T.unit r]
    rw [symUnitMat_gramPoint T r a, symUnitMat_gramPoint T r b, symUnitMat_gramPoint T a b]
    have hcr : ⟪T.normal a, T.normal r⟫_ℝ = ⟪T.normal r, T.normal a⟫_ℝ := real_inner_comm _ _
    rw [hcr]
    ring
  unfold faceAngle faceLinkAngle unitProjNormal
  rw [real_inner_smul_left, real_inner_smul_right, hdot]
  have ha_sq : ‖T.projNormal r a‖ = Real.sqrt (1 - symUnitMat (gramPoint T) r a ^ 2) := by
    rw [← hnorm_a, Real.sqrt_sq (norm_nonneg _)]
  have hb_sq : ‖T.projNormal r b‖ = Real.sqrt (1 - symUnitMat (gramPoint T) r b ^ 2) := by
    rw [← hnorm_b, Real.sqrt_sq (norm_nonneg _)]
  have h1a : 0 ≤ 1 - symUnitMat (gramPoint T) r a ^ 2 := by
    rw [← hnorm_a]; exact sq_nonneg _
  rw [ha_sq, hb_sq]
  congr 1
  rw [Real.sqrt_mul h1a, div_eq_mul_inv, mul_inv_rev]
  ring

theorem stdArea_eq_stdAreaGram (T : SphericalTetrahedron) :
    T.stdArea = stdAreaGram (gramPoint T) := by
  unfold stdArea stdFaceArea stdAreaGram vertexLinkSum
  simp only [Fin.sum_univ_four]
  have h01 : (0 : Fin 4).succAbove 0 = 1 := rfl
  have h02 : (0 : Fin 4).succAbove 1 = 2 := rfl
  have h03 : (0 : Fin 4).succAbove 2 = 3 := rfl
  have h10 : (1 : Fin 4).succAbove 0 = 0 := rfl
  have h12 : (1 : Fin 4).succAbove 1 = 2 := rfl
  have h13 : (1 : Fin 4).succAbove 2 = 3 := rfl
  have h20 : (2 : Fin 4).succAbove 0 = 0 := rfl
  have h21 : (2 : Fin 4).succAbove 1 = 1 := rfl
  have h23 : (2 : Fin 4).succAbove 2 = 3 := rfl
  have h30 : (3 : Fin 4).succAbove 0 = 0 := rfl
  have h31 : (3 : Fin 4).succAbove 1 = 1 := rfl
  have h32 : (3 : Fin 4).succAbove 2 = 2 := rfl
  rw [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32]
  simp only [faceAngle_eq_faceLinkAngle, symUnitMat_01, symUnitMat_02, symUnitMat_03,
    symUnitMat_12, symUnitMat_13, symUnitMat_23, symUnitMat_10, symUnitMat_20,
    symUnitMat_30, symUnitMat_21, symUnitMat_31, symUnitMat_32]
  rw [faceLinkAngle_comm (gramPoint T 2) (gramPoint T 0) (gramPoint T 4)]
  rw [faceLinkAngle_comm (gramPoint T 0) (gramPoint T 3) (gramPoint T 1)]
  rw [faceLinkAngle_comm (gramPoint T 3) (gramPoint T 5) (gramPoint T 4)]
  rw [faceLinkAngle_comm (gramPoint T 5) (gramPoint T 2) (gramPoint T 1)]
  ring

def triDet3 (u v w : ℝ) : ℝ :=
  1 - u ^ 2 - v ^ 2 - w ^ 2 + 2 * u * v * w

def triProj0 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
def triProj1 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
def triProj2 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 2

private lemma symUnitAdj_00 (x : Fin 6 → ℝ) : symUnitAdj x 0 0 = triDet3 (x 3) (x 4) (x 5) := by
  simp [symUnitAdj, triDet3]
private lemma symUnitAdj_11 (x : Fin 6 → ℝ) : symUnitAdj x 1 1 = triDet3 (x 1) (x 2) (x 5) := by
  simp [symUnitAdj, triDet3]
private lemma symUnitAdj_22 (x : Fin 6 → ℝ) : symUnitAdj x 2 2 = triDet3 (x 0) (x 2) (x 4) := by
  simp [symUnitAdj, triDet3, Matrix.cons_val_two]
private lemma symUnitAdj_33 (x : Fin 6 → ℝ) : symUnitAdj x 3 3 = triDet3 (x 0) (x 1) (x 3) := by
  simp [symUnitAdj, triDet3, Matrix.cons_val_three]

def faceLinkAngleFDeriv (p : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  let u := p 0; let v := p 1; let w := p 2
  let D := triDet3 u v w
  (((u * w - v) / ((1 - u ^ 2) * Real.sqrt D)) • triProj0 +
    ((v * w - u) / ((1 - v ^ 2) * Real.sqrt D)) • triProj1) +
    (1 / Real.sqrt D) • triProj2

private lemma hasFDerivAt_faceLinkAngle {p : Fin 3 → ℝ}
    (hu : |p 0| < 1) (hv : |p 1| < 1) (hD : 0 < triDet3 (p 0) (p 1) (p 2)) :
    HasFDerivAt (fun q : Fin 3 → ℝ => faceLinkAngle (q 0) (q 1) (q 2))
      (faceLinkAngleFDeriv p) p := by
  let u := p 0; let v := p 1; let w := p 2
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith [abs_lt.mp hu]
  have hv2 : 0 < 1 - v ^ 2 := by nlinarith [abs_lt.mp hv]
  have hprod : 0 < (1 - u ^ 2) * (1 - v ^ 2) := mul_pos hu2 hv2
  have hs : 0 < Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2)) := Real.sqrt_pos.mpr hprod
  let q0 : ℝ := (u * v - w) / Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2))
  have h1q : 1 - q0 ^ 2 = triDet3 u v w / ((1 - u ^ 2) * (1 - v ^ 2)) := by
    dsimp [q0, triDet3]
    rw [div_pow, Real.sq_sqrt hprod.le]
    field_simp [hprod.ne']
    ring
  have h1q_pos : 0 < 1 - q0 ^ 2 := by
    rw [h1q]
    exact div_pos hD hprod
  have hqm1 : q0 ≠ -1 := by nlinarith
  have hq1 : q0 ≠ 1 := by nlinarith
  have harc : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - q0 ^ 2))) q0 :=
    Real.hasDerivAt_arccos hqm1 hq1
  have h0 : HasFDerivAt (fun q : Fin 3 → ℝ => q 0) triProj0 p := triProj0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : Fin 3 → ℝ => q 1) triProj1 p := triProj1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : Fin 3 → ℝ => q 2) triProj2 p := triProj2.hasFDerivAt
  have hnum : HasFDerivAt (fun q : Fin 3 → ℝ => q 0 * q 1 - q 2)
      ((u • triProj1 + v • triProj0) - triProj2) p :=
    (h0.fun_mul h1).fun_sub h2
  have hg1 : HasFDerivAt (fun q : Fin 3 → ℝ => 1 - q 0 ^ 2) (-((2 * u) • triProj0)) p := by
    refine ((hasFDerivAt_const (1 : ℝ) p).fun_sub (h0.pow 2)).congr_fderiv ?_
    ext h; simp [u, triProj0, smul_eq_mul, two_mul]
  have hg2 : HasFDerivAt (fun q : Fin 3 → ℝ => 1 - q 1 ^ 2) (-((2 * v) • triProj1)) p := by
    refine ((hasFDerivAt_const (1 : ℝ) p).fun_sub (h1.pow 2)).congr_fderiv ?_
    ext h; simp [v, triProj1, smul_eq_mul, two_mul]
  have hgprod : HasFDerivAt (fun q : Fin 3 → ℝ => (1 - q 0 ^ 2) * (1 - q 1 ^ 2))
      ((1 - u ^ 2) • (-((2 * v) • triProj1)) + (1 - v ^ 2) • (-((2 * u) • triProj0))) p :=
    hg1.fun_mul hg2
  have hden := hgprod.sqrt hprod.ne'
  have hden_inv := ((hasFDerivAt_inv hs.ne').comp p hden).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  have hq := (hnum.fun_mul hden_inv).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q => (div_eq_mul_inv _ _).symm)
  have hcomp := (harc.comp_hasFDerivAt p hq).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  refine hcomp.congr_fderiv ?_
  ext h
  simp only [smul_apply, add_apply,
    sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, triProj0, triProj1, triProj2,
    ContinuousLinearMap.proj_apply, smul_eq_mul, faceLinkAngleFDeriv, Function.comp_apply]
  have hsD : Real.sqrt (triDet3 u v w) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hsq_prod : Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2)) ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) :=
    Real.sq_sqrt hprod.le
  have hsqrt_1q : Real.sqrt (1 - q0 ^ 2) =
      Real.sqrt (triDet3 u v w) / Real.sqrt ((1 - u ^ 2) * (1 - v ^ 2)) := by
    rw [h1q, Real.sqrt_div hD.le]
  rw [hsqrt_1q, hsq_prod]
  have hsne := hs.ne'
  have hu2ne := hu2.ne'
  have hv2ne := hv2.ne'
  simp only [u, v, w] at hsD hsne hu2ne hv2ne ⊢
  field_simp
  ring

def triPerm120 : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![triProj1, triProj2, triProj0]

def triPerm201 : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![triProj2, triProj0, triProj1]

private lemma triPerm120_0 (q : Fin 3 → ℝ) : triPerm120 q 0 = q 1 := rfl
private lemma triPerm120_1 (q : Fin 3 → ℝ) : triPerm120 q 1 = q 2 := rfl
private lemma triPerm120_2 (q : Fin 3 → ℝ) : triPerm120 q 2 = q 0 := rfl
private lemma triPerm201_0 (q : Fin 3 → ℝ) : triPerm201 q 0 = q 2 := rfl
private lemma triPerm201_1 (q : Fin 3 → ℝ) : triPerm201 q 1 = q 0 := rfl
private lemma triPerm201_2 (q : Fin 3 → ℝ) : triPerm201 q 2 = q 1 := rfl

def vertexLinkSumFDeriv (p : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  let u := p 0; let v := p 1; let w := p 2
  let sD := Real.sqrt (triDet3 u v w)
  (((1 + u - v - w) / ((1 + u) * sD)) • triProj0 +
    ((1 + v - w - u) / ((1 + v) * sD)) • triProj1) +
    ((1 + w - u - v) / ((1 + w) * sD)) • triProj2

private lemma vertexLinkSumFDeriv_apply (p q : Fin 3 → ℝ) :
    vertexLinkSumFDeriv p q =
      ((1 + p 0 - p 1 - p 2) / ((1 + p 0) * Real.sqrt (triDet3 (p 0) (p 1) (p 2)))) * q 0 +
      ((1 + p 1 - p 2 - p 0) / ((1 + p 1) * Real.sqrt (triDet3 (p 0) (p 1) (p 2)))) * q 1 +
      ((1 + p 2 - p 0 - p 1) / ((1 + p 2) * Real.sqrt (triDet3 (p 0) (p 1) (p 2)))) * q 2 := by
  simp only [vertexLinkSumFDeriv, add_apply, smul_apply, triProj0, triProj1, triProj2,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

private lemma hasFDerivAt_vertexLinkSum {p : Fin 3 → ℝ}
    (hu : |p 0| < 1) (hv : |p 1| < 1) (hw : |p 2| < 1)
    (hD : 0 < triDet3 (p 0) (p 1) (p 2)) :
    HasFDerivAt (fun q : Fin 3 → ℝ => vertexLinkSum (q 0) (q 1) (q 2))
      (vertexLinkSumFDeriv p) p := by
  let u := p 0; let v := p 1; let w := p 2
  have hD1 : 0 < triDet3 (triPerm120 p 0) (triPerm120 p 1) (triPerm120 p 2) := by
    rw [triPerm120_0, triPerm120_1, triPerm120_2]; dsimp [triDet3] at hD ⊢; linarith [hD]
  have hD2 : 0 < triDet3 (triPerm201 p 0) (triPerm201 p 1) (triPerm201 p 2) := by
    rw [triPerm201_0, triPerm201_1, triPerm201_2]; dsimp [triDet3] at hD ⊢; linarith [hD]
  have hf0 := hasFDerivAt_faceLinkAngle hu hv hD
  have hf1_base := hasFDerivAt_faceLinkAngle (p := triPerm120 p)
    (by rw [triPerm120_0]; exact hv) (by rw [triPerm120_1]; exact hw) hD1
  have hf2_base := hasFDerivAt_faceLinkAngle (p := triPerm201 p)
    (by rw [triPerm201_0]; exact hw) (by rw [triPerm201_1]; exact hu) hD2
  have hf1 : HasFDerivAt (fun q : Fin 3 → ℝ => faceLinkAngle (q 1) (q 2) (q 0))
      ((faceLinkAngleFDeriv (triPerm120 p)).comp triPerm120) p :=
    (hf1_base.comp p triPerm120.hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => by simp [triPerm120_0, triPerm120_1, triPerm120_2])
  have hf2 : HasFDerivAt (fun q : Fin 3 → ℝ => faceLinkAngle (q 2) (q 0) (q 1))
      ((faceLinkAngleFDeriv (triPerm201 p)).comp triPerm201) p :=
    (hf2_base.comp p triPerm201.hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => by simp [triPerm201_0, triPerm201_1, triPerm201_2])
  have hsum := ((hf0.fun_add hf1).fun_add hf2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  refine hsum.congr_fderiv ?_
  ext h
  simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    triPerm120_0, triPerm120_1, triPerm120_2, triPerm201_0, triPerm201_1, triPerm201_2,
    triProj0, triProj1, triProj2, ContinuousLinearMap.proj_apply, smul_eq_mul,
    vertexLinkSumFDeriv, faceLinkAngleFDeriv]
  have hu1p : 1 + u ≠ 0 := by linarith [(abs_lt.mp hu).1]
  have hv1p : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hw1p : 1 + w ≠ 0 := by linarith [(abs_lt.mp hw).1]
  have hu2 : 1 - u ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hu]
  have hv2 : 1 - v ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hv]
  have hw2 : 1 - w ^ 2 ≠ 0 := by nlinarith [abs_lt.mp hw]
  have hD1eq : triDet3 (p 1) (p 2) (p 0) = triDet3 u v w := by dsimp [triDet3, u, v, w]; ring
  have hD2eq : triDet3 (p 2) (p 0) (p 1) = triDet3 u v w := by dsimp [triDet3, u, v, w]; ring
  change (u * w - v) / ((1 - u ^ 2) * Real.sqrt (triDet3 u v w)) * h 0 +
      (v * w - u) / ((1 - v ^ 2) * Real.sqrt (triDet3 u v w)) * h 1 +
      1 / Real.sqrt (triDet3 u v w) * h 2 +
      ((v * u - w) / ((1 - v ^ 2) * Real.sqrt (triDet3 (p 1) (p 2) (p 0))) * h 1 +
        (w * u - v) / ((1 - w ^ 2) * Real.sqrt (triDet3 (p 1) (p 2) (p 0))) * h 2 +
        1 / Real.sqrt (triDet3 (p 1) (p 2) (p 0)) * h 0) +
      ((w * v - u) / ((1 - w ^ 2) * Real.sqrt (triDet3 (p 2) (p 0) (p 1))) * h 2 +
        (u * v - w) / ((1 - u ^ 2) * Real.sqrt (triDet3 (p 2) (p 0) (p 1))) * h 0 +
        1 / Real.sqrt (triDet3 (p 2) (p 0) (p 1)) * h 1) =
    (1 + u - v - w) / ((1 + u) * Real.sqrt (triDet3 u v w)) * h 0 +
      (1 + v - w - u) / ((1 + v) * Real.sqrt (triDet3 u v w)) * h 1 +
      (1 + w - u - v) / ((1 + w) * Real.sqrt (triDet3 u v w)) * h 2
  rw [hD1eq, hD2eq]
  have hsD : Real.sqrt (triDet3 u v w) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  field_simp [hu1p, hv1p, hw1p, hu2, hv2, hw2, hsD]
  ring

def coordProj6 (k : Fin 6) : (Fin 6 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k

def linkMap0 : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![coordProj6 3, coordProj6 4, coordProj6 5]
def linkMap1 : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![coordProj6 1, coordProj6 2, coordProj6 5]
def linkMap2 : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![coordProj6 0, coordProj6 2, coordProj6 4]
def linkMap3 : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![coordProj6 0, coordProj6 1, coordProj6 3]

private lemma linkMap0_0 (q : Fin 6 → ℝ) : linkMap0 q 0 = q 3 := rfl
private lemma linkMap0_1 (q : Fin 6 → ℝ) : linkMap0 q 1 = q 4 := rfl
private lemma linkMap0_2 (q : Fin 6 → ℝ) : linkMap0 q 2 = q 5 := rfl
private lemma linkMap1_0 (q : Fin 6 → ℝ) : linkMap1 q 0 = q 1 := rfl
private lemma linkMap1_1 (q : Fin 6 → ℝ) : linkMap1 q 1 = q 2 := rfl
private lemma linkMap1_2 (q : Fin 6 → ℝ) : linkMap1 q 2 = q 5 := rfl
private lemma linkMap2_0 (q : Fin 6 → ℝ) : linkMap2 q 0 = q 0 := rfl
private lemma linkMap2_1 (q : Fin 6 → ℝ) : linkMap2 q 1 = q 2 := rfl
private lemma linkMap2_2 (q : Fin 6 → ℝ) : linkMap2 q 2 = q 4 := rfl
private lemma linkMap3_0 (q : Fin 6 → ℝ) : linkMap3 q 0 = q 0 := rfl
private lemma linkMap3_1 (q : Fin 6 → ℝ) : linkMap3 q 1 = q 1 := rfl
private lemma linkMap3_2 (q : Fin 6 → ℝ) : linkMap3 q 2 = q 3 := rfl

/-- Fréchet derivative of `stdAreaGram` on `gramOpen`. -/
def stdAreaFDeriv (x : Fin 6 → ℝ) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  (((vertexLinkSumFDeriv (linkMap0 x)).comp linkMap0 +
      (vertexLinkSumFDeriv (linkMap1 x)).comp linkMap1) +
      (vertexLinkSumFDeriv (linkMap2 x)).comp linkMap2) +
      (vertexLinkSumFDeriv (linkMap3 x)).comp linkMap3

theorem hasFDerivAt_stdAreaGram {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    HasFDerivAt stdAreaGram (stdAreaFDeriv x) x := by
  have hlt : ∀ k : Fin 6, |x k| < 1 := gramOpen_offdiag_abs_lt_one hx
  have hD0 : 0 < triDet3 (linkMap0 x 0) (linkMap0 x 1) (linkMap0 x 2) := by
    rw [linkMap0_0, linkMap0_1, linkMap0_2, ← symUnitAdj_00]; exact gramOpen_adj_diag_pos hx 0
  have hD1 : 0 < triDet3 (linkMap1 x 0) (linkMap1 x 1) (linkMap1 x 2) := by
    rw [linkMap1_0, linkMap1_1, linkMap1_2, ← symUnitAdj_11]; exact gramOpen_adj_diag_pos hx 1
  have hD2 : 0 < triDet3 (linkMap2 x 0) (linkMap2 x 1) (linkMap2 x 2) := by
    rw [linkMap2_0, linkMap2_1, linkMap2_2, ← symUnitAdj_22]; exact gramOpen_adj_diag_pos hx 2
  have hD3 : 0 < triDet3 (linkMap3 x 0) (linkMap3 x 1) (linkMap3 x 2) := by
    rw [linkMap3_0, linkMap3_1, linkMap3_2, ← symUnitAdj_33]; exact gramOpen_adj_diag_pos hx 3
  have hl0 := (hasFDerivAt_vertexLinkSum (p := linkMap0 x)
    (by rw [linkMap0_0]; exact hlt 3) (by rw [linkMap0_1]; exact hlt 4)
    (by rw [linkMap0_2]; exact hlt 5) hD0).comp x linkMap0.hasFDerivAt
  have hl1 := (hasFDerivAt_vertexLinkSum (p := linkMap1 x)
    (by rw [linkMap1_0]; exact hlt 1) (by rw [linkMap1_1]; exact hlt 2)
    (by rw [linkMap1_2]; exact hlt 5) hD1).comp x linkMap1.hasFDerivAt
  have hl2 := (hasFDerivAt_vertexLinkSum (p := linkMap2 x)
    (by rw [linkMap2_0]; exact hlt 0) (by rw [linkMap2_1]; exact hlt 2)
    (by rw [linkMap2_2]; exact hlt 4) hD2).comp x linkMap2.hasFDerivAt
  have hl3 := (hasFDerivAt_vertexLinkSum (p := linkMap3 x)
    (by rw [linkMap3_0]; exact hlt 0) (by rw [linkMap3_1]; exact hlt 1)
    (by rw [linkMap3_2]; exact hlt 3) hD3).comp x linkMap3.hasFDerivAt
  have htot := (((hl0.fun_add hl1).fun_add hl2).fun_add hl3).fun_sub (hasFDerivAt_const (4 * Real.pi) x)
  refine (htot.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)).congr_fderiv ?_
  · simp [stdAreaGram, linkMap0_0, linkMap0_1, linkMap0_2,
      linkMap1_0, linkMap1_1, linkMap1_2, linkMap2_0, linkMap2_1, linkMap2_2,
      linkMap3_0, linkMap3_1, linkMap3_2]
  · simp [stdAreaFDeriv]

theorem continuousOn_stdAreaFDeriv : ContinuousOn stdAreaFDeriv gramOpen := by
  intro x hx
  have hc_link0 : ContinuousAt (fun y : Fin 6 → ℝ => linkMap0 y) x := linkMap0.continuous.continuousAt
  have hc_link1 : ContinuousAt (fun y : Fin 6 → ℝ => linkMap1 y) x := linkMap1.continuous.continuousAt
  have hc_link2 : ContinuousAt (fun y : Fin 6 → ℝ => linkMap2 y) x := linkMap2.continuous.continuousAt
  have hc_link3 : ContinuousAt (fun y : Fin 6 → ℝ => linkMap3 y) x := linkMap3.continuous.continuousAt
  have hc_vls : ∀ {p : Fin 3 → ℝ}, |p 0| < 1 → |p 1| < 1 → |p 2| < 1 →
      0 < triDet3 (p 0) (p 1) (p 2) → ContinuousAt vertexLinkSumFDeriv p := by
    intro p hu hv hw hD
    have hq0 : ContinuousAt (fun q : Fin 3 → ℝ => q 0) p := (continuous_apply 0).continuousAt
    have hq1 : ContinuousAt (fun q : Fin 3 → ℝ => q 1) p := (continuous_apply 1).continuousAt
    have hq2 : ContinuousAt (fun q : Fin 3 → ℝ => q 2) p := (continuous_apply 2).continuousAt
    have hD_cont : ContinuousAt (fun q : Fin 3 → ℝ => triDet3 (q 0) (q 1) (q 2)) p := by
      unfold triDet3
      exact ((((continuousAt_const.sub (hq0.pow 2)).sub (hq1.pow 2)).sub (hq2.pow 2)).add
        (((continuousAt_const.mul hq0).mul hq1).mul hq2))
    have hc0 : ContinuousAt (fun q : Fin 3 → ℝ => (1 + q 0 - q 1 - q 2) /
        ((1 + q 0) * Real.sqrt (triDet3 (q 0) (q 1) (q 2)))) p :=
      (((continuousAt_const.add hq0).sub hq1).sub hq2).div
        ((continuousAt_const.add hq0).mul hD_cont.sqrt)
        (mul_ne_zero (by linarith [(abs_lt.mp hu).1]) (Real.sqrt_pos.mpr hD).ne')
    have hc1 : ContinuousAt (fun q : Fin 3 → ℝ => (1 + q 1 - q 2 - q 0) /
        ((1 + q 1) * Real.sqrt (triDet3 (q 0) (q 1) (q 2)))) p :=
      (((continuousAt_const.add hq1).sub hq2).sub hq0).div
        ((continuousAt_const.add hq1).mul hD_cont.sqrt)
        (mul_ne_zero (by linarith [(abs_lt.mp hv).1]) (Real.sqrt_pos.mpr hD).ne')
    have hc2 : ContinuousAt (fun q : Fin 3 → ℝ => (1 + q 2 - q 0 - q 1) /
        ((1 + q 2) * Real.sqrt (triDet3 (q 0) (q 1) (q 2)))) p :=
      (((continuousAt_const.add hq2).sub hq0).sub hq1).div
        ((continuousAt_const.add hq2).mul hD_cont.sqrt)
        (mul_ne_zero (by linarith [(abs_lt.mp hw).1]) (Real.sqrt_pos.mpr hD).ne')
    unfold vertexLinkSumFDeriv
    exact ((hc0.smul continuousAt_const).add (hc1.smul continuousAt_const)).add
      (hc2.smul continuousAt_const)
  have hlt := gramOpen_offdiag_abs_lt_one hx
  have hD0 : 0 < triDet3 (linkMap0 x 0) (linkMap0 x 1) (linkMap0 x 2) := by
    rw [linkMap0_0, linkMap0_1, linkMap0_2, ← symUnitAdj_00]; exact gramOpen_adj_diag_pos hx 0
  have hD1 : 0 < triDet3 (linkMap1 x 0) (linkMap1 x 1) (linkMap1 x 2) := by
    rw [linkMap1_0, linkMap1_1, linkMap1_2, ← symUnitAdj_11]; exact gramOpen_adj_diag_pos hx 1
  have hD2 : 0 < triDet3 (linkMap2 x 0) (linkMap2 x 1) (linkMap2 x 2) := by
    rw [linkMap2_0, linkMap2_1, linkMap2_2, ← symUnitAdj_22]; exact gramOpen_adj_diag_pos hx 2
  have hD3 : 0 < triDet3 (linkMap3 x 0) (linkMap3 x 1) (linkMap3 x 2) := by
    rw [linkMap3_0, linkMap3_1, linkMap3_2, ← symUnitAdj_33]; exact gramOpen_adj_diag_pos hx 3
  have hv0 := (hc_vls (p := linkMap0 x) (by rw [linkMap0_0]; exact hlt 3)
    (by rw [linkMap0_1]; exact hlt 4) (by rw [linkMap0_2]; exact hlt 5) hD0).comp hc_link0
  have hv1 := (hc_vls (p := linkMap1 x) (by rw [linkMap1_0]; exact hlt 1)
    (by rw [linkMap1_1]; exact hlt 2) (by rw [linkMap1_2]; exact hlt 5) hD1).comp hc_link1
  have hv2 := (hc_vls (p := linkMap2 x) (by rw [linkMap2_0]; exact hlt 0)
    (by rw [linkMap2_1]; exact hlt 2) (by rw [linkMap2_2]; exact hlt 4) hD2).comp hc_link2
  have hv3 := (hc_vls (p := linkMap3 x) (by rw [linkMap3_0]; exact hlt 0)
    (by rw [linkMap3_1]; exact hlt 1) (by rw [linkMap3_2]; exact hlt 3) hD3).comp hc_link3
  have hcompL : ∀ L : (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℝ),
      Continuous ((fun A : (Fin 3 → ℝ) →L[ℝ] ℝ => A.comp L)) := fun L =>
    ((ContinuousLinearMap.compL ℝ (Fin 6 → ℝ) (Fin 3 → ℝ) ℝ).flip L).continuous
  have hc_tot : ContinuousAt stdAreaFDeriv x := by
    unfold stdAreaFDeriv
    exact (((hcompL linkMap0).continuousAt.comp hv0).add
      ((hcompL linkMap1).continuousAt.comp hv1)).add
      ((hcompL linkMap2).continuousAt.comp hv2) |>.add
      ((hcompL linkMap3).continuousAt.comp hv3)
  exact hc_tot.continuousWithinAt

theorem hasStrictFDerivAt_stdAreaGram {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    HasStrictFDerivAt stdAreaGram (stdAreaFDeriv x) x := by
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt ?_ ?_
  · exact Filter.Eventually.mono (isOpen_gramOpen.mem_nhds hx) fun y hy => hasFDerivAt_stdAreaGram hy
  · exact (continuousOn_stdAreaFDeriv x hx).continuousAt (isOpen_gramOpen.mem_nhds hx)

private lemma pairIdx_0 : pairIdx 0 = (0, 1) := rfl
private lemma pairIdx_1 : pairIdx 1 = (0, 2) := rfl
private lemma pairIdx_2 : pairIdx 2 = (0, 3) := rfl
private lemma pairIdx_3 : pairIdx 3 = (1, 2) := rfl
private lemma pairIdx_4 : pairIdx 4 = (1, 3) := rfl
private lemma pairIdx_5 : pairIdx 5 = (2, 3) := rfl

private lemma oppIdx_0 : oppIdx 0 = (2, 3) := rfl
private lemma oppIdx_1 : oppIdx 1 = (1, 3) := rfl
private lemma oppIdx_2 : oppIdx 2 = (1, 2) := rfl
private lemma oppIdx_3 : oppIdx 3 = (0, 3) := rfl
private lemma oppIdx_4 : oppIdx 4 = (0, 2) := rfl
private lemma oppIdx_5 : oppIdx 5 = (0, 1) := rfl

private lemma stdAreaFDeriv_coord_step1 (x : Fin 6 → ℝ) (k : Fin 6) :
    stdAreaFDeriv x (Pi.single k 1) =
      (1 + symUnitMat x (pairIdx k).1 (pairIdx k).2 -
          symUnitMat x (pairIdx k).1 (oppIdx k).2 -
          symUnitMat x (pairIdx k).2 (oppIdx k).2) /
        ((1 + symUnitMat x (pairIdx k).1 (pairIdx k).2) *
          Real.sqrt (symUnitAdj x (oppIdx k).1 (oppIdx k).1)) +
      (1 + symUnitMat x (pairIdx k).1 (pairIdx k).2 -
          symUnitMat x (pairIdx k).1 (oppIdx k).1 -
          symUnitMat x (pairIdx k).2 (oppIdx k).1) /
        ((1 + symUnitMat x (pairIdx k).1 (pairIdx k).2) *
          Real.sqrt (symUnitAdj x (oppIdx k).2 (oppIdx k).2)) := by
  fin_cases k <;>
  · simp only [stdAreaFDeriv, add_apply, ContinuousLinearMap.comp_apply,
      vertexLinkSumFDeriv_apply, linkMap0_0, linkMap0_1, linkMap0_2,
      linkMap1_0, linkMap1_1, linkMap1_2, linkMap2_0, linkMap2_1, linkMap2_2,
      linkMap3_0, linkMap3_1, linkMap3_2, Pi.single_apply, Fin.isValue]
    norm_num
    simp only [pairIdx_0, pairIdx_1, pairIdx_2, pairIdx_3, pairIdx_4, pairIdx_5,
      oppIdx_0, oppIdx_1, oppIdx_2, oppIdx_3, oppIdx_4, oppIdx_5, Fin.isValue,
      symUnitMat_01, symUnitMat_02, symUnitMat_03, symUnitMat_12, symUnitMat_13, symUnitMat_23,
      symUnitMat_10, symUnitMat_20, symUnitMat_30, symUnitMat_21, symUnitMat_31, symUnitMat_32,
      symUnitAdj_00, symUnitAdj_11, symUnitAdj_22, symUnitAdj_33]
    try ring

theorem stdAreaFDeriv_coord {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (k : Fin 6) :
    let T := tetOf x hx
    let (i, j) := oppIdx k
    let ρ := ⟪T.dualVertex i, T.dualVertex j⟫_ℝ
    let aij := Real.sqrt (1 - ρ ^ 2) / (1 + ρ)
    stdAreaFDeriv x (Pi.single k 1) =
      ((⟪T.normalDualAxis, T.dualVertex i⟫_ℝ + ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) * aij) /
        Real.sqrt (1 - x k ^ 2) := by
  dsimp only
  set T := tetOf x hx
  have hgm : gramPoint T = x := gramPoint_tetOf hx
  let p := (pairIdx k).1
  let q := (pairIdx k).2
  let i := (oppIdx k).1
  let j := (oppIdx k).2
  let M := symUnitAdj x
  let G := symUnitMat x
  have hdet : 0 < G.det := gramOpen_det_pos hx
  have hi : 0 < M i i := gramOpen_adj_diag_pos hx i
  have hj : 0 < M j j := gramOpen_adj_diag_pos hx j
  have hjac : 0 < M i i * M j j - M i j ^ 2 := gramOpen_jacobi_pos hx k
  have hxk : |x k| < 1 := gramOpen_offdiag_abs_lt_one hx k
  have hg_sq : 0 < 1 - x k ^ 2 := by nlinarith [abs_lt.mp hxk]
  have hgp1 : 0 < 1 + x k := by linarith [(abs_lt.mp hxk).1]
  have hgm1 : 0 < 1 - x k := by linarith [(abs_lt.mp hxk).2]
  have hstep1 :
      stdAreaFDeriv x (Pi.single k 1) =
        (1 + G p q - G p j - G q j) / ((1 + G p q) * Real.sqrt (M i i)) +
        (1 + G p q - G p i - G q i) / ((1 + G p q) * Real.sqrt (M j j)) :=
    stdAreaFDeriv_coord_step1 x k
  rw [hstep1]
  have hrho : ⟪T.dualVertex i, T.dualVertex j⟫_ℝ = M i j / Real.sqrt (M i i * M j j) := by
    rw [T.dualVertex_inner_eq_adj i j, hgm]
  have hhi : ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ =
      (∑ l : Fin 4, M l i) / Real.sqrt (G.det * M i i) := by
    rw [T.dualHeight_eq_adj i, hgm]
  have hhj : ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ =
      (∑ l : Fin 4, M l j) / Real.sqrt (G.det * M j j) := by
    rw [T.dualHeight_eq_adj j, hgm]
  rw [hrho, hhi, hhj]
  have hJac_eq : M i i * M j j - M i j ^ 2 = G.det * (1 - x k ^ 2) := by
    have := symUnitAdj_jacobi x k
    dsimp only at this
    rwa [symUnitMat_pairIdx] at this
  have hId_fst := symUnitAdj_area_identity_fst x k
  have hId_snd := symUnitAdj_area_identity_snd x k
  dsimp only at hId_fst hId_snd
  have h1rho2 :
      1 - (M i j / Real.sqrt (M i i * M j j)) ^ 2 =
        (G.det * (1 - x k ^ 2)) / (M i i * M j j) := by
    rw [div_pow, Real.sq_sqrt (mul_nonneg hi.le hj.le)]
    field_simp [(mul_pos hi hj).ne']
    linarith [hJac_eq]
  have hsqrt_1rho2 :
      Real.sqrt (1 - (M i j / Real.sqrt (M i i * M j j)) ^ 2) =
        (Real.sqrt G.det * Real.sqrt (1 - x k ^ 2)) / (Real.sqrt (M i i) * Real.sqrt (M j j)) := by
    rw [h1rho2, Real.sqrt_div (mul_nonneg hdet.le hg_sq.le),
      Real.sqrt_mul hdet.le, Real.sqrt_mul hi.le]
  have h1prho :
      1 + M i j / Real.sqrt (M i i * M j j) =
        (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j) / (Real.sqrt (M i i) * Real.sqrt (M j j)) := by
    rw [Real.sqrt_mul hi.le]
    field_simp [(Real.sqrt_pos.mpr hi).ne', (Real.sqrt_pos.mpr hj).ne']
  have hden_pos : 0 < Real.sqrt (M i i) * Real.sqrt (M j j) + M i j := by
    have hsq_lt : M i j ^ 2 < (Real.sqrt (M i i) * Real.sqrt (M j j)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hi.le, Real.sq_sqrt hj.le]
      linarith
    have hpos_m : 0 < Real.sqrt (M i i) * Real.sqrt (M j j) :=
      mul_pos (Real.sqrt_pos.mpr hi) (Real.sqrt_pos.mpr hj)
    nlinarith [sq_abs (M i j)]
  have hdiff_pos : 0 < Real.sqrt (M i i) * Real.sqrt (M j j) - M i j := by
    have hsq_lt : M i j ^ 2 < (Real.sqrt (M i i) * Real.sqrt (M j j)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hi.le, Real.sq_sqrt hj.le]
      linarith
    have hpos_m : 0 < Real.sqrt (M i i) * Real.sqrt (M j j) :=
      mul_pos (Real.sqrt_pos.mpr hi) (Real.sqrt_pos.mpr hj)
    nlinarith [sq_abs (M i j)]
  rw [hsqrt_1rho2, h1prho]
  rw [Real.sqrt_mul hdet.le, Real.sqrt_mul hdet.le]
  have hgpq : G p q = x k := symUnitMat_pairIdx x k
  rw [hgpq]
  have hsi : Real.sqrt (M i i) ≠ 0 := (Real.sqrt_pos.mpr hi).ne'
  have hsj : Real.sqrt (M j j) ≠ 0 := (Real.sqrt_pos.mpr hj).ne'
  have hsdet : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.mpr hdet).ne'
  have hsg : Real.sqrt (1 - x k ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hg_sq).ne'
  have hsi2 : Real.sqrt (M i i) ^ 2 = M i i := Real.sq_sqrt hi.le
  have hsj2 : Real.sqrt (M j j) ^ 2 = M j j := Real.sq_sqrt hj.le
  field_simp [hgp1.ne', hsi, hsj, hsdet, hsg, hden_pos.ne']
  have hcalc :
      ((1 + x k - G p j - G q j) * Real.sqrt (M j j) +
          (1 + x k - G p i - G q i) * Real.sqrt (M i i)) *
        (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j) =
      (1 + x k) * (((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
        (∑ l : Fin 4, M l j) * Real.sqrt (M i i))) := by
    have hmul :
        (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j) *
          (Real.sqrt (M i i) * Real.sqrt (M j j) - M i j) = G.det * (1 - x k ^ 2) := by
      have hh : (Real.sqrt (M i i) * Real.sqrt (M j j)) ^ 2 = M i i * M j j := by
        rw [mul_pow, hsi2, hsj2]
      linarith [hJac_eq]
    have hlhs :
        (((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
            (∑ l : Fin 4, M l j) * Real.sqrt (M i i)) *
          (Real.sqrt (M i i) * Real.sqrt (M j j) - M i j)) =
        (G.det * (1 - x k)) *
          ((1 + x k - G p j - G q j) * Real.sqrt (M j j) +
            (1 + x k - G p i - G q i) * Real.sqrt (M i i)) := by
      have hterm1 :
          (∑ l : Fin 4, M l j) * M i i - (∑ l : Fin 4, M l i) * M i j =
            G.det * (1 - x k) * (1 + x k - G p j - G q j) := by
        rw [← hgpq]
        have hsum : (∑ l : Fin 4, M l j) * M i i - (∑ l : Fin 4, M l i) * M i j =
            ∑ l : Fin 4, (M i i * M l j - M i j * M l i) := by
          simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
        rw [hsum]
        exact hId_fst
      have hterm2 :
          (∑ l : Fin 4, M l i) * M j j - (∑ l : Fin 4, M l j) * M i j =
            G.det * (1 - x k) * (1 + x k - G p i - G q i) := by
        rw [← hgpq]
        have hsum : (∑ l : Fin 4, M l i) * M j j - (∑ l : Fin 4, M l j) * M i j =
            ∑ l : Fin 4, (M j j * M l i - M i j * M l j) := by
          simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
        rw [hsum]
        exact hId_snd
      calc
        ((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
            (∑ l : Fin 4, M l j) * Real.sqrt (M i i)) *
            (Real.sqrt (M i i) * Real.sqrt (M j j) - M i j)
            = ((∑ l : Fin 4, M l j) * Real.sqrt (M i i) ^ 2 - (∑ l : Fin 4, M l i) * M i j) *
                Real.sqrt (M j j) +
              ((∑ l : Fin 4, M l i) * Real.sqrt (M j j) ^ 2 - (∑ l : Fin 4, M l j) * M i j) *
                Real.sqrt (M i i) := by ring
        _ = ((∑ l : Fin 4, M l j) * M i i - (∑ l : Fin 4, M l i) * M i j) *
                Real.sqrt (M j j) +
              ((∑ l : Fin 4, M l i) * M j j - (∑ l : Fin 4, M l j) * M i j) *
                Real.sqrt (M i i) := by rw [hsi2, hsj2]
        _ = (G.det * (1 - x k) * (1 + x k - G p j - G q j)) * Real.sqrt (M j j) +
              (G.det * (1 - x k) * (1 + x k - G p i - G q i)) * Real.sqrt (M i i) := by
            rw [hterm1, hterm2]
        _ = _ := by ring
    have hgfactor : G.det * (1 - x k ^ 2) = G.det * (1 - x k) * (1 + x k) := by ring
    have hnz : G.det * (1 - x k) ≠ 0 := mul_ne_zero hdet.ne' hgm1.ne'
    have hscaled :
        G.det * (1 - x k) *
          (((1 + x k - G p j - G q j) * Real.sqrt (M j j) +
              (1 + x k - G p i - G q i) * Real.sqrt (M i i)) *
            (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j)) =
        G.det * (1 - x k) *
          ((1 + x k) * (((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
            (∑ l : Fin 4, M l j) * Real.sqrt (M i i)))) := by
      calc
        G.det * (1 - x k) *
            (((1 + x k - G p j - G q j) * Real.sqrt (M j j) +
                (1 + x k - G p i - G q i) * Real.sqrt (M i i)) *
              (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j))
            = (G.det * (1 - x k) *
                ((1 + x k - G p j - G q j) * Real.sqrt (M j j) +
                  (1 + x k - G p i - G q i) * Real.sqrt (M i i))) *
              (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j) := by ring
        _ = (((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
                (∑ l : Fin 4, M l j) * Real.sqrt (M i i)) *
              (Real.sqrt (M i i) * Real.sqrt (M j j) - M i j)) *
              (Real.sqrt (M i i) * Real.sqrt (M j j) + M i j) := by rw [hlhs]
        _ = ((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
                (∑ l : Fin 4, M l j) * Real.sqrt (M i i)) *
              ((Real.sqrt (M i i) * Real.sqrt (M j j) + M i j) *
                (Real.sqrt (M i i) * Real.sqrt (M j j) - M i j)) := by ring
        _ = ((∑ l : Fin 4, M l i) * Real.sqrt (M j j) +
                (∑ l : Fin 4, M l j) * Real.sqrt (M i i)) *
              (G.det * (1 - x k) * (1 + x k)) := by rw [hmul, hgfactor]
        _ = _ := by ring
    exact mul_left_cancel₀ hnz hscaled
  linear_combination hcalc

end SphericalTetrahedron
