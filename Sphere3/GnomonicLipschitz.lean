module

public import Sphere3.GnomonicBase
public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section

/-!
# A globally Lipschitz normalization chart from R^3 into S^3

The map `u ↦ (u,1)/‖(u,1)‖` is 2-Lipschitz on all of R^3.
This follows from the elementary inequality

  ‖x/‖x‖ - y/‖y‖‖ ≤ 2 ‖x-y‖

when both norms are at least one. In particular, 3-dimensional
Hausdorff measure of the image of a compact region of R^3 is finite.
-/

noncomputable section

open MeasureTheory

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Exact reciprocal-difference identity with positive denominators. -/
theorem scalar_inv_difference_abs_mul (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| * b = |a - b| / a := by
  have hdiv : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp [ha.ne', hb.ne']
    <;> ring
  rw [hdiv, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, abs_sub_comm]
  field_simp [ha.ne', hb.ne']
  <;> ring

/-- Radial normalization is 2-Lipschitz on the complement of the open
unit ball, with respect to the distance between the original vectors. -/
theorem radialNormalization_two_lipschitz_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  let a : ℝ := ‖x‖
  let b : ℝ := ‖y‖
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one hx
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one hy
  have haInv : a⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ ha).2 (by simpa using hx)
  have hab : |a - b| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have hsub : a⁻¹ • x - b⁻¹ • y =
      a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y := by
    rw [smul_sub, sub_smul]
    abel
  have hfirst : a⁻¹ * ‖x - y‖ ≤ ‖x - y‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haInv) (norm_nonneg (x - y))]
  have hsecond : |a - b| / a ≤ ‖x - y‖ := by
    rw [div_eq_mul_inv]
    have hInv0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
    have hm := mul_le_mul_of_nonneg_right hab hInv0
    nlinarith [mul_nonneg (sub_nonneg.mpr haInv) (norm_nonneg (x - y))]
  change ‖a⁻¹ • x - b⁻¹ • y‖ ≤ 2 * ‖x - y‖
  calc
    ‖a⁻¹ • x - b⁻¹ • y‖ =
        ‖a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y‖ := by rw [hsub]
    _ ≤ ‖a⁻¹ • (x - y)‖ + ‖(a⁻¹ - b⁻¹) • y‖ := norm_add_le _ _
    _ = a⁻¹ * ‖x - y‖ + |a⁻¹ - b⁻¹| * b := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ha)]
        rfl
    _ = a⁻¹ * ‖x - y‖ + |a - b| / a := by
        rw [scalar_inv_difference_abs_mul a b ha hb]
    _ ≤ 2 * ‖x - y‖ := by linarith

/-- Embed the affine chart as the hyperplane of last coordinate one. -/
def gnomonicLift (u : E3) : E4 := !₂[u 0, u 1, u 2, 1]

/-- The affine lift has norm at least one everywhere. -/
theorem gnomonicLift_norm_sq (u : E3) :
    ‖gnomonicLift u‖ ^ 2 = ‖u‖ ^ 2 + 1 := by
  have h1 : ‖gnomonicLift u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp [gnomonicLift]
  have h2 : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  linarith

theorem gnomonicLift_norm_ge_one (u : E3) : 1 ≤ ‖gnomonicLift u‖ := by
  have h := gnomonicLift_norm_sq u
  nlinarith [sq_nonneg (‖u‖), norm_nonneg (gnomonicLift u)]

/-- Lifting to an affine hyperplane preserves pairwise distances. -/
theorem gnomonicLift_sub_norm (u v : E3) :
    ‖gnomonicLift u - gnomonicLift v‖ = ‖u - v‖ := by
  have h : ‖gnomonicLift u - gnomonicLift v‖ ^ 2 =
      ‖u - v‖ ^ 2 := by
    have h1 : ‖gnomonicLift u - gnomonicLift v‖ ^ 2 =
        (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
      simp [gnomonicLift]
    have h2 : ‖u - v‖ ^ 2 =
        (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 + (u 2 - v 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      simp only [PiLp.sub_apply]
    linarith
  nlinarith [norm_nonneg (gnomonicLift u - gnomonicLift v),
    norm_nonneg (u - v)]

/-- Spherical normalization of the affine lift. -/
def gnomonicNormalize (u : E3) : E4 :=
  ‖gnomonicLift u‖⁻¹ • gnomonicLift u

/-- The radial chart is globally 2-Lipschitz, not merely locally. -/
theorem gnomonicNormalize_lipschitz : LipschitzWith 2 gnomonicNormalize := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have h := radialNormalization_two_lipschitz_pair (gnomonicLift u)
    (gnomonicLift v) (gnomonicLift_norm_ge_one u)
    (gnomonicLift_norm_ge_one v)
  rw [gnomonicLift_sub_norm] at h
  simpa only [gnomonicNormalize, dist_eq_norm, NNReal.coe_ofNat] using h

/-- The image of a compact three-dimensional parameter set has finite
three-dimensional ambient Hausdorff measure. -/
theorem gnomonicNormalize_compact_hausdorff_finite
    (K : Set E3) (hK : IsCompact K) :
    (Measure.hausdorffMeasure (3 : ℝ) : Measure E4)
        (gnomonicNormalize '' K) ≠ ⊤ := by
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  letI : (Measure.hausdorffMeasure (3 : ℝ) : Measure E3).IsAddHaarMeasure := by
    simpa [hdim] using
      (inferInstance : (Measure.hausdorffMeasure
        (Module.finrank ℝ E3 : ℝ) : Measure E3).IsAddHaarMeasure)
  have hKfinite :
      (Measure.hausdorffMeasure (3 : ℝ) : Measure E3) K ≠ ⊤ :=
    hK.measure_ne_top
  have hle := gnomonicNormalize_lipschitz.hausdorffMeasure_image_le
    (d := (3 : ℝ)) (by norm_num) K
  have hfactor : ((2 : NNReal) : ENNReal) ^ (3 : ℝ) ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    exact ENNReal.coe_ne_top
  have hprod :
      ((2 : NNReal) : ENNReal) ^ (3 : ℝ) *
        (Measure.hausdorffMeasure (3 : ℝ) : Measure E3) K ≠ ⊤ :=
    ENNReal.mul_ne_top hfactor hKfinite
  exact ne_top_of_le_ne_top hprod hle

end Sphere3
