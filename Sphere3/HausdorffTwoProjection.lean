module

public import Sphere3.GnomonicLipschitz
public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section

/-!
# Positivity of Hausdorff H^2 on a surface patch from a coordinate projection

Coordinate restriction from Euclidean R^4 onto its first two coordinates is
1-Lipschitz. A subset of a surface whose coordinate projection includes a
nonempty open planar set has strictly positive *unnormalized* Hausdorff
2-measure, since planar full-dimensional Hausdorff measure is positive on
nonempty open sets.

This lemma does not require a surface integration formula or change-of-
variables theorem. No custom normalization constant enters.
-/

noncomputable section

open MeasureTheory

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A fixed coordinate projection, suitable after rotating a face so its
tangent plane is transverse to the first two coordinate axes. -/
def canonicalTwoProjection (x : E4) : E2 := !₂[x 0, x 1]

/-- The square norm of the first two coordinates cannot exceed the full
Euclidean square norm. -/
theorem canonicalTwoProjection_norm_le (x : E4) :
    ‖canonicalTwoProjection x‖ ≤ ‖x‖ := by
  have hsq : ‖canonicalTwoProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (canonicalTwoProjection x),
      EuclideanSpace.real_norm_sq_eq x, Fin.sum_univ_two, Fin.sum_univ_four]
    change (x 0) ^ 2 + (x 1) ^ 2 ≤ (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2
    nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]
  nlinarith [norm_nonneg (canonicalTwoProjection x), norm_nonneg x]

theorem canonicalTwoProjection_sub (x y : E4) :
    canonicalTwoProjection (x - y) =
      canonicalTwoProjection x - canonicalTwoProjection y := by
  ext i
  fin_cases i <;> simp [canonicalTwoProjection, Pi.sub_apply]

/-- Coordinate projection is nonexpansive. -/
theorem canonicalTwoProjection_lipschitz :
    LipschitzWith 1 canonicalTwoProjection := by
  apply LipschitzWith.mk_one
  intro x y
  have h := canonicalTwoProjection_norm_le (x - y)
  rw [canonicalTwoProjection_sub] at h
  simpa only [dist_eq_norm] using h

/-- The full-dimensional Hausdorff measure on E2 is an additive Haar
measure, and therefore strictly positive on all nonempty open sets. -/
theorem euclideanTwo_hausdorff_isOpenPos :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E2).IsOpenPosMeasure := by
  have hdim : Module.finrank ℝ E2 = 2 := by simp
  letI : (Measure.hausdorffMeasure (2 : ℝ) : Measure E2).IsAddHaarMeasure := by
    simpa [hdim] using
      (inferInstance : (Measure.hausdorffMeasure
        (Module.finrank ℝ E2 : ℝ) : Measure E2).IsAddHaarMeasure)
  infer_instance

/-- A two-dimensional surface patch has positive raw Hausdorff measure
if the ordinary coordinate projection contains a nonempty open set. -/
theorem canonicalTwoProjection_patch_hausdorff_pos
    {U : Set E4} {O : Set E2}
    (hOopen : IsOpen O) (hOne : O.Nonempty)
    (hSubset : O ⊆ canonicalTwoProjection '' U) :
    0 < (Measure.hausdorffMeasure (2 : ℝ) : Measure E4) U := by
  letI : (Measure.hausdorffMeasure (2 : ℝ) : Measure E2).IsOpenPosMeasure :=
    euclideanTwo_hausdorff_isOpenPos
  have hPositiveImage :
      0 < (Measure.hausdorffMeasure (2 : ℝ) : Measure E2)
        (canonicalTwoProjection '' U) := by
    exact lt_of_lt_of_le (hOopen.measure_pos _ hOne)
      (measure_mono hSubset)
  have hle := canonicalTwoProjection_lipschitz.hausdorffMeasure_image_le
    (d := (2 : ℝ)) (by norm_num) U
  have hle' :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E2)
        (canonicalTwoProjection '' U) ≤
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4) U := by
    simpa using hle
  exact lt_of_lt_of_le hPositiveImage hle'

end Sphere3
