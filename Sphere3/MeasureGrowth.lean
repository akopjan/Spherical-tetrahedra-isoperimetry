module

public import Mathlib

@[expose] public section

/-!
# Measure growth from a positive patch

This module separates the measure-theoretic part of strict volume growth
from the geometry of the canonical tetrahedral family.  All assumptions
are explicit.  In particular, the positivity of a three-dimensional
Hausdorff patch on `S^3` is not silently assumed as a theorem of mathlib.
-/

noncomputable section

namespace Sphere3

open MeasureTheory

/-- A measurable positive patch disjoint from a finite-measure set makes
an inclusion strict in measure. -/
theorem measure_lt_of_positive_patch
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B U : Set X}
    (hAB : A ⊆ B) (hUB : U ⊆ B)
    (hdisj : Disjoint A U) (hUmeas : MeasurableSet U)
    (hAfin : μ A ≠ ⊤) (hUpos : 0 < μ U) :
    μ A < μ B := by
  have hAU : A ∪ U ⊆ B := Set.union_subset hAB hUB
  have hsum : μ (A ∪ U) = μ A + μ U :=
    measure_union hdisj hUmeas
  have hstrict : μ A < μ A + μ U :=
    ENNReal.lt_add_right hAfin (ne_of_gt hUpos)
  have hle : μ A + μ U ≤ μ B := by
    rw [← hsum]
    exact measure_mono hAU
  exact lt_of_lt_of_le hstrict hle


/-- An open nonempty patch makes an inclusion strict whenever the measure
is positive on open sets and finite on the smaller set. -/
theorem measure_lt_of_open_patch
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {A B U : Set X}
    (hAB : A ⊆ B) (hUB : U ⊆ B)
    (hdisj : Disjoint A U) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hAfin : μ A ≠ ⊤) :
    μ A < μ B := by
  exact measure_lt_of_positive_patch μ hAB hUB hdisj
    hUopen.measurableSet hAfin (hUopen.measure_pos μ hUne)

/-- Strict measure growth can be deduced using only the measurable smaller
set and the positive measure of the set-theoretic difference. -/
theorem measure_lt_of_positive_sdiff
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {A B : Set X}
    (hAB : A ⊆ B) (hAmeas : MeasurableSet A)
    (hAfin : μ A ≠ ⊤) (hDiffPos : 0 < μ (B \ A)) :
    μ A < μ B := by
  have hsplit : μ (B ∩ A) + μ (B \ A) = μ B := measure_inter_add_sdiff B hAmeas
  have hinter : B ∩ A = A := Set.inter_eq_right.mpr hAB
  rw [hinter] at hsplit
  have hlt : μ A < μ A + μ (B \ A) :=
    ENNReal.lt_add_right hAfin (ne_of_gt hDiffPos)
  exact lt_of_lt_of_le hlt (le_of_eq hsplit)

/-- A 1-Lipschitz image with positive Hausdorff measure implies
positive Hausdorff measure of the source. This is the projection
principle used for a patch of a hypersurface. -/
theorem hausdorff_pos_of_lipschitz_image
    {X Y : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : LipschitzWith 1 f)
    {s : Set X}
    (hpos : 0 < (Measure.hausdorffMeasure (3 : ℝ)) (f '' s)) :
    0 < (Measure.hausdorffMeasure (3 : ℝ)) s := by
  have hle := hf.hausdorffMeasure_image_le (d := (3 : ℝ)) (by norm_num) s
  have hle' : (Measure.hausdorffMeasure (3 : ℝ)) (f '' s) ≤
      (Measure.hausdorffMeasure (3 : ℝ)) s := by
    simpa using hle
  exact lt_of_lt_of_le hpos hle'

end Sphere3
