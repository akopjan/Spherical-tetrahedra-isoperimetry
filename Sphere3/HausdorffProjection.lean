module

public import Sphere3.CanonicalPatch
public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section

/-!
# Positive Hausdorff measure from an open projected patch

A key local comparison for codimension-one surfaces.  Instead of
identifying the unnormalized ambient Hausdorff measure with the
natural angular measure on the sphere, project an open surface patch
onto a three-dimensional Euclidean chart.  The projection is
1-Lipschitz, so it cannot increase Hausdorff measure.

The abstract lemma below reduces positivity to the open-image condition
using Mathlib's `LipschitzWith.hausdorffMeasure_image_le`.
-/

noncomputable section

namespace Sphere3

open MeasureTheory

/-- A positive measure for an open set in the projected space forces
positive Hausdorff measure of its 1-Lipschitz preimage patch. -/
theorem hausdorff_pos_of_open_subset_lipschitz_image
    {X Y : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {p : X → Y} (hp : LipschitzWith 1 p)
    {U : Set X} {O : Set Y}
    (hOpen : IsOpen O) (hNonempty : O.Nonempty)
    (hSubset : O ⊆ p '' U)
    [Measure.IsOpenPosMeasure
      (Measure.hausdorffMeasure (3 : ℝ) : Measure Y)] :
    0 < (Measure.hausdorffMeasure (3 : ℝ)) U := by
  have hO : 0 < (Measure.hausdorffMeasure (3 : ℝ) : Measure Y) O :=
    hOpen.measure_pos _ hNonempty
  have hImage : 0 < (Measure.hausdorffMeasure (3 : ℝ) : Measure Y) (p '' U) :=
    lt_of_lt_of_le hO (measure_mono hSubset)
  exact hausdorff_pos_of_lipschitz_image hp hImage

end Sphere3
