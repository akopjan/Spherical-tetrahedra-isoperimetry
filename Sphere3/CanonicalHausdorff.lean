module

public import Sphere3.CanonicalCones
public import Sphere3.MeasureGrowth

@[expose] public section

/-!
# The precise measure-theoretic bridge for the canonical family

The canonical bodies are nested, and the larger one has a point in its
interior outside the smaller.  To obtain strict volume monotonicity, we
must also prove (i) finiteness of the three-dimensional Hausdorff measure
of the smaller body, and (ii) positive measure of the difference.  This
file proves the final implication from those two explicit facts.

Both prerequisites are established in `Sphere3.GnomonicHausdorffFiniteness`.
-/

noncomputable section

namespace Sphere3

open MeasureTheory

private abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The set-theoretic difference in the canonical family has a point
on the sphere. Its positive three-dimensional measure is not inferred
from mere nonemptiness. -/
theorem canonicalSphereBody_difference_nonempty
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (canonicalSphereBody s \ canonicalSphereBody t).Nonempty := by
  obtain ⟨x, hxS, hxT, _⟩ := canonicalSphereBody_strict_witness ht hts
  exact ⟨x, hxS, hxT⟩

/-- The strict Hausdorff-volume inequality from its two measure-theoretic
prerequisites. -/
theorem canonicalSphereBody_measure_lt_of_patch
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hMeas : MeasurableSet (canonicalSphereBody t))
    (hFin : (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) ≠ ⊤)
    (hPos : 0 < (Measure.hausdorffMeasure (3 : ℝ))
      (canonicalSphereBody s \ canonicalSphereBody t)) :
    (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) := by
  exact measure_lt_of_positive_sdiff
    (Measure.hausdorffMeasure (3 : ℝ))
    (canonicalSphereBody_mono ht (le_of_lt hts)) hMeas hFin hPos

end Sphere3
