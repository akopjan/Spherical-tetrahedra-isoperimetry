module

public import Sphere3.MeasureGrowth
public import Mathlib

@[expose] public section

/-!
# Positive Hausdorff measure under a map with a Lipschitz inverse

This reduction avoids comparing ambient Hausdorff measure to the
radially disintegrated spherical measure. It applies to the inverse
gnomonic map on a bounded patch.
-/

noncomputable section

namespace Sphere3

open MeasureTheory

/-- A Lipschitz left inverse on the image of a positive-measure set
forces its image to have positive Hausdorff measure of the same dimension.
This works with *unnormalized* Hausdorff measure on both spaces. -/
theorem hausdorff_pos_image_of_lipschitz_left_inverse
    {X Y : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (d : ℝ) (hd : 0 ≤ d)
    (f : X → Y) (g : Y → X) (C : NNReal) (S : Set X)
    (hg : ∀ x ∈ S, g (f x) = x)
    (hLip : LipschitzOnWith C g (f '' S))
    (hPos : 0 < (Measure.hausdorffMeasure d) S) :
    0 < (Measure.hausdorffMeasure d) (f '' S) := by
  have hImage : g '' (f '' S) = S := by
    ext x
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      simpa [hg u hu] using hu
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hg x hx⟩
  have hMeasure := hLip.hausdorffMeasure_image_le hd
  rw [hImage] at hMeasure
  by_contra hNot
  have hZero : (Measure.hausdorffMeasure d) (f '' S) = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hNot)
  rw [hZero] at hMeasure
  simp only [mul_zero] at hMeasure
  exact (not_le_of_gt hPos) hMeasure


/-- Strict increase of *the same unnormalized Hausdorff measure* when a
larger set contains a disjoint measurable patch whose parameter-domain
preimage has positive Hausdorff measure and whose chart has a Lipschitz
left inverse. The main geometric task is to instantiate this lemma for
the gnomonic chart of spherical tetrahedra. -/
theorem hausdorff_strict_of_bilipschitz_patch
    {X Y : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (d : ℝ) (hd : 0 ≤ d)
    (A B U : Set Y) (P : Set X)
    (hAB : A ⊆ B) (hUB : U ⊆ B)
    (hDisjoint : Disjoint A U) (hUmeas : MeasurableSet U)
    (hAfin : (Measure.hausdorffMeasure d) A ≠ ⊤)
    (f : X → Y) (g : Y → X) (C : NNReal)
    (hImage : f '' P = U)
    (hLeft : ∀ x ∈ P, g (f x) = x)
    (hLip : LipschitzOnWith C g (f '' P))
    (hPpos : 0 < (Measure.hausdorffMeasure d) P) :
    (Measure.hausdorffMeasure d) A <
      (Measure.hausdorffMeasure d) B := by
  have hPosImage := hausdorff_pos_image_of_lipschitz_left_inverse
    d hd f g C P hLeft hLip hPpos
  rw [hImage] at hPosImage
  exact measure_lt_of_positive_patch
    (Measure.hausdorffMeasure d) hAB hUB hDisjoint hUmeas hAfin hPosImage

end Sphere3
