module

public import Sphere3.CanonicalPatch

@[expose] public section

/-!
# Strict four-dimensional volume growth for truncated canonical cones

The parameter family `CanonicalCone t` is increasing for `t > 0`.
A genuine open subset of the larger cone lies outside the smaller.
Unlike the spherical problem, ordinary four-dimensional Lebesgue volume
is positive on nonempty ambient open sets. Restricting to the closed
ball of radius two gives finite volume. We therefore obtain an
unconditional strict inequality for *truncated Euclidean cones*.

Strict monotonicity of three-dimensional spherical Hausdorff volume is
established separately in `Sphere3.GnomonicHausdorffFiniteness`.
-/

noncomputable section

namespace Sphere3

open MeasureTheory

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- Intersect the canonical cone with the closed Euclidean ball of radius two. -/
def canonicalTruncatedCone (t : ℝ) : Set E4 :=
  {x | ‖x‖ ≤ 2 ∧ CanonicalCone t (x 0) (x 1) (x 2) (x 3)}

/-- Truncated cones increase with the height parameter. -/
theorem canonicalTruncatedCone_mono {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    canonicalTruncatedCone t ⊆ canonicalTruncatedCone s := by
  intro x hx
  exact ⟨hx.1, canonicalCone_mono ht hts hx.2⟩

/-- A truncated cone is closed, hence compact in finite-dimensional space. -/
theorem canonicalTruncatedCone_isClosed (t : ℝ) :
    IsClosed (canonicalTruncatedCone t) := by
  change IsClosed ({x : E4 | ‖x‖ ≤ (2 : ℝ)} ∩
    {x : E4 | CanonicalCone t (x 0) (x 1) (x 2) (x 3)})
  exact (isClosed_le continuous_norm continuous_const).inter
    (canonicalCone_isClosed t)

theorem canonicalTruncatedCone_isCompact (t : ℝ) :
    IsCompact (canonicalTruncatedCone t) := by
  have hsubset : canonicalTruncatedCone t ⊆
      Metric.closedBall (0 : E4) 2 := by
    intro x hx
    change dist x 0 ≤ 2
    simpa only [dist_zero_right] using hx.1
  exact (isCompact_closedBall (0 : E4) 2).of_isClosed_subset
    (canonicalTruncatedCone_isClosed t) hsubset

/-- The separating patch is open in the *ambient* four-dimensional space. -/
def canonicalTruncatedPatch (t s : ℝ) : Set E4 :=
  canonicalAmbientPatch t s ∩ {x : E4 | ‖x‖ < 2}

theorem canonicalTruncatedPatch_isOpen (t s : ℝ) :
    IsOpen (canonicalTruncatedPatch t s) := by
  change IsOpen (canonicalAmbientPatch t s ∩ {x : E4 | ‖x‖ < 2})
  exact (canonicalAmbientPatch_isOpen t s).inter
    (isOpen_lt continuous_norm continuous_const)

theorem canonicalTruncatedPatch_nonempty {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (canonicalTruncatedPatch t s).Nonempty := by
  obtain ⟨x, hxBig, hxSmall, hxInterior⟩ :=
    canonicalSphereBody_strict_witness ht hts
  have hxOutside : ¬ CanonicalCone t (x 0) (x 1) (x 2) (x 3) := by
    intro h
    exact hxSmall ⟨hxBig.1, h⟩
  refine ⟨x, ?_⟩
  change x ∈ canonicalAmbientPatch t s ∩ {x : E4 | ‖x‖ < 2}
  refine ⟨⟨hxInterior, hxOutside⟩, ?_⟩
  change ‖x‖ < 2
  rw [hxBig.1]
  norm_num

theorem canonicalTruncatedPatch_subset {t s : ℝ} :
    canonicalTruncatedPatch t s ⊆ canonicalTruncatedCone s := by
  intro x hx
  exact ⟨le_of_lt hx.2, canonicalInterior_subset hx.1.1⟩

theorem canonicalTruncatedPatch_disjoint (t s : ℝ) :
    Disjoint (canonicalTruncatedCone t) (canonicalTruncatedPatch t s) := by
  apply Set.disjoint_left.mpr
  intro x hxSmall hxPatch
  exact hxPatch.1.2 hxSmall.2

/-- The four-dimensional Lebesgue volume of the truncated cones
is strictly increasing for `0 < t < s`. This is an unconditional
measure-theoretic result and does not use spherical Hausdorff measure. -/
theorem canonicalTruncatedCone_volume_strictMono {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (volume : Measure E4) (canonicalTruncatedCone t) <
      (volume : Measure E4) (canonicalTruncatedCone s) := by
  have hfinite : (volume : Measure E4) (canonicalTruncatedCone t) ≠ ⊤ :=
    (canonicalTruncatedCone_isCompact t).measure_ne_top
  have hopen : IsOpen (canonicalTruncatedPatch t s) :=
    canonicalTruncatedPatch_isOpen t s
  have hnonempty : (canonicalTruncatedPatch t s).Nonempty :=
    canonicalTruncatedPatch_nonempty ht hts
  exact measure_lt_of_open_patch volume
    (canonicalTruncatedCone_mono ht (le_of_lt hts))
    canonicalTruncatedPatch_subset
    (canonicalTruncatedPatch_disjoint t s)
    hopen hnonempty hfinite

/-- Strict growth under a scaled polar relation between four-dimensional
Lebesgue measure and three-dimensional Hausdorff measure. -/
theorem canonicalSphereBody_hausdorff_strict_of_scaled_polar
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (K : ENNReal)
    (hPolar : ∀ u : ℝ, 0 < u →
      (volume : Measure E4) (canonicalTruncatedCone u) =
        K * (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody u)) :
    (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) := by
  have hStrict := canonicalTruncatedCone_volume_strictMono ht hts
  by_contra hNot
  have hReverse :
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) ≤
        (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) :=
    le_of_not_gt hNot
  have hScaled :
      K * (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) ≤
        K * (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) := by
    gcongr
  rw [← hPolar s (lt_trans ht hts), ← hPolar t ht] at hScaled
  exact (not_le_of_gt hStrict) hScaled

/-- A convenient specialization of the scaled polar reduction to
`K = 4`.  For Mathlib's *unnormalized* Hausdorff measure, this scaling
should not be assumed correct without a normalization calculation.
The hypothesis is explicit; this theorem does not prove polar integration. -/
theorem canonicalSphereBody_hausdorff_strict_of_polar
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hPolar : ∀ u : ℝ, 0 < u →
      (volume : Measure E4) (canonicalTruncatedCone u) =
        (4 : ENNReal) *
          (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody u)) :
    (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) := by
  exact canonicalSphereBody_hausdorff_strict_of_scaled_polar
    ht hts (4 : ENNReal) hPolar
end Sphere3
