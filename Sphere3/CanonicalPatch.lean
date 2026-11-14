module

public import Sphere3.CanonicalCones
public import Sphere3.MeasureGrowth

@[expose] public section

/-!
# A relatively open patch in the difference of two regular spherical cones

For `0 < t < s`, the difference of the two nested canonical spherical
bodies contains a nonempty patch open in the relative topology of `S³`.
The construction below proves open/closed and measurable-set facts;
it does not infer positive 3-dimensional Hausdorff measure merely from
nonemptiness (which would be invalid for arbitrary subsets).
-/

noncomputable section

namespace Sphere3

open MeasureTheory

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The four defining affine-linear functions are continuous, and
hence the canonical cone is closed. -/
theorem canonicalCone_isClosed (t : ℝ) :
    IsClosed {x : E4 | CanonicalCone t (x 0) (x 1) (x 2) (x 3)} := by
  have h0 : IsClosed {x : E4 | 0 ≤ x 0 + x 1 + x 2 + t * x 3} :=
    isClosed_le continuous_const (by fun_prop)
  have h1 : IsClosed {x : E4 | 0 ≤ x 0 - x 1 - x 2 + t * x 3} :=
    isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {x : E4 | 0 ≤ -x 0 + x 1 - x 2 + t * x 3} :=
    isClosed_le continuous_const (by fun_prop)
  have h3 : IsClosed {x : E4 | 0 ≤ -x 0 - x 1 + x 2 + t * x 3} :=
    isClosed_le continuous_const (by fun_prop)
  simpa only [CanonicalCone, Set.setOf_and] using
    h0.inter (h1.inter (h2.inter h3))

/-- Strict inequalities define an open set in ambient `ℝ⁴`. -/
theorem canonicalConeInterior_isOpen (t : ℝ) :
    IsOpen {x : E4 | CanonicalConeInterior t (x 0) (x 1) (x 2) (x 3)} := by
  have h0 : IsOpen {x : E4 | 0 < x 0 + x 1 + x 2 + t * x 3} :=
    isOpen_lt continuous_const (by fun_prop)
  have h1 : IsOpen {x : E4 | 0 < x 0 - x 1 - x 2 + t * x 3} :=
    isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {x : E4 | 0 < -x 0 + x 1 - x 2 + t * x 3} :=
    isOpen_lt continuous_const (by fun_prop)
  have h3 : IsOpen {x : E4 | 0 < -x 0 - x 1 + x 2 + t * x 3} :=
    isOpen_lt continuous_const (by fun_prop)
  simpa only [CanonicalConeInterior, Set.setOf_and] using
    h0.inter (h1.inter (h2.inter h3))

/-- Each canonical spherical body is closed, hence Borel measurable. -/
theorem canonicalSphereBody_isClosed (t : ℝ) :
    IsClosed (canonicalSphereBody t) := by
  have hSphere : IsClosed {x : E4 | ‖x‖ = 1} :=
    isClosed_eq continuous_norm continuous_const
  simpa only [canonicalSphereBody, Set.setOf_and] using
    hSphere.inter (canonicalCone_isClosed t)

/-- The ambient open set consisting of points strictly inside the
larger cone and outside the smaller one. -/
def canonicalAmbientPatch (t s : ℝ) : Set E4 :=
  {x | CanonicalConeInterior s (x 0) (x 1) (x 2) (x 3) ∧
       ¬ CanonicalCone t (x 0) (x 1) (x 2) (x 3)}

theorem canonicalAmbientPatch_isOpen (t s : ℝ) :
    IsOpen (canonicalAmbientPatch t s) := by
  change IsOpen
    ({x : E4 | CanonicalConeInterior s (x 0) (x 1) (x 2) (x 3)} ∩
      {x : E4 | CanonicalCone t (x 0) (x 1) (x 2) (x 3)}ᶜ)
  exact (canonicalConeInterior_isOpen s).inter
    (canonicalCone_isClosed t).isOpen_compl

/-- A spherical patch, open relative to the unit sphere. -/
def canonicalSpherePatch (t s : ℝ) : Set E4 :=
  {x | ‖x‖ = 1 ∧ x ∈ canonicalAmbientPatch t s}

/-- The patch belongs to the larger body, and is disjoint from the
smaller body. -/
theorem canonicalSpherePatch_subset_difference (t s : ℝ) :
    canonicalSpherePatch t s ⊆
      canonicalSphereBody s \ canonicalSphereBody t := by
  intro x hx
  rcases hx with ⟨hxNorm, hxInterior, hxOutside⟩
  constructor
  · exact ⟨hxNorm, canonicalInterior_subset hxInterior⟩
  · intro hsmall
    exact hxOutside hsmall.2

/-- The patch is Borel measurable as an open set intersected with
an ambient unit sphere. -/
theorem canonicalSpherePatch_measurable (t s : ℝ) :
    MeasurableSet (canonicalSpherePatch t s) := by
  have hSphere : MeasurableSet {x : E4 | ‖x‖ = 1} :=
    (isClosed_eq continuous_norm continuous_const).measurableSet
  change MeasurableSet
    ({x : E4 | ‖x‖ = 1} ∩ canonicalAmbientPatch t s)
  exact hSphere.inter (canonicalAmbientPatch_isOpen t s).measurableSet

/-- Every proper canonical inclusion contains a nonempty measurable
relatively open patch on `S³`. -/
theorem canonicalSpherePatch_nonempty {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (canonicalSpherePatch t s).Nonempty := by
  obtain ⟨x, hxS, hxT, hxInterior⟩ :=
    canonicalSphereBody_strict_witness ht hts
  refine ⟨x, hxS.1, hxInterior, ?_⟩
  intro hCone
  exact hxT ⟨hxS.1, hCone⟩

/-- An ambient open neighborhood around the spherical witness is
contained in the strict difference of the four halfspace systems. -/
theorem canonicalAmbientPatch_contains_ball {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ (x : E4) (r : ℝ),
      ‖x‖ = 1 ∧ 0 < r ∧
      Metric.ball x r ⊆ canonicalAmbientPatch t s := by
  obtain ⟨x, hx⟩ := canonicalSpherePatch_nonempty ht hts
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (canonicalAmbientPatch_isOpen t s) x hx.2
  exact ⟨x, r, hx.1, hr, hball⟩

/-- The genuine spherical part of that ball lies in the patch.
This is a relative-open-neighborhood result, not yet a measure theorem. -/
theorem canonicalSpherePatch_contains_spherical_ball {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ (x : E4) (r : ℝ),
      ‖x‖ = 1 ∧ 0 < r ∧
      (Metric.ball x r ∩ {y : E4 | ‖y‖ = 1}) ⊆
        canonicalSpherePatch t s := by
  obtain ⟨x, r, hx, hr, hball⟩ :=
    canonicalAmbientPatch_contains_ball ht hts
  refine ⟨x, r, hx, hr, ?_⟩
  intro y hy
  exact ⟨hy.2, hball hy.1⟩

/-- Strict volume growth follows once the open spherical patch has
positive Hausdorff measure and the smaller body has finite measure.
The remaining positivity and finiteness statements are geometric facts,
not yet formalized in this project. -/
theorem canonicalHausdorff_lt_of_patch_pos {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hFin : (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) ≠ ⊤)
    (hPos : 0 < (Measure.hausdorffMeasure (3 : ℝ))
      (canonicalSpherePatch t s)) :
    (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) := by
  have hMeas : MeasurableSet (canonicalSpherePatch t s) :=
    canonicalSpherePatch_measurable t s
  have hAB : canonicalSphereBody t ⊆ canonicalSphereBody s :=
    canonicalSphereBody_mono ht (le_of_lt hts)
  have hUB : canonicalSpherePatch t s ⊆ canonicalSphereBody s :=
    fun x hx => (canonicalSpherePatch_subset_difference t s hx).1
  have hDisj : Disjoint (canonicalSphereBody t) (canonicalSpherePatch t s) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxT hxPatch
    exact (canonicalSpherePatch_subset_difference t s hxPatch).2 hxT
  exact measure_lt_of_positive_patch
    (Measure.hausdorffMeasure (3 : ℝ))
    hAB hUB hDisj hMeas hFin hPos


/-- It is enough to exhibit a positive-measure projection of the patch
onto a 3-dimensional Euclidean space.  The map must be 1-Lipschitz.
This is the intended route to eliminating `hPos` above. -/
theorem canonicalHausdorff_lt_of_projected_patch {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hFin : (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) ≠ ⊤)
    (p : E4 → EuclideanSpace ℝ (Fin 3))
    (hp : LipschitzWith 1 p)
    (hProjected : 0 < (Measure.hausdorffMeasure (3 : ℝ))
      (p '' canonicalSpherePatch t s)) :
    (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) := by
  have hPatch : 0 < (Measure.hausdorffMeasure (3 : ℝ))
      (canonicalSpherePatch t s) :=
    hausdorff_pos_of_lipschitz_image hp hProjected
  exact canonicalHausdorff_lt_of_patch_pos ht hts hFin hPatch

end Sphere3
