module

public import Sphere3.CanonicalFaceSurjectivity
public import Sphere3.HausdorffTwoProjection

@[expose] public section

/-!
# Two-dimensional Hausdorff finiteness of canonical faces

The actual canonical face is a chart image of a compact planar triangle.
This source establishes compactness of that triangle and the general
H^2-finiteness theorem for any Lipschitz image of a compact subset of R^2.

The required global Lipschitz bound for the normalized affine lift is
supplied in `Sphere3.CanonicalFaceGlobalLipschitz`.
-/

noncomputable section

open MeasureTheory

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The first-face planar triangle is an intersection of closed
half-planes, and hence closed. -/
theorem canonicalFacePlanarTriangle_isClosed (t : ℝ) :
    IsClosed (canonicalFacePlanarTriangle t) := by
  have h1 : IsClosed {z : ℝ × ℝ |
      -canonicalFaceRawAperture t / 2 ≤ z.1} :=
    isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {z : ℝ × ℝ |
      -canonicalFaceRawAperture t / 2 ≤ z.2} :=
    isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {z : ℝ × ℝ |
      z.1 + z.2 ≤ canonicalFaceRawAperture t / 2} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  change IsClosed
    ({z : ℝ × ℝ | -canonicalFaceRawAperture t / 2 ≤ z.1} ∩
      ({z : ℝ × ℝ | -canonicalFaceRawAperture t / 2 ≤ z.2} ∩
       {z : ℝ × ℝ | z.1 + z.2 ≤ canonicalFaceRawAperture t / 2}))
  exact h1.inter (h2.inter h3)

/-- The planar triangle is compact for *every* real t, even if t is
nonpositive. The inequalities themselves bound each coordinate. -/
theorem canonicalFacePlanarTriangle_isCompact (t : ℝ) :
    IsCompact (canonicalFacePlanarTriangle t) := by
  let a : ℝ := canonicalFaceRawAperture t
  have hbox : canonicalFacePlanarTriangle t ⊆
      (Set.Icc (-a / 2) a ×ˢ Set.Icc (-a / 2) a) := by
    intro z hz
    rcases hz with ⟨hp, hq, hpq⟩
    change z.1 ∈ Set.Icc (-a / 2) a ∧
      z.2 ∈ Set.Icc (-a / 2) a
    constructor
    · exact ⟨hp, by linarith⟩
    · exact ⟨hq, by linarith⟩
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (canonicalFacePlanarTriangle_isClosed t) hbox

/-- In the two-dimensional real vector space R×R, the raw Hausdorff
H^2 measure is an additive Haar measure. -/
theorem realProdTwo_hausdorff_isAddHaar :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  simpa [hdim] using
    (inferInstance : (Measure.hausdorffMeasure
      (Module.finrank ℝ (ℝ × ℝ) : ℝ) : Measure (ℝ × ℝ)).IsAddHaarMeasure)

/-- The Lipschitz image of any compact subset of the two-dimensional
parameter space has finite *raw* ambient H^2 measure. -/
theorem lipschitz_compact_planar_hausdorffTwo_finite
    {Y : Type*} [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : NNReal} {f : (ℝ × ℝ) → Y}
    (hLip : LipschitzWith K f)
    {A : Set (ℝ × ℝ)} (hCompact : IsCompact A) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure Y) (f '' A) ≠ ⊤ := by
  letI : (Measure.hausdorffMeasure (2 : ℝ) : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    realProdTwo_hausdorff_isAddHaar
  have hAFin :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure (ℝ × ℝ)) A ≠ ⊤ :=
    hCompact.measure_ne_top
  have hFactor : ((K : ENNReal) ^ (2 : ℝ)) ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    exact ENNReal.coe_ne_top
  have hProd : (K : ENNReal) ^ (2 : ℝ) *
      (Measure.hausdorffMeasure (2 : ℝ) : Measure (ℝ × ℝ)) A ≠ ⊤ :=
    ENNReal.mul_ne_top hFactor hAFin
  have hLE := hLip.hausdorffMeasure_image_le
    (d := (2 : ℝ)) (by norm_num) A
  exact ne_top_of_le_ne_top hProd hLE

/-- The only remaining hypothesis is a Lipschitz bound for the
explicit normalized first-face lift. The full face is exactly its
compact-domain image (proved in `CanonicalFaceSurjectivity`). -/
theorem canonical_first_face_hausdorff_finite_of_lipschitz
    (t : ℝ) (ht : 0 < t)
    (K : NNReal)
    (hLip : LipschitzWith K
      (fun z : ℝ × ℝ => canonicalFacePoint t z.1 z.2)) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
      ((SphericalTetrahedron.canonicalTetrahedron t ht).face 0) ≠ ⊤ := by
  rw [canonicalTetrahedron_first_face_eq_chart t ht]
  exact lipschitz_compact_planar_hausdorffTwo_finite hLip
    (canonicalFacePlanarTriangle_isCompact t)

end Sphere3
