module

public import SphericalTetrahedron.CanonicalRealization
public import Sphere3.CanonicalFaceScale

@[expose] public section

/-!
# Exact coordinates for one canonical spherical face

This file constructs a nonvanishing affine lift of the first face of the
canonical tetrahedron.  Unlike the older spherical-excess approach, the lift
makes the common two-dimensional metric of the *entire* regular family
explicit.  The height-dependent normal `(-t,-t,-t,3)` is perpendicular to
all tangent vectors `(p,q,-p-q,0)`, which makes the normalized inner
products independent of the height parameter.

Area-measure comparison via this chart is completed in
`Sphere3.CanonicalFaceOpenPatchProjection` and
`SphericalTetrahedron.CanonicalFaceHausdorffStrict`.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- Length of the raw normal-axis vector `(-t,-t,-t,3)`. -/
def canonicalFaceHeight (t : ℝ) : ℝ :=
  Real.sqrt (9 + 3 * t ^ 2)

theorem canonicalFaceHeight_pos (t : ℝ) :
    0 < canonicalFaceHeight t := by
  unfold canonicalFaceHeight
  exact Real.sqrt_pos.2 (by positivity)

theorem canonicalFaceHeight_sq (t : ℝ) :
    canonicalFaceHeight t ^ 2 = 9 + 3 * t ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- The positive definite quadratic form for the fixed metric on the
common tangent plane `u₀ + u₁ + u₂ = 0`. -/
def canonicalFaceQ (p q : ℝ) : ℝ :=
  1 + p ^ 2 + q ^ 2 + (p + q) ^ 2

theorem canonicalFaceQ_pos (p q : ℝ) :
    0 < canonicalFaceQ p q := by
  unfold canonicalFaceQ
  positivity

/-- The unnormalized chart for the face `n₀ · x = 0`.
The other three normal inequalities become `2hp+4t ≥ 0`,
`2hq+4t ≥ 0`, and `-2h(p+q)+4t ≥ 0`. -/
def canonicalFaceRawLift (t p q : ℝ) : E4 :=
  !₂[canonicalFaceHeight t * p - t,
     canonicalFaceHeight t * q - t,
     -canonicalFaceHeight t * (p + q) - t,
     3]

/-- The raw chart does not vanish: its fourth coordinate is three. -/
theorem canonicalFaceRawLift_ne_zero (t p q : ℝ) :
    canonicalFaceRawLift t p q ≠ 0 := by
  intro h
  have hfourth := congrArg (fun x : E4 => x 3) h
  norm_num [canonicalFaceRawLift] at hfourth

theorem canonicalFaceRawLift_norm_pos (t p q : ℝ) :
    0 < ‖canonicalFaceRawLift t p q‖ :=
  (norm_pos_iff).2 (canonicalFaceRawLift_ne_zero t p q)

/-- The first supporting hyperplane contains the whole chart. -/
theorem canonicalFaceRawLift_first_facet (t p q : ℝ) :
    (canonicalFaceRawLift t p q) 0 +
      (canonicalFaceRawLift t p q) 1 +
      (canonicalFaceRawLift t p q) 2 +
      t * (canonicalFaceRawLift t p q) 3 = 0 := by
  simp [canonicalFaceRawLift]
  ring

/-- Three remaining facet evaluations, in the original cone
normalization.  No trigonometric formulas are used. -/
theorem canonicalFaceRawLift_second_facet (t p q : ℝ) :
    (canonicalFaceRawLift t p q) 0 -
      (canonicalFaceRawLift t p q) 1 -
      (canonicalFaceRawLift t p q) 2 +
      t * (canonicalFaceRawLift t p q) 3 =
        2 * canonicalFaceHeight t * p + 4 * t := by
  simp [canonicalFaceRawLift]
  ring

theorem canonicalFaceRawLift_third_facet (t p q : ℝ) :
    -(canonicalFaceRawLift t p q) 0 +
      (canonicalFaceRawLift t p q) 1 -
      (canonicalFaceRawLift t p q) 2 +
      t * (canonicalFaceRawLift t p q) 3 =
        2 * canonicalFaceHeight t * q + 4 * t := by
  simp [canonicalFaceRawLift]
  ring

theorem canonicalFaceRawLift_fourth_facet (t p q : ℝ) :
    -(canonicalFaceRawLift t p q) 0 -
      (canonicalFaceRawLift t p q) 1 +
      (canonicalFaceRawLift t p q) 2 +
      t * (canonicalFaceRawLift t p q) 3 =
        -2 * canonicalFaceHeight t * (p + q) + 4 * t := by
  simp [canonicalFaceRawLift]
  ring

/-- Elementary facet inequalities in the two free chart coordinates. -/
def canonicalFaceRawRegion (t : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ 2 * canonicalFaceHeight t * z.1 + 4 * t ∧
       0 ≤ 2 * canonicalFaceHeight t * z.2 + 4 * t ∧
       0 ≤ -2 * canonicalFaceHeight t * (z.1 + z.2) + 4 * t}

/-- The four cone inequalities are equivalent to membership in the raw
planar triangle, because the first inequality is identically zero. -/
theorem canonicalFaceRawLift_cone_iff (t p q : ℝ) :
    CanonicalCone t
      ((canonicalFaceRawLift t p q) 0)
      ((canonicalFaceRawLift t p q) 1)
      ((canonicalFaceRawLift t p q) 2)
      ((canonicalFaceRawLift t p q) 3) ↔
        (p, q) ∈ canonicalFaceRawRegion t := by
  rw [CanonicalCone, canonicalFaceRawRegion, Set.mem_setOf_eq,
    canonicalFaceRawLift_first_facet,
    canonicalFaceRawLift_second_facet,
    canonicalFaceRawLift_third_facet,
    canonicalFaceRawLift_fourth_facet]
  simp

/-- The bilinear inner-product identity is independent of t except
for the single positive global scale `9+3t²`. -/
theorem canonicalFaceRawLift_inner (t p q r s : ℝ) :
    ⟪canonicalFaceRawLift t p q, canonicalFaceRawLift t r s⟫_ℝ =
      (9 + 3 * t ^ 2) *
        (1 + p * r + q * s + (p + q) * (r + s)) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [canonicalFaceRawLift, dotProduct, Fin.sum_univ_four]
  ring_nf
  rw [canonicalFaceHeight_sq]
  ring

/-- A particularly simple norm formula for the affine lift. -/
theorem canonicalFaceRawLift_norm_sq (t p q : ℝ) :
    ‖canonicalFaceRawLift t p q‖ ^ 2 =
      (9 + 3 * t ^ 2) * canonicalFaceQ p q := by
  calc
    ‖canonicalFaceRawLift t p q‖ ^ 2 =
        ⟪canonicalFaceRawLift t p q, canonicalFaceRawLift t p q⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = (9 + 3 * t ^ 2) * canonicalFaceQ p q := by
      rw [canonicalFaceRawLift_inner]
      unfold canonicalFaceQ
      ring

/-- As a consequence, the norm factors as the common height times the
square root of the same quadratic form for all t. -/
theorem canonicalFaceRawLift_norm (t p q : ℝ) :
    ‖canonicalFaceRawLift t p q‖ =
      canonicalFaceHeight t * Real.sqrt (canonicalFaceQ p q) := by
  have hnorm : ‖canonicalFaceRawLift t p q‖ ^ 2 =
      (canonicalFaceHeight t * Real.sqrt (canonicalFaceQ p q)) ^ 2 := by
    rw [canonicalFaceRawLift_norm_sq, ← canonicalFaceHeight_sq,
      mul_pow, Real.sq_sqrt (canonicalFaceQ_pos p q).le]
  have hnonneg : 0 ≤ canonicalFaceHeight t *
      Real.sqrt (canonicalFaceQ p q) :=
    mul_nonneg (canonicalFaceHeight_pos t).le (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (canonicalFaceRawLift t p q)]

/-- The actual unit-spherical chart. -/
def canonicalFacePoint (t p q : ℝ) : E4 :=
  ‖canonicalFaceRawLift t p q‖⁻¹ • canonicalFaceRawLift t p q

theorem canonicalFacePoint_norm (t p q : ℝ) :
    ‖canonicalFacePoint t p q‖ = 1 := by
  have hp := canonicalFaceRawLift_norm_pos t p q
  unfold canonicalFacePoint
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ hp.ne'

/-- The entire Gram kernel of the normalized face chart is independent
of the moving face plane. The denominator and numerator are explicitly
positive/finitely valued, and no measure normalization is used. -/
theorem canonicalFacePoint_inner (t p q r s : ℝ) :
    ⟪canonicalFacePoint t p q, canonicalFacePoint t r s⟫_ℝ =
      (1 + p * r + q * s + (p + q) * (r + s)) /
      (Real.sqrt (canonicalFaceQ p q) *
       Real.sqrt (canonicalFaceQ r s)) := by
  have hh := canonicalFaceHeight_pos t
  have hp := Real.sqrt_pos.2 (canonicalFaceQ_pos p q)
  have hr := Real.sqrt_pos.2 (canonicalFaceQ_pos r s)
  unfold canonicalFacePoint
  rw [real_inner_smul_left, real_inner_smul_right,
    canonicalFaceRawLift_inner,
    canonicalFaceRawLift_norm t p q,
    canonicalFaceRawLift_norm t r s]
  rw [← canonicalFaceHeight_sq]
  field_simp [hh.ne', hp.ne', hr.ne']

/-- Normalized face charts in different moving hyperplanes have identical
Gram kernels, hence identical intrinsic Euclidean metrics. -/
theorem canonicalFacePoint_inner_height_invariant
    (t s p q r v : ℝ) :
    ⟪canonicalFacePoint t p q, canonicalFacePoint t r v⟫_ℝ =
      ⟪canonicalFacePoint s p q, canonicalFacePoint s r v⟫_ℝ := by
  rw [canonicalFacePoint_inner, canonicalFacePoint_inner]

/-- Pairwise chordal distances are independent of the canonical height.
This is the key ingredient for a measure-preserving isometry between
corresponding canonical faces. -/
theorem canonicalFacePoint_dist_height_invariant
    (t s p q r v : ℝ) :
    dist (canonicalFacePoint t p q) (canonicalFacePoint t r v) =
      dist (canonicalFacePoint s p q) (canonicalFacePoint s r v) := by
  have hinner := canonicalFacePoint_inner_height_invariant t s p q r v
  have hSq :
      dist (canonicalFacePoint t p q) (canonicalFacePoint t r v) ^ 2 =
      dist (canonicalFacePoint s p q) (canonicalFacePoint s r v) ^ 2 := by
    simp only [dist_eq_norm]
    rw [norm_sub_sq_real, norm_sub_sq_real]
    rw [canonicalFacePoint_norm, canonicalFacePoint_norm,
      canonicalFacePoint_norm, canonicalFacePoint_norm, hinner]
  have hd1 : 0 ≤ dist (canonicalFacePoint t p q) (canonicalFacePoint t r v) := dist_nonneg
  have hd2 : 0 ≤ dist (canonicalFacePoint s p q) (canonicalFacePoint s r v) := dist_nonneg
  nlinarith

/-- The spherical point belongs to the first canonical face precisely
when its parameters satisfy the three planar inequalities. -/
theorem canonicalFacePoint_mem_first_face_iff
    (t : ℝ) (ht : 0 < t) (p q : ℝ) :
    canonicalFacePoint t p q ∈
      (SphericalTetrahedron.canonicalTetrahedron t ht).face (0 : Fin 4) ↔
        (p, q) ∈ canonicalFaceRawRegion t := by
  have hp := canonicalFaceRawLift_norm_pos t p q
  have hscale : 0 < ‖canonicalFaceRawLift t p q‖⁻¹ := inv_pos.mpr hp
  have hraw := canonicalFaceRawLift_cone_iff t p q
  have hfirst := canonicalFaceRawLift_first_facet t p q
  change ((‖canonicalFacePoint t p q‖ = 1 ∧
    (∀ i, 0 ≤ ⟪(SphericalTetrahedron.canonicalTetrahedron t ht).normal i,
          canonicalFacePoint t p q⟫_ℝ)) ∧
    ⟪(SphericalTetrahedron.canonicalTetrahedron t ht).normal 0,
      canonicalFacePoint t p q⟫_ℝ = 0) ↔ _
  -- The facet-normal conversion uses the previously proven exact cone iff.
  have hNormal (i : Fin 4) :
      0 ≤ ⟪(SphericalTetrahedron.canonicalTetrahedron t ht).normal i,
        canonicalFacePoint t p q⟫_ℝ ↔
      0 ≤ ⟪SphericalTetrahedron.canonicalRawNormal t i,
        canonicalFaceRawLift t p q⟫_ℝ := by
    rw [SphericalTetrahedron.canonicalTetrahedron_normal_nonneg_iff]
    unfold canonicalFacePoint
    rw [real_inner_smul_right]
    exact mul_nonneg_iff_of_pos_left hscale
  have hZero :
      ⟪(SphericalTetrahedron.canonicalTetrahedron t ht).normal 0,
        canonicalFacePoint t p q⟫_ℝ = 0 := by
    unfold canonicalFacePoint
    rw [real_inner_smul_right]
    have hraw0 :
        ⟪SphericalTetrahedron.canonicalRawNormal t 0,
          canonicalFaceRawLift t p q⟫_ℝ = 0 := by
      have hl : canonicalFaceRawLift t p q =
          WithLp.toLp 2 (canonicalFaceRawLift t p q).ofLp := rfl
      conv_lhs => rw [hl, SphericalTetrahedron.canonicalRawNormal, EuclideanSpace.inner_toLp_toLp]
      simp [Sphere3.canonicalNormalMatrix, dotProduct, Fin.sum_univ_four]
      linarith [hfirst]
    change ‖canonicalFaceRawLift t p q‖⁻¹ *
      ⟪SphericalTetrahedron.canonicalUnitNormal t 0,
        canonicalFaceRawLift t p q⟫_ℝ = 0
    rw [SphericalTetrahedron.canonicalUnitNormal, real_inner_smul_left,
      hraw0, mul_zero, mul_zero]
  constructor
  · rintro ⟨⟨_hnorm, hNormals⟩, _hZero⟩
    apply hraw.mp
    apply (SphericalTetrahedron.canonicalRawNormal_cone_iff t _).mp
    intro i
    exact (hNormal i).mp (hNormals i)
  · intro hr
    refine ⟨⟨canonicalFacePoint_norm t p q, ?_⟩, hZero⟩
    have hCone := hraw.mpr hr
    have hRawNormals :=
      (SphericalTetrahedron.canonicalRawNormal_cone_iff t _).mpr hCone
    intro i
    exact (hNormal i).mpr (hRawNormals i)

end Sphere3
