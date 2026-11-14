module

public import Sphere3.CanonicalFaceNested
public import Sphere3.GnomonicHausdorffFiniteness

@[expose] public section

/-!
# Surjectivity of the explicit canonical face chart

The forward implication was proved in `CanonicalFaceCoordinates`. Here the
inverse is written explicitly for every point on the first face. Positive
fourth coordinate is essential and follows from strict positivity of t.

The resulting set equality expresses the *actual* first face in the
benchmark as the image of the closed planar triangle. This removes the
need to reason by analogy with an auxiliary spherical model.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- Rational inverse of the face chart on the positive fourth hemisphere.
The inverse makes sense for arbitrary vectors with nonzero fourth coordinate;
the face equation is used in the verification. -/
def canonicalFaceInverse (t : ℝ) (x : E4) : ℝ × ℝ :=
  ((3 * x 0 + t * x 3) / (canonicalFaceHeight t * x 3),
   (3 * x 1 + t * x 3) / (canonicalFaceHeight t * x 3))

/-- Inverse chart recovers a positive scalar multiple of the input. -/
theorem canonicalFaceRawLift_inverse
    (t : ℝ) (x : E4)
    (hx3 : x 3 ≠ 0)
    (hFace : x 0 + x 1 + x 2 + t * x 3 = 0) :
    canonicalFaceRawLift t (canonicalFaceInverse t x).1
        (canonicalFaceInverse t x).2 = (3 / x 3) • x := by
  have hh : canonicalFaceHeight t ≠ 0 := (canonicalFaceHeight_pos t).ne'
  have hden : canonicalFaceHeight t * x 3 ≠ 0 := mul_ne_zero hh hx3
  ext i
  fin_cases i <;>
    simp [canonicalFaceRawLift, canonicalFaceInverse] <;>
    field_simp [hh, hx3, hden] <;>
    nlinarith [hFace]

/-- Normalizing the raw inverse chart gives the original unit vector. -/
theorem canonicalFacePoint_inverse
    (t : ℝ) (x : E4)
    (hUnit : ‖x‖ = 1)
    (hx3 : 0 < x 3)
    (hFace : x 0 + x 1 + x 2 + t * x 3 = 0) :
    canonicalFacePoint t (canonicalFaceInverse t x).1
      (canonicalFaceInverse t x).2 = x := by
  have hraw := canonicalFaceRawLift_inverse t x hx3.ne' hFace
  have hscale : 0 < 3 / x 3 := div_pos (by norm_num) hx3
  unfold canonicalFacePoint
  rw [hraw, norm_smul, Real.norm_eq_abs, abs_of_pos hscale,
    hUnit, mul_one, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]

/-- The scalar equation for the first face, stated directly in the four
coordinates, follows from vanishing of the first unit normal's dot product. -/
theorem canonicalTetrahedron_first_face_equation
    (t : ℝ) (ht : 0 < t) (x : E4)
    (hx : x ∈ (SphericalTetrahedron.canonicalTetrahedron t ht).face 0) :
    x 0 + x 1 + x 2 + t * x 3 = 0 := by
  have hunitNormal := hx.2
  change ⟪SphericalTetrahedron.canonicalUnitNormal t 0, x⟫_ℝ = 0
    at hunitNormal
  unfold SphericalTetrahedron.canonicalUnitNormal at hunitNormal
  rw [real_inner_smul_left] at hunitNormal
  have hs : Real.sqrt (3 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  have hcoef : (Real.sqrt (3 + t ^ 2))⁻¹ ≠ 0 := inv_ne_zero hs
  have hraw :
      ⟪SphericalTetrahedron.canonicalRawNormal t 0, x⟫_ℝ = 0 := by
    exact (mul_eq_zero.mp hunitNormal).resolve_left hcoef
  have hxw : x = WithLp.toLp 2 x.ofLp := rfl
  rw [hxw, SphericalTetrahedron.canonicalRawNormal, EuclideanSpace.inner_toLp_toLp] at hraw
  simp [Sphere3.canonicalNormalMatrix, dotProduct, Fin.sum_univ_four] at hraw
  linarith [hraw]

/-- The first face lies in the positive fourth hemisphere. -/
theorem canonicalTetrahedron_first_face_height_pos
    (t : ℝ) (ht : 0 < t) (x : E4)
    (hx : x ∈ (SphericalTetrahedron.canonicalTetrahedron t ht).face 0) :
    0 < x 3 := by
  have hbody : x ∈ canonicalSphereBody t := by
    rw [← SphericalTetrahedron.canonicalTetrahedron_body_eq t ht]
    exact hx.1
  exact canonicalSphereBody_height_pos t ht x hbody

/-- Every point of the actual first face is hit by the explicit chart,
with a parameter pair inside the canonical planar triangle. -/
theorem canonicalTetrahedron_first_face_eq_chart
    (t : ℝ) (ht : 0 < t) :
    (SphericalTetrahedron.canonicalTetrahedron t ht).face 0 =
      (fun z : ℝ × ℝ => canonicalFacePoint t z.1 z.2) ''
        canonicalFacePlanarTriangle t := by
  rw [← canonicalFaceRawRegion_eq_triangle]
  ext x
  constructor
  · intro hx
    let z : ℝ × ℝ := canonicalFaceInverse t x
    have hunit : ‖x‖ = 1 := hx.1.1
    have hpos := canonicalTetrahedron_first_face_height_pos t ht x hx
    have heq := canonicalTetrahedron_first_face_equation t ht x hx
    have hchart : canonicalFacePoint t z.1 z.2 = x :=
      canonicalFacePoint_inverse t x hunit hpos heq
    have hz : z ∈ canonicalFaceRawRegion t := by
      apply (canonicalFacePoint_mem_first_face_iff t ht z.1 z.2).mp
      rw [hchart]
      exact hx
    exact ⟨z, hz, hchart⟩
  · rintro ⟨z, hz, rfl⟩
    exact (canonicalFacePoint_mem_first_face_iff t ht z.1 z.2).mpr hz

end Sphere3
