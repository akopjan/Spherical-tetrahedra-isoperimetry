module

public import Sphere3.CanonicalFaceChartInjective
public import Sphere3.HausdorffTwoProjection

@[expose] public section

/-!
# Open projection of the actual face difference

After rotating the larger first face to the fixed plane at t=0,
its first two ambient coordinates are

   k(p,q) = (p,q)/sqrt(1+p²+q²+(p+q)²).

The disk chart k is an open map (proved in CanonicalFaceDiskChart).
The canonical planar difference patch is nonempty and open, and by
injectivity of the face chart its spherical image lies in the actual
face difference. This constructs the open projection witness required for strictly
increasing raw Hausdorff area.
-/

noncomputable section

namespace Sphere3

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The canonical homeomorphism between the planar product and E2. -/
def canonicalPlanarToEuclidean : (ℝ × ℝ) ≃ₜ E2 where
  toEquiv := {
    toFun := fun z => !₂[z.1, z.2]
    invFun := fun x => (x 0, x 1)
    left_inv := by intro z; rfl
    right_inv := by
      intro x
      ext i
      fin_cases i <;> rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Two-coordinate projection of the chart after the ambient rotation
is the canonical fixed-plane disk chart, independently of t. -/
theorem canonicalTwoProjection_rotated_face_point (t : ℝ) (z : ℝ × ℝ) :
    canonicalTwoProjection
      (canonicalFaceRotation t 0 (canonicalFacePoint t z.1 z.2)) =
        canonicalPlanarToEuclidean (canonicalFaceDiskMap z) := by
  rw [canonicalFaceRotation_chart]
  have hh : canonicalFaceHeight (0 : ℝ) = 3 := by
    norm_num [canonicalFaceHeight]
  have hq : Real.sqrt (canonicalFaceQ z.1 z.2) ≠ 0 :=
    (Real.sqrt_pos.2 (canonicalFaceQ_pos z.1 z.2)).ne'
  have hnorm : ‖canonicalFaceRawLift 0 z.1 z.2‖ =
      3 * Real.sqrt (canonicalFaceQ z.1 z.2) := by
    simpa [hh] using canonicalFaceRawLift_norm 0 z.1 z.2
  ext i
  fin_cases i
  · change ‖canonicalFaceRawLift 0 z.1 z.2‖⁻¹ *
        (canonicalFaceHeight 0 * z.1 - 0) =
          z.1 / Real.sqrt (canonicalFaceDiskQ z)
    rw [hnorm, hh]
    change (3 * Real.sqrt (canonicalFaceQ z.1 z.2))⁻¹ *
      (3 * z.1 - 0) = z.1 / Real.sqrt (canonicalFaceQ z.1 z.2)
    field_simp [hq]
    ring
  · change ‖canonicalFaceRawLift 0 z.1 z.2‖⁻¹ *
        (canonicalFaceHeight 0 * z.2 - 0) =
          z.2 / Real.sqrt (canonicalFaceDiskQ z)
    rw [hnorm, hh]
    change (3 * Real.sqrt (canonicalFaceQ z.1 z.2))⁻¹ *
      (3 * z.2 - 0) = z.2 / Real.sqrt (canonicalFaceQ z.1 z.2)
    field_simp [hq]
    ring

/-- An explicit nonempty open set of E2 appears inside the
projection of the *rotated genuine face difference*. -/
theorem canonical_face_difference_has_open_projection
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    ∃ O : Set E2, IsOpen O ∧ O.Nonempty ∧
      O ⊆ canonicalTwoProjection ''
        (canonicalFaceRotation s 0 ''
          ((SphericalTetrahedron.canonicalTetrahedron s (lt_trans ht hts)).face 0 \
            canonicalFaceRotation t s ''
              (SphericalTetrahedron.canonicalTetrahedron t ht).face 0)) := by
  let W : Set (ℝ × ℝ) := canonicalFaceOpenDifference t s
  let O : Set E2 := canonicalPlanarToEuclidean ''
    (canonicalFaceDiskMap '' W)
  refine ⟨O, ?_, ?_, ?_⟩
  · exact canonicalPlanarToEuclidean.isOpenMap _
      (canonicalFaceDiskMap_isOpenMap _
        (canonicalFaceOpenDifference_isOpen t s))
  · obtain ⟨z, hz⟩ := canonicalFaceOpenDifference_nonempty ht hts
    exact ⟨canonicalPlanarToEuclidean (canonicalFaceDiskMap z),
      ⟨canonicalFaceDiskMap z, ⟨z, hz, rfl⟩, rfl⟩⟩
  · intro y hy
    rcases hy with ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    have hPatch := canonicalFaceOpenDifference_face_difference ht hts
      ⟨z, hz, rfl⟩
    refine ⟨canonicalFaceRotation s 0 (canonicalFacePoint s z.1 z.2),
      ⟨canonicalFacePoint s z.1 z.2, hPatch, rfl⟩, ?_⟩
    exact canonicalTwoProjection_rotated_face_point s z

end Sphere3
