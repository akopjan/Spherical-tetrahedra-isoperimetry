module

public import Sphere3.CanonicalFaceRotation
public import Sphere3.CanonicalFaceDiskChart

@[expose] public section

/-!
# Injectivity of the first-face chart and disjointness of the open patch

The fourth coordinate of the raw affine lift is exactly 3, so it can be
used as a projective denominator to recover the planar chart parameters.
Consequently the nonempty planar difference patch embeds into the real
set difference of the corresponding *original* canonical faces, after
transporting the smaller face by the explicit ambient rotation.
-/

noncomputable section

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The projective inverse recovers a point's planar parameters. -/
theorem canonicalFaceInverse_point (t : ℝ) (z : ℝ × ℝ) :
    canonicalFaceInverse t (canonicalFacePoint t z.1 z.2) = z := by
  let r : E4 := canonicalFaceRawLift t z.1 z.2
  have hr : 0 < ‖r‖ := canonicalFaceRawLift_norm_pos t z.1 z.2
  have hh : 0 < canonicalFaceHeight t := canonicalFaceHeight_pos t
  have hden : canonicalFaceHeight t * (3 * ‖r‖⁻¹) ≠ 0 := by
    positivity
  apply Prod.ext
  · change (3 * (‖r‖⁻¹ * (canonicalFaceHeight t * z.1 - t)) +
      t * (‖r‖⁻¹ * 3)) / (canonicalFaceHeight t * (‖r‖⁻¹ * 3)) = z.1
    field_simp [hr.ne', hh.ne']
    ring
  · change (3 * (‖r‖⁻¹ * (canonicalFaceHeight t * z.2 - t)) +
      t * (‖r‖⁻¹ * 3)) / (canonicalFaceHeight t * (‖r‖⁻¹ * 3)) = z.2
    field_simp [hr.ne', hh.ne']
    ring

/-- The canonical normalized first-face chart is globally injective. -/
theorem canonicalFacePoint_injective (t : ℝ) :
    Function.Injective
      (fun z : ℝ × ℝ => canonicalFacePoint t z.1 z.2) := by
  intro z w h
  calc
    z = canonicalFaceInverse t (canonicalFacePoint t z.1 z.2) :=
      (canonicalFaceInverse_point t z).symm
    _ = canonicalFaceInverse t (canonicalFacePoint t w.1 w.2) :=
      congrArg _ h
    _ = w := canonicalFaceInverse_point t w

/-- The open planar patch lies inside the genuine set-theoretic
face difference, not just inside an auxiliary planar model. -/
theorem canonicalFaceOpenDifference_face_difference
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (fun z : ℝ × ℝ => canonicalFacePoint s z.1 z.2) ''
        canonicalFaceOpenDifference t s ⊆
      (SphericalTetrahedron.canonicalTetrahedron s (lt_trans ht hts)).face 0 \
        canonicalFaceRotation t s ''
          (SphericalTetrahedron.canonicalTetrahedron t ht).face 0 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hArea := canonicalFaceOpenDifference_subset t s hz
  constructor
  · apply (canonicalFacePoint_mem_first_face_iff
        s (lt_trans ht hts) z.1 z.2).mpr
    simpa [canonicalFaceRawRegion_eq_triangle] using hArea.1
  · rintro ⟨y, hy, hxy⟩
    rw [canonicalTetrahedron_first_face_eq_chart t ht] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have heq : canonicalFacePoint s w.1 w.2 =
      canonicalFacePoint s z.1 z.2 := by
      simpa [canonicalFaceRotation_chart] using hxy
    have hwz := canonicalFacePoint_injective s heq
    subst w
    exact hArea.2 hw

end Sphere3
