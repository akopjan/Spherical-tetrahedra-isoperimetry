module

public import SphericalTetrahedron.Topology

@[expose] public section

/-!
# Exact affine chart for an arbitrary nondegenerate spherical tetrahedron

The normal coordinates put the closed tetrahedron in bijection with the
standard three-simplex.  In particular, this is a chart for the *actual*
`SphericalTetrahedron.body`, not a second definition of spherical volume.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Radial projection from the punctured ambient vector space to the sphere. -/
def radialNormalize (z : E4) : E4 := (‖z‖⁻¹ : ℝ) • z

/-- Inverse radial projection onto the affine hyperplane of normal height one. -/
def affineLift (T : SphericalTetrahedron) (x : E4) : E4 :=
  (⟪T.normalSum, x⟫_ℝ)⁻¹ • x

/-- Points in the section never vanish, since their normal height is one. -/
theorem affineSection_ne_zero (T : SphericalTetrahedron) {z : E4}
    (hz : z ∈ T.affineSection) : z ≠ 0 := by
  intro hzero
  have hh := hz.2
  rw [hzero, inner_zero_right] at hh
  norm_num at hh

/-- The inverse radial lift of a normalized section point is the original point. -/
theorem affineLift_radialNormalize (T : SphericalTetrahedron)
    {z : E4} (hz : z ∈ T.affineSection) :
    T.affineLift (radialNormalize z) = z := by
  have hz0 : z ≠ 0 := T.affineSection_ne_zero hz
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  unfold affineLift radialNormalize
  rw [real_inner_smul_right, hz.2, mul_one]
  simp [smul_smul, hn]

/-- Normalizing the affine lift of a spherical point gives the point back. -/
theorem radialNormalize_affineLift (T : SphericalTetrahedron)
    {x : E4} (hx : x ∈ T.body) :
    radialNormalize (T.affineLift x) = x := by
  have hh : 0 < ⟪T.normalSum, x⟫_ℝ := T.normalSum_inner_pos hx
  have hnorm : ‖T.affineLift x‖ = (⟪T.normalSum, x⟫_ℝ)⁻¹ := by
    unfold affineLift
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh), hx.1]
    ring
  unfold radialNormalize
  rw [hnorm]
  unfold affineLift
  simp [smul_smul, hh.ne']

/-- The affine section and the actual spherical tetrahedron are bijective. -/
noncomputable def affineSectionEquivBody (T : SphericalTetrahedron) :
    T.affineSection ≃ T.body where
  toFun z := ⟨radialNormalize z.1, T.affineSection_to_body z.2⟩
  invFun x := ⟨T.affineLift x.1, T.body_to_affineSection x.2⟩
  left_inv z := by
    apply Subtype.ext
    exact T.affineLift_radialNormalize z.2
  right_inv x := by
    apply Subtype.ext
    exact T.radialNormalize_affineLift x.2

/-- The whole spherical body is precisely the radial image of its affine section. -/
theorem body_eq_radial_image_affineSection (T : SphericalTetrahedron) :
    T.body = radialNormalize '' T.affineSection := by
  ext x
  constructor
  · intro hx
    refine ⟨T.affineLift x, T.body_to_affineSection hx, ?_⟩
    exact T.radialNormalize_affineLift hx
  · rintro ⟨z, hz, rfl⟩
    exact T.affineSection_to_body hz

/-- The affine section maps to the standard simplex in normal coordinates. -/
theorem affineSection_image_coordinates (T : SphericalTetrahedron) :
    T.normalCoordinatesLinear '' T.affineSection = standardSimplex4 := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (T.mem_affineSection_iff_standardSimplex4 z).mp hz
  · intro hu
    obtain ⟨z, hz, hzu⟩ := T.standardSimplex4_has_affine_preimage hu
    exact ⟨z, hz, hzu⟩

/-- The spherical parametrization of the standard simplex induced by the normals. -/
def simplexToSphere (T : SphericalTetrahedron) (u : Fin 4 → ℝ) : E4 :=
  radialNormalize (T.normalCoordinatesEquiv.symm u)

/-- Coordinates of a point reconstructed from its four normal coordinates. -/
theorem normalCoordinatesLinear_symm_apply (T : SphericalTetrahedron)
    (u : Fin 4 → ℝ) :
    T.normalCoordinatesLinear (T.normalCoordinatesEquiv.symm u) = u := by
  change T.normalCoordinatesEquiv (T.normalCoordinatesEquiv.symm u) = u
  exact T.normalCoordinatesEquiv.apply_symm_apply u

/-- Every point of the actual tetrahedron comes from one simplex point. -/
theorem body_eq_simplex_radial_image (T : SphericalTetrahedron) :
    T.body = T.simplexToSphere '' standardSimplex4 := by
  ext x
  constructor
  · intro hx
    let z := T.affineLift x
    have hz : z ∈ T.affineSection := T.body_to_affineSection hx
    let u := T.normalCoordinatesEquiv z
    have hu : u ∈ standardSimplex4 := by
      -- The underlying linear map of the coordinate equivalence is N.
      change T.normalCoordinatesLinear z ∈ standardSimplex4
      exact (T.mem_affineSection_iff_standardSimplex4 z).mp hz
    refine ⟨u, hu, ?_⟩
    change radialNormalize (T.normalCoordinatesEquiv.symm u) = x
    rw [LinearEquiv.symm_apply_apply]
    exact T.radialNormalize_affineLift hx
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨z, hz, hzu⟩ := T.standardSimplex4_has_affine_preimage hu
    have hz' : z = T.normalCoordinatesEquiv.symm u := by
      apply T.normalCoordinatesEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      exact hzu
    unfold simplexToSphere
    rw [← hz']
    exact T.affineSection_to_body hz

/-- The unit-normal inner products of a simplex point have the same signs
and zeros as its barycentric coordinates. -/
theorem simplexToSphere_inner (T : SphericalTetrahedron)
    (u : Fin 4 → ℝ) (i : Fin 4) :
    ⟪T.normal i, T.simplexToSphere u⟫_ℝ =
      ‖T.normalCoordinatesEquiv.symm u‖⁻¹ * u i := by
  unfold simplexToSphere radialNormalize
  rw [real_inner_smul_right]
  have h := congrFun (T.normalCoordinatesLinear_symm_apply u) i
  change ⟪T.normal i, T.normalCoordinatesEquiv.symm u⟫_ℝ = u i at h
  rw [h]

/-- The face opposite normal `i` is the image of the corresponding
coordinate facet of the standard three-simplex. -/
theorem face_eq_simplex_facet_image (T : SphericalTetrahedron) (i : Fin 4) :
    T.face i =
      T.simplexToSphere '' {u : Fin 4 → ℝ | u ∈ standardSimplex4 ∧ u i = 0} := by
  ext x
  constructor
  · intro hx
    have himage : x ∈ T.simplexToSphere '' standardSimplex4 := by
      rw [← T.body_eq_simplex_radial_image]
      exact hx.1
    obtain ⟨u, hu, hxu⟩ := himage
    have hz : T.normalCoordinatesEquiv.symm u ∈ T.affineSection := by
      apply (T.mem_affineSection_iff_standardSimplex4 _).mpr
      rw [T.normalCoordinatesLinear_symm_apply]
      exact hu
    have hz0 : T.normalCoordinatesEquiv.symm u ≠ 0 := T.affineSection_ne_zero hz
    have hp : 0 < (‖T.normalCoordinatesEquiv.symm u‖⁻¹ : ℝ) :=
      inv_pos.mpr (norm_pos_iff.mpr hz0)
    have hi : ‖T.normalCoordinatesEquiv.symm u‖⁻¹ * u i = 0 := by
      rw [← T.simplexToSphere_inner, hxu]
      exact hx.2
    have hui : u i = 0 := (mul_eq_zero.mp hi).resolve_left hp.ne'
    exact ⟨u, ⟨hu, hui⟩, hxu⟩
  · rintro ⟨u, ⟨hu, hui⟩, rfl⟩
    constructor
    · rw [T.body_eq_simplex_radial_image]
      exact ⟨u, hu, rfl⟩
    · rw [T.simplexToSphere_inner, hui, mul_zero]

/-- The four face conditions pull back to coordinate facets of the simplex. -/
theorem face_iff_simplex_coordinate_zero (T : SphericalTetrahedron)
    (i : Fin 4) (x : E4) :
    x ∈ T.face i ↔ x ∈ T.body ∧ T.normalCoordinatesLinear x i = 0 := by
  rfl

end SphericalTetrahedron
