module

public import SphericalTetrahedron.AffineChart

@[expose] public section

/-!
# A genuine topological chart for a spherical tetrahedron

The affine section of the positive cone is homeomorphic to the actual
spherical tetrahedron.  No measure-identification or global compactness
claim is used.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Radial normalization is continuous on the nonzero affine section. -/
theorem continuousOn_radialNormalize_affineSection
    (T : SphericalTetrahedron) :
    ContinuousOn radialNormalize T.affineSection := by
  have hInv : ContinuousOn (fun z : E4 => (‖z‖⁻¹ : ℝ))
      T.affineSection :=
    (continuous_norm.continuousOn).inv₀
      (fun z hz => norm_ne_zero_iff.mpr (T.affineSection_ne_zero hz))
  unfold radialNormalize
  exact hInv.smul continuous_id.continuousOn

/-- The inverse radial map is continuous on the closed spherical body. -/
theorem continuousOn_affineLift_body (T : SphericalTetrahedron) :
    ContinuousOn T.affineLift T.body := by
  have hHeight : Continuous (fun x : E4 => ⟪T.normalSum, x⟫_ℝ) := by
    fun_prop
  have hInv : ContinuousOn
      (fun x : E4 => (⟪T.normalSum, x⟫_ℝ)⁻¹) T.body :=
    hHeight.continuousOn.inv₀
      (fun x hx => (T.normalSum_inner_pos hx).ne')
  unfold affineLift
  exact hInv.smul continuous_id.continuousOn

/-- A homeomorphism with explicit inverse between the affine coordinate
section and `T.body`.  Both spaces carry their subspace topologies. -/
noncomputable def affineSectionHomeomorphBody (T : SphericalTetrahedron) :
    T.affineSection ≃ₜ T.body where
  toEquiv := T.affineSectionEquivBody
  continuous_toFun := by
    have h : Continuous (fun z : T.affineSection => radialNormalize z.1) :=
      (T.continuousOn_radialNormalize_affineSection).comp_continuous
        continuous_subtype_val (fun z => z.2)
    exact h.subtype_mk (fun z => T.affineSection_to_body z.2)
  continuous_invFun := by
    have h : Continuous (fun x : T.body => T.affineLift x.1) :=
      (T.continuousOn_affineLift_body).comp_continuous
        continuous_subtype_val (fun x => x.2)
    exact h.subtype_mk (fun x => T.body_to_affineSection x.2)

/-- Normal coordinates restrict to a homeomorphism between the affine
section and the standard three-simplex in four coordinates. -/
noncomputable def affineSectionHomeomorphSimplex (T : SphericalTetrahedron) :
    T.affineSection ≃ₜ standardSimplex4 where
  toEquiv := {
    toFun := fun z => ⟨T.normalCoordinatesEquiv z.1,
      (T.mem_affineSection_iff_standardSimplex4 z.1).mp z.2⟩
    invFun := fun u => ⟨T.normalCoordinatesEquiv.symm u.1, by
      apply (T.mem_affineSection_iff_standardSimplex4 _).mpr
      change T.normalCoordinatesEquiv (T.normalCoordinatesEquiv.symm u.1) ∈
        standardSimplex4
      simpa only [LinearEquiv.apply_symm_apply] using u.2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      exact T.normalCoordinatesEquiv.symm_apply_apply z.1
    right_inv := by
      intro u
      apply Subtype.ext
      exact T.normalCoordinatesEquiv.apply_symm_apply u.1
  }
  continuous_toFun := by
    have h : Continuous
        (fun z : T.affineSection => T.normalCoordinatesEquiv z.1) :=
      T.normalCoordinatesEquiv.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val
    exact h.subtype_mk
      (fun z => (T.mem_affineSection_iff_standardSimplex4 z.1).mp z.2)
  continuous_invFun := by
    have h : Continuous
        (fun u : standardSimplex4 => T.normalCoordinatesEquiv.symm u.1) :=
      T.normalCoordinatesEquiv.symm.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val
    exact h.subtype_mk (fun u => by
      apply (T.mem_affineSection_iff_standardSimplex4 _).mpr
      change T.normalCoordinatesEquiv (T.normalCoordinatesEquiv.symm u.1) ∈
        standardSimplex4
      simpa only [LinearEquiv.apply_symm_apply] using u.2)

/-- Every nondegenerate spherical tetrahedron is homeomorphic to the
standard closed three-simplex, with an explicit gnomonic formula. -/
noncomputable def standardSimplexHomeomorphBody (T : SphericalTetrahedron) :
    standardSimplex4 ≃ₜ T.body :=
  T.affineSectionHomeomorphSimplex.symm.trans
    T.affineSectionHomeomorphBody

/-- The topological chart identifies the compact spherical body with
its affine section. -/
theorem affineSection_isCompact (T : SphericalTetrahedron) :
    IsCompact T.affineSection := by
  have hBodyCompact : CompactSpace T.body :=
    isCompact_iff_compactSpace.mp T.body_isCompact
  have hUniv : IsCompact (Set.univ : Set T.body) :=
    @isCompact_univ _ _ hBodyCompact
  have hImage : IsCompact
      ((T.affineSectionHomeomorphBody).symm '' (Set.univ : Set T.body)) :=
    hUniv.image (T.affineSectionHomeomorphBody.symm.continuous)
  have hRange : (T.affineSectionHomeomorphBody).symm ''
      (Set.univ : Set T.body) = (Set.univ : Set T.affineSection) := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨x, hx⟩ := T.affineSectionHomeomorphBody.symm.surjective z
      exact ⟨x, Set.mem_univ _, hx⟩
  have hSectionUniv : IsCompact (Set.univ : Set T.affineSection) := by
    rw [← hRange]
    exact hImage
  have hSection : CompactSpace T.affineSection :=
    isCompact_univ_iff.mp hSectionUniv
  exact isCompact_iff_compactSpace.mpr hSection

end SphericalTetrahedron
