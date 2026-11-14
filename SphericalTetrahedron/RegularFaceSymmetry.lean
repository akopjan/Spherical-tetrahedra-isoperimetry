module

public import SphericalTetrahedron.CanonicalRealization

@[expose] public section

/-!
# All faces of a regular spherical tetrahedron have equal area

An arbitrary permutation of the four unit inward normals of a regular
spherical tetrahedron preserves their Gram matrix.  As the normals form
a basis, this permutation extends to a linear isometric equivalence of
`E4`.  It maps the corresponding faces into one another, so all four
faces have *equal actual two-dimensional Hausdorff measure*.

This reduces the analytic area-identification problem to a single face.
Strict growth of one canonical face is proved in
`CanonicalFaceHausdorffStrict`.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Each permutation of the facet normals of a regular tetrahedron is
realized by a linear isometric equivalence of the ambient space. -/
theorem regular_normal_perm_isometry (T : SphericalTetrahedron)
    (hReg : T.Regular) (σ : Equiv.Perm (Fin 4)) :
    ∃ U : E4 ≃ₗᵢ[ℝ] E4,
      ∀ i : Fin 4, U (T.normal i) = T.normal (σ i) := by
  obtain ⟨ρ, hρ⟩ := hReg
  have hGram : ∀ i j : Fin 4,
      ⟪T.normal i, T.normal j⟫_ℝ =
        ⟪T.normal (σ i), T.normal (σ j)⟫_ℝ := by
    intro i j
    by_cases hij : i = j
    · subst j
      calc
        ⟪T.normal i, T.normal i⟫_ℝ = ‖T.normal i‖ ^ 2 :=
          real_inner_self_eq_norm_sq _
        _ = (1 : ℝ) := by rw [T.unit i]; norm_num
        _ = ‖T.normal (σ i)‖ ^ 2 := by
          rw [T.unit (σ i)]
          norm_num
        _ = ⟪T.normal (σ i), T.normal (σ i)⟫_ℝ :=
          (real_inner_self_eq_norm_sq _).symm
    · have hσ : σ i ≠ σ j := fun heq => hij (σ.injective heq)
      exact (hρ i j hij).trans (hρ (σ i) (σ j) hσ).symm
  have hPermIndependent : LinearIndependent ℝ (T.normal ∘ σ) :=
    T.independent.comp σ σ.injective
  exact Sphere3.orthogonal_equiv_of_equal_gram T.normal (T.normal ∘ σ)
    T.independent hPermIndependent hGram

/-- All faces of a regular tetrahedron have the same genuine Hausdorff
measure.  The argument uses only Gram rigidity and invariance under
isometries, and makes no normalization assumption about Hausdorff measure. -/
theorem regular_face_measure_eq (T : SphericalTetrahedron)
    (hReg : T.Regular) (i j : Fin 4) :
    measure 2 (T.face i) = measure 2 (T.face j) := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap i j
  obtain ⟨U, hU⟩ := regular_normal_perm_isometry T hReg σ
  have hImage : T.face (σ i) =
      (LinearIsometryEquiv.toIsometryEquiv U) '' T.face i :=
    congruent_tetrahedron_image_face T T U σ
      (fun k => (hU k).symm) i
  have hi : σ i = j := Equiv.swap_apply_left i j
  dsimp [measure]
  calc
    ((Measure.hausdorffMeasure (2 : ℝ)) (T.face i)).toReal =
        ((Measure.hausdorffMeasure (2 : ℝ)) (T.face (σ i))).toReal := by
      rw [hImage]
      rw [(LinearIsometryEquiv.toIsometryEquiv U).hausdorffMeasure_image
        2 (T.face i)]
    _ = ((Measure.hausdorffMeasure (2 : ℝ)) (T.face j)).toReal := by
      rw [hi]

/-- For a regular spherical tetrahedron the total area is exactly four
times the measure of any one face, regardless of Hausdorff normalization. -/
theorem regular_area_eq_four_face (T : SphericalTetrahedron)
    (hReg : T.Regular) (i : Fin 4) :
    T.area = 4 * measure 2 (T.face i) := by
  calc
    T.area = ∑ j : Fin 4, measure 2 (T.face j) := rfl
    _ = ∑ _j : Fin 4, measure 2 (T.face i) := by
      apply Finset.sum_congr rfl
      intro j _
      exact regular_face_measure_eq T hReg j i
    _ = 4 * measure 2 (T.face i) := by
      simp [Finset.sum_const, nsmul_eq_mul]

end SphericalTetrahedron
