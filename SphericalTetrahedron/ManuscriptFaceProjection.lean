module

public import SphericalTetrahedron.ManuscriptKernelInverse

@[expose] public section

/-!
# Face projection of the distinguished dual axis

The crucial invariant in the manuscript is

  ‖q - nᵢ‖² = ‖q‖² - 1.

Here `q` is the canonical vector pairing to `1` with all four inward
normals `nᵢ`. The vector `q-nᵢ` is the orthogonal projection of `q`
onto the plane through the other three dual vertices. The equal norm
provides the right-hand side of the four face-energy equations.

These lemmas prove the coordinate and metric identities only. This connects to the inverse-Gram `F` in `ManuscriptRigidityBridge` and
`ManuscriptStationaryRigidity`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SphericalTetrahedron

/-- The normal coordinates of the projected axis are completely explicit. -/
theorem manuscript_projection_normal_coordinates
    (T : SphericalTetrahedron) (i j : Fin 4) :
    ⟪T.normal j, T.normalDualAxis - T.normal i⟫_ℝ =
      1 - ⟪T.normal j, T.normal i⟫_ℝ := by
  rw [inner_sub_right, T.normalDualAxis_inner]

/-- The projected axis is in the three-dimensional hyperplane normal
to `normal i`. -/
theorem manuscript_projection_normal_orthogonal
    (T : SphericalTetrahedron) (i : Fin 4) :
    ⟪T.normal i, T.normalDualAxis - T.normal i⟫_ℝ = 0 := by
  rw [T.manuscript_projection_normal_coordinates]
  rw [real_inner_self_eq_norm_sq, T.unit i]
  norm_num

/-- Every remaining dual vertex has the same height against `q` and
its projection onto the corresponding face plane. -/
theorem manuscript_projection_face_height
    (T : SphericalTetrahedron) {i j : Fin 4} (hij : i ≠ j) :
    ⟪T.normalDualAxis - T.normal i, T.dualVertex j⟫_ℝ =
      ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ := by
  rw [inner_sub_left, T.dualVertex_offdiag i j hij]
  ring

/-- The equal-norm identity for projections onto all four face planes.
This is the geometric constant on the right of `(4.2)` in the manuscript. -/
theorem manuscript_face_projection_norm_sq
    (T : SphericalTetrahedron) (i : Fin 4) :
    ‖T.normalDualAxis - T.normal i‖ ^ 2 =
      ‖T.normalDualAxis‖ ^ 2 - 1 := by
  have hdot : ⟪T.normalDualAxis, T.normal i⟫_ℝ = 1 := by
    rw [real_inner_comm]
    exact T.normalDualAxis_inner i
  rw [norm_sub_sq_real, hdot, T.unit i]
  ring

/-- In particular all four face projections have equal squared norm. -/
theorem manuscript_face_projections_equinorm
    (T : SphericalTetrahedron) (i j : Fin 4) :
    ‖T.normalDualAxis - T.normal i‖ ^ 2 =
      ‖T.normalDualAxis - T.normal j‖ ^ 2 := by
  rw [T.manuscript_face_projection_norm_sq i,
    T.manuscript_face_projection_norm_sq j]

end SphericalTetrahedron
