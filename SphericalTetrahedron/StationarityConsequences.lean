module

public import SphericalTetrahedron.DualAngleBounds
public import Sphere3.StationaryEdgeAlgebra

@[expose] public section

/-!
# Necessary identities for stationary spherical tetrahedra

The original stationarity system involves six nonlinear equations.
The two equalities below eliminate the four vertex-height variables and
the common nonzero multiplier.  The equations involve only the six
pairwise scalar products of the canonical dual vertices.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- A stationary tetrahedron satisfies two independent equations in
    the six vertex scalar products, with no unknown Lagrange multiplier. -/
theorem stationary_opposite_edge_kernel_identities
    (T : SphericalTetrahedron) (h : T.Stationary) :
    stationaryKernel ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ +
        stationaryKernel ⟪T.dualVertex 2, T.dualVertex 3⟫_ℝ =
      stationaryKernel ⟪T.dualVertex 0, T.dualVertex 2⟫_ℝ +
        stationaryKernel ⟪T.dualVertex 1, T.dualVertex 3⟫_ℝ ∧
    stationaryKernel ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ +
        stationaryKernel ⟪T.dualVertex 2, T.dualVertex 3⟫_ℝ =
      stationaryKernel ⟪T.dualVertex 0, T.dualVertex 3⟫_ℝ +
        stationaryKernel ⟪T.dualVertex 1, T.dualVertex 2⟫_ℝ := by
  obtain ⟨c, hc, heq⟩ := (T.stationary_iff_dualVertex_equations).mp h
  exact Sphere3.stationary_opposite_edge_identities
    (fun i => ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ)
    (fun i j => stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ)
    c hc heq

/-- The dual-axis heights of a stationary tetrahedron are determined
    by any triangle of edge-kernel values. -/
theorem stationary_dual_axis_height_triangle
    (T : SphericalTetrahedron) (h : T.Stationary)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ c : ℝ, c ≠ 0 ∧
      2 * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ = c *
        (stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ +
         stationaryKernel ⟪T.dualVertex i, T.dualVertex k⟫_ℝ -
         stationaryKernel ⟪T.dualVertex j, T.dualVertex k⟫_ℝ) := by
  obtain ⟨c, hc, heq⟩ := (T.stationary_iff_dualVertex_equations).mp h
  exact ⟨c, hc, Sphere3.stationary_height_triangle_identity
    (fun a => ⟪T.normalDualAxis, T.dualVertex a⟫_ℝ)
    (fun a b => stationaryKernel ⟪T.dualVertex a, T.dualVertex b⟫_ℝ)
    c heq i j k hij hik hjk⟩


/-- No sum of dual-axis heights at distinct vertices can vanish in a
stationary nondegenerate tetrahedron.  The nonvanishing follows from
strict angular separation, not from an assumed sign for the multiplier. -/
theorem stationary_edge_height_ne_zero
    (T : SphericalTetrahedron) (hStationary : T.Stationary)
    {i j : Fin 4} (hij : i ≠ j) :
    ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
      ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ ≠ 0 := by
  obtain ⟨c, hc, heq⟩ :=
    (T.stationary_iff_dualVertex_equations).mp hStationary
  rw [heq i j hij]
  exact mul_ne_zero hc (T.stationaryKernel_dualVertex_pos hij).ne'

/-- The sign of the common Lagrange multiplier is the sign of EVERY
pairwise sum of vertex heights; its sign is not silently assumed. -/
theorem stationary_edge_height_common_sign
    (T : SphericalTetrahedron) (hStationary : T.Stationary) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ i j : Fin 4, i ≠ j →
        0 < c * (⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
                 ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) := by
  obtain ⟨c, hc, heq⟩ :=
    (T.stationary_iff_dualVertex_equations).mp hStationary
  refine ⟨c, hc, ?_⟩
  intro i j hij
  rw [heq i j hij]
  have hsq : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hK : 0 < stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ :=
    T.stationaryKernel_dualVertex_pos hij
  nlinarith [mul_pos hsq hK]

end SphericalTetrahedron
