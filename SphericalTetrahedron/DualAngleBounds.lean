module

public import SphericalTetrahedron.DualFrame

@[expose] public section

/-!
# Strict angle bounds for dual vertices

Distinct vertices of a nondegenerate spherical simplex cannot coincide or
be antipodal.  With the unit-norm identities, the elementary formulas for
squared chordal distances imply strict bounds on their inner products.
Those bounds also establish positivity of the arccosine first-variation
kernel on every geometrically relevant edge.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Different canonical dual vertices are never antipodal. -/
theorem dualVertex_not_antipodal (T : SphericalTetrahedron)
    (i j : Fin 4) :
    T.dualVertex i ≠ -T.dualVertex j := by
  intro heq
  have hi : T.dualVertex i ∈ T.body := T.dualVertex_mem_body i
  rw [heq] at hi
  exact (T.body_no_antipodal (T.dualVertex_mem_body j)) hi

/-- The inner product of distinct dual vertices lies in `(-1,1)`.
This uses neither regularity nor any variational assumption. -/
theorem dualVertex_inner_mem (T : SphericalTetrahedron)
    {i j : Fin 4} (hij : i ≠ j) :
    -1 < ⟪T.dualVertex i, T.dualVertex j⟫_ℝ ∧
      ⟪T.dualVertex i, T.dualVertex j⟫_ℝ < 1 := by
  have hdiff : T.dualVertex i - T.dualVertex j ≠ 0 :=
    sub_ne_zero.mpr (T.dualVertex_injective.ne hij)
  have hsum : T.dualVertex i + T.dualVertex j ≠ 0 := by
    intro hz
    have hneg : T.dualVertex i = -T.dualVertex j := by
      have heq := congrArg (fun x : E4 => x - T.dualVertex j) hz
      simpa using heq
    exact T.dualVertex_not_antipodal i j hneg
  have hdpos : 0 < ‖T.dualVertex i - T.dualVertex j‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hdiff)
  have hspos : 0 < ‖T.dualVertex i + T.dualVertex j‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hsum)
  have hd : ‖T.dualVertex i - T.dualVertex j‖ ^ 2 =
      2 - 2 * ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
    rw [norm_sub_sq_real, T.dualVertex_norm, T.dualVertex_norm]
    ring
  have hs : ‖T.dualVertex i + T.dualVertex j‖ ^ 2 =
      2 + 2 * ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
    rw [norm_add_sq_real, T.dualVertex_norm, T.dualVertex_norm]
    ring
  constructor <;> nlinarith

/-- Positivity of the stationarity kernel for every possible genuine
nondegenerate spherical edge. -/
theorem stationaryKernel_pos_of_mem {x : ℝ}
    (hx : -1 < x ∧ x < 1) :
    0 < stationaryKernel x := by
  have hmul : 0 < (1 - x) * (1 + x) :=
    mul_pos (by linarith [hx.2]) (by linarith [hx.1])
  have hradicand : 0 < 1 - x ^ 2 := by nlinarith [hmul]
  have hroot : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.2 hradicand
  have hacos : 0 < Real.arccos x := Real.arccos_pos.mpr hx.2
  unfold stationaryKernel
  exact mul_pos (by linarith [hx.1]) (div_pos hacos hroot)

/-- Every edge kernel in the intrinsic stationarity equations is positive. -/
theorem stationaryKernel_dualVertex_pos (T : SphericalTetrahedron)
    {i j : Fin 4} (hij : i ≠ j) :
    0 < stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ :=
  stationaryKernel_pos_of_mem (T.dualVertex_inner_mem hij)

end SphericalTetrahedron
