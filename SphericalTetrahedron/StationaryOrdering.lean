module

public import SphericalTetrahedron.StationarityConsequences

@[expose] public section

/-!
# Four-point comparison identities from stationarity

The six equations h_i + h_j = c*K(i,j) imply that for pairwise
distinct i,k,j,l,

    K(i,j) - K(k,j) = K(i,l) - K(k,l).

Thus the ordering of the two edge kernels with the common endpoint j
is the same as their ordering with common endpoint l. This identity
eliminates the Lagrange multiplier and all vertex heights. Strict
monotonicity of the angular kernel converts it into a corresponding
comparison of the dual Gram matrix entries.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- A four-point difference identity involving only dual-angle kernels. -/
theorem stationary_four_point_kernel_identity
    (T : SphericalTetrahedron) (h : T.Stationary)
    (i k j l : Fin 4)
    (hij : i ≠ j) (hkj : k ≠ j)
    (hil : i ≠ l) (hkl : k ≠ l) :
    stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ -
      stationaryKernel ⟪T.dualVertex k, T.dualVertex j⟫_ℝ =
    stationaryKernel ⟪T.dualVertex i, T.dualVertex l⟫_ℝ -
      stationaryKernel ⟪T.dualVertex k, T.dualVertex l⟫_ℝ := by
  obtain ⟨c, hc, heq⟩ :=
    (T.stationary_iff_dualVertex_equations).mp h
  have h1 := heq i j hij
  have h2 := heq k j hkj
  have h3 := heq i l hil
  have h4 := heq k l hkl
  have hmul : c *
      (stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ -
       stationaryKernel ⟪T.dualVertex k, T.dualVertex j⟫_ℝ -
       stationaryKernel ⟪T.dualVertex i, T.dualVertex l⟫_ℝ +
       stationaryKernel ⟪T.dualVertex k, T.dualVertex l⟫_ℝ) = 0 := by
    nlinarith [h1, h2, h3, h4]
  have hz := (mul_eq_zero.mp hmul).resolve_left hc
  linarith

/-- Comparing the two kernels at j or at l gives the same strict order. -/
theorem stationary_four_point_kernel_order
    (T : SphericalTetrahedron) (h : T.Stationary)
    (i k j l : Fin 4)
    (hij : i ≠ j) (hkj : k ≠ j)
    (hil : i ≠ l) (hkl : k ≠ l) :
    (stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ <
     stationaryKernel ⟪T.dualVertex k, T.dualVertex j⟫_ℝ) ↔
    (stationaryKernel ⟪T.dualVertex i, T.dualVertex l⟫_ℝ <
     stationaryKernel ⟪T.dualVertex k, T.dualVertex l⟫_ℝ) := by
  have heq := T.stationary_four_point_kernel_identity h i k j l
    hij hkj hil hkl
  constructor <;> intro hlt <;> linarith

end SphericalTetrahedron
