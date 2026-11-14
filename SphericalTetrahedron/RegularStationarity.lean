module

public import SphericalTetrahedron.RegularDualGram
public import SphericalTetrahedron.DualAngleBounds

@[expose] public section

/-!
# Regular tetrahedra satisfy the exact stationary equations

This is the forward direction of the rigidity statement: `Regular → Stationary`.
The theorem uses the canonical witnesses proved in `DualFrame.lean` and
an explicit inverse-Gram calculation for the original normal frame.

The converse (`Stationary → Regular`) is proved in
`ManuscriptStationaryRigidity`.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- In a regular tetrahedron every canonical dual vertex has the same
positive height against the normal dual axis. -/
theorem regular_dualVertex_height (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i : Fin 4) :
    ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ =
      ‖T.normalDualRay 0‖⁻¹ * (1 + 3 * rho)⁻¹ := by
  unfold dualVertex
  rw [real_inner_smul_right, T.regular_dualAxis_inner_dualRay rho hGram i]
  rw [T.regular_dualRay_norm_eq rho hGram i 0]

/-- For a regular tetrahedron the mutual scalar products of distinct
unit dual vertices are all `-rho/(1+2*rho)`. -/
theorem regular_dualVertex_inner_offdiag (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i j : Fin 4) (hij : i ≠ j) :
    ⟪T.dualVertex i, T.dualVertex j⟫_ℝ =
      -rho / (1 + 2 * rho) := by
  have hRange := _root_.regular_parameter_mem T rho hGram
  have h1 : 1 - rho ≠ 0 := ne_of_gt (by linarith [hRange.2])
  have h3 : 1 + 3 * rho ≠ 0 := ne_of_gt (by linarith [hRange.1])
  have h2 : 1 + 2 * rho ≠ 0 := ne_of_gt (by linarith [hRange.1])
  have hden : (1 - rho) * (1 + 3 * rho) ≠ 0 := mul_ne_zero h1 h3
  let s : ℝ := ‖T.normalDualRay 0‖
  have hspos : 0 < s := norm_pos_iff.mpr (T.normalDualRay_ne_zero 0)
  have hsq : s ^ 2 * ((1 - rho) * (1 + 3 * rho)) = 1 + 2 * rho := by
    apply (eq_div_iff hden).mp
    change ‖T.normalDualRay 0‖ ^ 2 =
      (1 + 2 * rho) / ((1 - rho) * (1 + 3 * rho))
    rw [← real_inner_self_eq_norm_sq]
    exact T.regular_dualRay_inner_self rho hGram 0
  have hnum : ⟪T.dualVertex i, T.dualVertex j⟫_ℝ =
      s⁻¹ * s⁻¹ * (-rho / ((1 - rho) * (1 + 3 * rho))) := by
    unfold dualVertex
    rw [inner_smul_left, inner_smul_right,
      T.regular_dualRay_inner_offdiag rho hGram i j hij,
      T.regular_dualRay_norm_eq rho hGram i 0,
      T.regular_dualRay_norm_eq rho hGram j 0]
    simp only [starRingEnd_apply, star_trivial]
    ring
  calc
    ⟪T.dualVertex i, T.dualVertex j⟫_ℝ =
        s⁻¹ * s⁻¹ * (-rho / ((1 - rho) * (1 + 3 * rho))) := hnum
    _ = -rho / (s ^ 2 * ((1 - rho) * (1 + 3 * rho))) := by
      field_simp [hspos.ne', hden]
      <;> ring
    _ = -rho / (1 + 2 * rho) := by rw [hsq]

/-- The common dual-vertex scalar product lies strictly between -1 and 1. -/
theorem regular_dualAngle_mem (rho : ℝ)
    (hRange : -(1 : ℝ) / 3 < rho ∧ rho < 1) :
    -1 < -rho / (1 + 2 * rho) ∧
      -rho / (1 + 2 * rho) < 1 := by
  have h2 : 0 < 1 + 2 * rho := by linarith [hRange.1]
  constructor
  · apply (lt_div_iff₀ h2).2
    nlinarith [hRange.1]
  · apply (div_lt_iff₀ h2).2
    nlinarith [hRange.1]

/-- Regularity is sufficient for the six canonical stationarity equations,
providing an explicit witness for the Lagrange multiplier. -/
theorem regular_implies_stationary (T : SphericalTetrahedron)
    (hReg : T.Regular) : T.Stationary := by
  obtain ⟨rho, hGram⟩ := hReg
  have hRange : -(1 : ℝ) / 3 < rho ∧ rho < 1 :=
    _root_.regular_parameter_mem T rho hGram
  let d : ℝ := -rho / (1 + 2 * rho)
  let h : ℝ := ‖T.normalDualRay 0‖⁻¹ * (1 + 3 * rho)⁻¹
  have hRay : 0 < ‖T.normalDualRay 0‖ :=
    norm_pos_iff.mpr (T.normalDualRay_ne_zero 0)
  have hThree : 0 < 1 + 3 * rho := by linarith [hRange.1]
  have hHeight : 0 < h :=
    mul_pos (inv_pos.mpr hRay) (inv_pos.mpr hThree)
  have hK : 0 < stationaryKernel d :=
    stationaryKernel_pos_of_mem (regular_dualAngle_mem rho hRange)
  let c : ℝ := 2 * h / stationaryKernel d
  have hc : c ≠ 0 := ne_of_gt (div_pos (by positivity) hK)
  apply (T.stationary_iff_dualVertex_equations).2
  refine ⟨c, hc, ?_⟩
  intro i j hij
  rw [T.regular_dualVertex_height rho hGram i,
    T.regular_dualVertex_height rho hGram j,
    T.regular_dualVertex_inner_offdiag rho hGram i j hij]
  change h + h = c * stationaryKernel d
  dsimp only [c]
  field_simp [hK.ne']
  <;> ring

end SphericalTetrahedron
