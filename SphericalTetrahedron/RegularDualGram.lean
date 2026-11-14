module

public import SphericalTetrahedron.DualFrame
public import Sphere3.RegularGramBounds

@[expose] public section

/-!
# Inverting the regular normal Gram matrix inside the original tetrahedron

This file works with the actual `SphericalTetrahedron.normal`, rather than
with the auxiliary canonical family.  A regular normal frame has Gram matrix
`(1 - rho) I + rho J`.  The dual coordinate rays therefore have the explicit
inverse-Gram entries recorded below.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- The complete Gram matrix, including its diagonal entries. -/
theorem regular_normal_inner_formula (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i j : Fin 4) :
    ⟪T.normal i, T.normal j⟫_ℝ = if i = j then 1 else rho := by
  by_cases hij : i = j
  · subst j
    calc
      ⟪T.normal i, T.normal i⟫_ℝ = ‖T.normal i‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      _ = 1 := by rw [T.unit i]; norm_num
      _ = if i = i then (1 : ℝ) else rho := by simp
  · simpa [hij] using hGram i j hij

/-- Every regular normal pairs with the sum of the four normals to
`1 + 3*rho`, irrespective of its index. -/
theorem regular_normal_inner_sum (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i : Fin 4) :
    ⟪T.normal i, T.normalSum⟫_ℝ = 1 + 3 * rho := by
  rw [normalSum, inner_sum]
  simp_rw [T.regular_normal_inner_formula rho hGram]
  fin_cases i <;> norm_num [Fin.sum_univ_succ] <;> ring

/-- The normal sum pairs to one with every (unnormalized) dual ray. -/
theorem normalSum_inner_dualRay (T : SphericalTetrahedron)
    (j : Fin 4) :
    ⟪T.normalSum, T.normalDualRay j⟫_ℝ = 1 := by
  rw [normalSum, sum_inner]
  simp_rw [T.normalDualRay_inner]
  fin_cases j <;> norm_num [Fin.sum_univ_succ]

/-- The explicit inverse image of a coordinate unit vector under
`x ↦ (⟪n_i,x⟫)_i`. -/
theorem regular_dualRay_formula (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i : Fin 4) :
    T.normalDualRay i =
      ((1 - rho)⁻¹ : ℝ) •
        (T.normal i - (rho / (1 + 3 * rho)) • T.normalSum) := by
  have hRange := _root_.regular_parameter_mem T rho hGram
  have h1 : 1 - rho ≠ 0 := ne_of_gt (by linarith [hRange.2])
  have h3 : 1 + 3 * rho ≠ 0 := ne_of_gt (by linarith [hRange.1])
  apply T.normalCoordinatesLinear_injective
  funext j
  change ⟪T.normal j, T.normalDualRay i⟫_ℝ =
    ⟪T.normal j, ((1 - rho)⁻¹ : ℝ) •
      (T.normal i - (rho / (1 + 3 * rho)) • T.normalSum)⟫_ℝ
  rw [T.normalDualRay_inner, inner_smul_right,
    inner_sub_right, inner_smul_right,
    T.regular_normal_inner_formula rho hGram,
    T.regular_normal_inner_sum rho hGram]
  by_cases hij : j = i
  · simp only [if_pos hij, div_mul_cancel₀ _ h3]
    exact (inv_mul_cancel₀ h1).symm
  · simp only [if_neg hij, div_mul_cancel₀ _ h3]
    have : (1 - rho)⁻¹ * (rho - rho) = 0 := by ring
    exact this.symm

/-- Exact inverse-Gram formula for pairings of the dual rays. -/
theorem regular_dualRay_inner (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i j : Fin 4) :
    ⟪T.normalDualRay i, T.normalDualRay j⟫_ℝ =
      ((1 - rho)⁻¹ : ℝ) *
        ((if i = j then (1 : ℝ) else 0) - rho / (1 + 3 * rho)) := by
  rw [T.regular_dualRay_formula rho hGram i]
  rw [inner_smul_left, inner_sub_left,
    inner_smul_left, T.normalDualRay_inner,
    T.normalSum_inner_dualRay]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- The diagonal entries of the inverse Gram matrix. -/
theorem regular_dualRay_inner_self (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i : Fin 4) :
    ⟪T.normalDualRay i, T.normalDualRay i⟫_ℝ =
      (1 + 2 * rho) / ((1 - rho) * (1 + 3 * rho)) := by
  have hRange := _root_.regular_parameter_mem T rho hGram
  have h1 : 1 - rho ≠ 0 := ne_of_gt (by linarith [hRange.2])
  have h3 : 1 + 3 * rho ≠ 0 := ne_of_gt (by linarith [hRange.1])
  rw [T.regular_dualRay_inner rho hGram i i, if_pos rfl, one_sub_div h3,
    inv_eq_one_div, div_mul_div_comm, one_mul]
  congr 1
  ring

/-- The off-diagonal entries of the inverse Gram matrix. -/
theorem regular_dualRay_inner_offdiag (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i j : Fin 4) (hij : i ≠ j) :
    ⟪T.normalDualRay i, T.normalDualRay j⟫_ℝ =
      -rho / ((1 - rho) * (1 + 3 * rho)) := by
  have hRange := _root_.regular_parameter_mem T rho hGram
  have h1 : 1 - rho ≠ 0 := ne_of_gt (by linarith [hRange.2])
  have h3 : 1 + 3 * rho ≠ 0 := ne_of_gt (by linarith [hRange.1])
  rw [T.regular_dualRay_inner rho hGram i j]
  simp only [if_neg hij, zero_sub]
  field_simp [h1, h3]
  <;> ring

/-- The unique dual axis equals a scalar multiple of the normal sum. -/
theorem regular_dualAxis_formula (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho) :
    T.normalDualAxis = ((1 + 3 * rho)⁻¹ : ℝ) • T.normalSum := by
  have hRange := _root_.regular_parameter_mem T rho hGram
  have h3 : 1 + 3 * rho ≠ 0 := ne_of_gt (by linarith [hRange.1])
  apply T.normalCoordinatesLinear_injective
  funext i
  change ⟪T.normal i, T.normalDualAxis⟫_ℝ =
    ⟪T.normal i, ((1 + 3 * rho)⁻¹ : ℝ) • T.normalSum⟫_ℝ
  rw [T.normalDualAxis_inner, inner_smul_right,
    T.regular_normal_inner_sum rho hGram]
  field_simp [h3]
  <;> ring

/-- All regular dual rays have the same Euclidean norm. -/
theorem regular_dualRay_norm_eq (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i j : Fin 4) :
    ‖T.normalDualRay i‖ = ‖T.normalDualRay j‖ := by
  have hi : ‖T.normalDualRay i‖ ^ 2 =
      (1 + 2 * rho) / ((1 - rho) * (1 + 3 * rho)) := by
    rw [← real_inner_self_eq_norm_sq]
    exact T.regular_dualRay_inner_self rho hGram i
  have hj : ‖T.normalDualRay j‖ ^ 2 =
      (1 + 2 * rho) / ((1 - rho) * (1 + 3 * rho)) := by
    rw [← real_inner_self_eq_norm_sq]
    exact T.regular_dualRay_inner_self rho hGram j
  nlinarith [norm_nonneg (T.normalDualRay i),
    norm_nonneg (T.normalDualRay j)]

/-- The positive common dual-ray height. -/
theorem regular_dualAxis_inner_dualRay (T : SphericalTetrahedron)
    (rho : ℝ)
    (hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (i : Fin 4) :
    ⟪T.normalDualAxis, T.normalDualRay i⟫_ℝ =
      (1 + 3 * rho)⁻¹ := by
  rw [T.regular_dualAxis_formula rho hGram, inner_smul_left,
    T.normalSum_inner_dualRay]
  simp only [starRingEnd_apply, star_trivial, mul_one]

end SphericalTetrahedron
