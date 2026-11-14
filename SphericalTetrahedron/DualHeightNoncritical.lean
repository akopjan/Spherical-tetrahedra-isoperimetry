module

public import SphericalTetrahedron.DualPolarity
public import Sphere3.AreaGradientNoncriticalAlgebra

@[expose] public section

/-!
# A positive weighted identity for the dual-axis heights

The dual-axis vector `q` equals the sum of the four unnormalized
dual rays, or equivalently the positive combination
`sum_i ||w_i|| * v_i` of the four unit dual vertices.
Taking the inner product with `q` proves exactly:

  sum_i ||w_i|| * <q,v_i> = ||q||^2 > 0.

This shows that not all four dual-axis heights can vanish; in fact,
at least one is positive, although **individual heights need not be
positive**. These results support the noncritical-area-gradient
argument required by a Lagrange multiplier proof. They do not supply
the separate analytic formula for the derivative of Hausdorff area.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Each unnormalized dual ray is its own length times its unit vertex. -/
theorem normalDualRay_eq_norm_smul_dualVertex
    (T : SphericalTetrahedron) (i : Fin 4) :
    T.normalDualRay i = ‖T.normalDualRay i‖ • T.dualVertex i := by
  have h : ‖T.normalDualRay i‖ ≠ 0 :=
    (norm_pos_iff.mpr (T.normalDualRay_ne_zero i)).ne'
  unfold dualVertex
  rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- Explicit positive-weight expansion of the canonical dual axis. -/
theorem normalDualAxis_eq_sum_weighted_dualVertex
    (T : SphericalTetrahedron) :
    T.normalDualAxis =
      ∑ i : Fin 4, ‖T.normalDualRay i‖ • T.dualVertex i := by
  calc
    T.normalDualAxis = ∑ i : Fin 4, T.normalDualRay i :=
      T.normalDualAxis_eq_sum_normalDualRay
    _ = ∑ i : Fin 4, ‖T.normalDualRay i‖ • T.dualVertex i := by
      apply Finset.sum_congr rfl
      intro i _
      exact T.normalDualRay_eq_norm_smul_dualVertex i

/-- Positive weighted identity, derived from the dual basis and no
assumption of stationarity or regularity. -/
theorem dual_height_weighted_sum_eq_norm_sq
    (T : SphericalTetrahedron) :
    (∑ i : Fin 4,
        ‖T.normalDualRay i‖ *
          ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ) =
      ‖T.normalDualAxis‖ ^ 2 := by
  calc
    (∑ i : Fin 4,
        ‖T.normalDualRay i‖ *
          ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ) =
      ⟪T.normalDualAxis,
        ∑ i : Fin 4, ‖T.normalDualRay i‖ • T.dualVertex i⟫_ℝ := by
        rw [inner_sum]
        simp only [real_inner_smul_right]
    _ = ⟪T.normalDualAxis, T.normalDualAxis⟫_ℝ := by
      rw [← T.normalDualAxis_eq_sum_weighted_dualVertex]
    _ = ‖T.normalDualAxis‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- The dual-axis length is positive, independently of stationarity. -/
theorem normalDualAxis_norm_pos (T : SphericalTetrahedron) :
    0 < ‖T.normalDualAxis‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hp := T.normalDualAxis_inner (0 : Fin 4)
  rw [h, inner_zero_right] at hp
  norm_num at hp

/-- The weighted sum of heights is strictly positive. -/
theorem dual_height_weighted_sum_pos (T : SphericalTetrahedron) :
    0 < ∑ i : Fin 4,
      ‖T.normalDualRay i‖ *
        ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ := by
  rw [T.dual_height_weighted_sum_eq_norm_sq]
  exact sq_pos_of_pos T.normalDualAxis_norm_pos

/-- At least one canonical height is positive. This does **not** assert
that all four individual heights are positive. -/
theorem exists_dual_height_pos (T : SphericalTetrahedron) :
    ∃ i : Fin 4, 0 < ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ := by
  classical
  by_contra h
  push_neg at h
  have hsum :
      (∑ i : Fin 4,
        ‖T.normalDualRay i‖ *
          ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (h i)
  exact (not_lt_of_ge hsum) T.dual_height_weighted_sum_pos

end SphericalTetrahedron

namespace SphericalTetrahedron

/-- Without stationarity, at least one dual-height pair sum is nonzero.
This is the algebraic noncriticality witness for any future proof of the
Hausdorff area gradient formula. -/
theorem exists_nonzero_dual_height_pair (T : SphericalTetrahedron) :
    (⟪T.normalDualAxis, T.dualVertex 0⟫_ℝ +
      ⟪T.normalDualAxis, T.dualVertex 1⟫_ℝ ≠ 0) ∨
    (⟪T.normalDualAxis, T.dualVertex 0⟫_ℝ +
      ⟪T.normalDualAxis, T.dualVertex 2⟫_ℝ ≠ 0) ∨
    (⟪T.normalDualAxis, T.dualVertex 1⟫_ℝ +
      ⟪T.normalDualAxis, T.dualVertex 2⟫_ℝ ≠ 0) ∨
    (⟪T.normalDualAxis, T.dualVertex 0⟫_ℝ +
      ⟪T.normalDualAxis, T.dualVertex 3⟫_ℝ ≠ 0) := by
  obtain ⟨i, hi⟩ := T.exists_dual_height_pos
  apply Sphere3.exists_nonzero_pair_sum
  fin_cases i
  · exact Or.inl (ne_of_gt hi)
  · exact Or.inr (Or.inl (ne_of_gt hi))
  · exact Or.inr (Or.inr (Or.inl (ne_of_gt hi)))
  · exact Or.inr (Or.inr (Or.inr (ne_of_gt hi)))

end SphericalTetrahedron
