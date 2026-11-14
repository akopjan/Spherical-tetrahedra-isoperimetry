module

public import SphericalTetrahedron.ManuscriptRigidityBridge

@[expose] public section

/-!
# The inverse angular kernel on precisely the values needed in the manuscript

A total inverse of `stationaryKernel` can be defined without first proving
that its image is exactly `(0,2)`: on its actual range inside `(-1,1)` we
choose the unique preimage, and outside that range we set the inverse to
zero. Strict monotonicity of the angular kernel makes that choice unique.

This is particularly useful for the stationarity equations, because every
pair sum of normalized heights is already known to be in this range.
The analytic triangle ordering lemma is proved in
`ManuscriptTriangleOrdering`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SphericalTetrahedron

/-- A total inverse of the angular kernel, exact on its feasible range. -/
def manuscriptKernelInverse (s : ℝ) : ℝ := by
  classical
  exact if h : ∃ x : ℝ,
      x ∈ Set.Ioo (-1 : ℝ) 1 ∧ stationaryKernel x = s then
    Classical.choose h
  else 0

/-- Every feasible scalar product is recovered exactly from its
stationary kernel value, without a global range-surjectivity theorem. -/
theorem manuscriptKernelInverse_stationaryKernel
    (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    manuscriptKernelInverse (stationaryKernel x) = x := by
  have hExist : ∃ y : ℝ,
      y ∈ Set.Ioo (-1 : ℝ) 1 ∧ stationaryKernel y = stationaryKernel x :=
    ⟨x, hx, rfl⟩
  have hSpec := Classical.choose_spec hExist
  have hIn : (Classical.choose hExist) ∈ Set.Ioo (-1 : ℝ) 1 := hSpec.1
  have hEq : stationaryKernel (Classical.choose hExist) =
      stationaryKernel x := hSpec.2
  unfold manuscriptKernelInverse
  rw [dif_pos hExist]
  exact stationaryKernel_injective_of_mem hIn hx hEq

/-- The inverse is strictly increasing on the actual image of the
geometrically feasible angular kernel. No endpoint-surjectivity claim
about `(0,2)` is needed. -/
theorem manuscriptKernelInverse_strictMonoOn_image :
    StrictMonoOn manuscriptKernelInverse
      (stationaryKernel '' Set.Ioo (-1 : ℝ) 1) := by
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  have hxy : x < y := by
    by_contra hn
    have hyx : y ≤ x := le_of_not_gt hn
    rcases eq_or_lt_of_le hyx with heq | hlt
    · subst x
      exact (lt_irrefl _) hab
    · have hrev := stationaryKernel_strictMonoOn hy hx hlt
      exact (not_lt_of_ge (le_of_lt hrev)) hab
  simpa only [manuscriptKernelInverse_stationaryKernel x hx,
    manuscriptKernelInverse_stationaryKernel y hy] using hxy

/-- The manuscript's concrete face-energy function, with its angular
inverse chosen by the explicit construction above. -/
def manuscriptActualFaceEnergy (a b c : ℝ) : ℝ :=
  manuscriptFaceEnergy manuscriptKernelInverse a b c

/-- Strict stationarity determines all six dual-vertex Gram products
as inverse-kernel values of scaled heights. -/
theorem stationary_inverse_kernel_gram
    (T : SphericalTetrahedron) (hStat : T.Stationary) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ i j : Fin 4, i ≠ j →
        manuscriptKernelInverse
          (c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
           c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) =
          ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
  obtain ⟨c, hc, hStationary⟩ :=
    (T.stationary_iff_dualVertex_equations).mp hStat
  refine ⟨c, hc, ?_⟩
  intro i j hij
  have hPair :
      c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ =
      stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
    calc
      c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
          c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ =
        c⁻¹ * (⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
          ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) := by ring
      _ = c⁻¹ * (c * stationaryKernel
            ⟪T.dualVertex i, T.dualVertex j⟫_ℝ) := by
        rw [hStationary i j hij]
      _ = stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
        field_simp [hc]
  rw [hPair]
  exact manuscriptKernelInverse_stationaryKernel _ (T.dualVertex_inner_mem hij)

end SphericalTetrahedron
