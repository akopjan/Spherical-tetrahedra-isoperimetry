module

public import Mathlib

@[expose] public section

/-!
# Gram parameter of a regular spherical tetrahedron

Four linearly independent unit vectors in Euclidean four-space cannot
have an arbitrary common off-diagonal inner product. Their common value
lies in `(-1/3, 1)`. This is a direct consequence of positivity of the
Gram quadratic form and linear independence.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Sphere3

/-- The Gram matrix of four independent unit vectors whose off-diagonal
entries are all `rho` is positive definite only if `-1/3 < rho < 1`. -/
theorem regularGramParameter_mem
    (v : Fin 4 → EuclideanSpace ℝ (Fin 4))
    (hv : LinearIndependent ℝ v)
    (hunit : ∀ i, ‖v i‖ = 1)
    (rho : ℝ)
    (hGram : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = rho) :
    -(1 : ℝ) / 3 < rho ∧ rho < 1 := by
  classical
  have hpair (i j : Fin 4) :
      ⟪v i, v j⟫_ℝ = if i = j then 1 else rho := by
    by_cases h : i = j
    · subst j
      simp [real_inner_self_eq_norm_sq, hunit]
    · simp [h, hGram i j h]
  have hsum_ne : (∑ i : Fin 4, v i) ≠ 0 := by
    intro hsum
    have hmap :
        (Fintype.linearCombination ℝ v) (fun _ => (1 : ℝ)) =
          (Fintype.linearCombination ℝ v) (fun _ => (0 : ℝ)) := by
      simp only [Fintype.linearCombination_apply]
      simpa using hsum
    have hfun := hv.fintypeLinearCombination_injective hmap
    have hcontra := congrArg (fun f : Fin 4 → ℝ => f 0) hfun
    norm_num at hcontra
  have hsum_sq : ‖∑ i : Fin 4, v i‖ ^ 2 = 4 + 12 * rho := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum]
    simp [hpair, Fin.sum_univ_succ]
    <;> ring
  have hsum_pos : 0 < ‖∑ i : Fin 4, v i‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hsum_ne)
  have hlow : -(1 : ℝ) / 3 < rho := by linarith
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hneq : v 0 ≠ v 1 := fun h => h01 (hv.injective h)
  have hdiff_pos : 0 < ‖v 0 - v 1‖ ^ 2 := by
    have h : 0 < ‖v 0 - v 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
    positivity
  have hdiff : ‖v 0 - v 1‖ ^ 2 = 2 - 2 * rho := by
    rw [norm_sub_sq_real]
    rw [hunit 0, hunit 1, hGram 0 1 h01]
    ring
  have hupp : rho < 1 := by linarith
  exact ⟨hlow, hupp⟩

end Sphere3
