module

public import Mathlib

@[expose] public section

/-!
# Congruence from a Gram matrix

Two independent families of four vectors in Euclidean four-space with the
same Gram matrix are related by a linear isometric equivalence.
This is purely linear algebra, independent of spherical geometry.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Sphere3

abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Equality of Gram matrices determines four-dimensional bases up to isometry. -/
theorem orthogonal_equiv_of_equal_gram
    (v w : Fin 4 → E4)
    (hv : LinearIndependent ℝ v)
    (hw : LinearIndependent ℝ w)
    (hGram : ∀ i j, ⟪v i, v j⟫_ℝ = ⟪w i, w j⟫_ℝ) :
    ∃ U : E4 ≃ₗᵢ[ℝ] E4, ∀ i, U (v i) = w i := by
  have hdim : Fintype.card (Fin 4) = Module.finrank ℝ E4 := by
    simp [E4]
  let bv : Module.Basis (Fin 4) ℝ E4 :=
    basisOfLinearIndependentOfCardEqFinrank hv hdim
  let bw : Module.Basis (Fin 4) ℝ E4 :=
    basisOfLinearIndependentOfCardEqFinrank hw hdim
  have bv_apply (i : Fin 4) : bv i = v i := by
    simp [bv]
  have bw_apply (i : Fin 4) : bw i = w i := by
    simp [bw]
  let L : E4 ≃ₗ[ℝ] E4 := bv.equiv bw (Equiv.refl (Fin 4))
  have hL (i : Fin 4) : L (v i) = w i := by
    rw [← bv_apply i, ← bw_apply i]
    simp [L]
  have hsum (a b : Fin 4 → ℝ) (u : Fin 4 → E4) :
      ⟪∑ i, a i • u i, ∑ j, b j • u j⟫_ℝ =
        ∑ i, ∑ j, a i * b j * ⟪u i, u j⟫_ℝ := by
    calc
      ⟪∑ i, a i • u i, ∑ j, b j • u j⟫_ℝ
          = ∑ i, ∑ j, ⟪a i • u i, b j • u j⟫_ℝ := by
              rw [sum_inner]
              simp_rw [inner_sum]
      _ = ∑ i, ∑ j, a i * b j * ⟪u i, u j⟫_ℝ := by
              simp_rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]
  have hInner : ∀ x y : E4, ⟪L x, L y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    let a : Fin 4 → ℝ := bv.equivFun x
    let b : Fin 4 → ℝ := bv.equivFun y
    have hx : (∑ i, a i • v i) = x := by
      simpa [a, bv_apply] using bv.sum_equivFun x
    have hy : (∑ i, b i • v i) = y := by
      simpa [b, bv_apply] using bv.sum_equivFun y
    have hxL : L x = ∑ i, a i • w i := by
      calc
        L x = L (∑ i, a i • v i) := by rw [hx]
        _ = ∑ i, a i • w i := by simp [map_sum, map_smul, hL]
    have hyL : L y = ∑ i, b i • w i := by
      calc
        L y = L (∑ i, b i • v i) := by rw [hy]
        _ = ∑ i, b i • w i := by simp [map_sum, map_smul, hL]
    calc
      ⟪L x, L y⟫_ℝ
          = ⟪∑ i, a i • w i, ∑ j, b j • w j⟫_ℝ := by rw [hxL, hyL]
      _ = ∑ i, ∑ j, a i * b j * ⟪w i, w j⟫_ℝ := hsum a b w
      _ = ∑ i, ∑ j, a i * b j * ⟪v i, v j⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hGram i j]
      _ = ⟪x, y⟫_ℝ := by
        rw [← hx, ← hy]
        exact (hsum a b v).symm
  let U : E4 ≃ₗᵢ[ℝ] E4 := L.isometryOfInner hInner
  refine ⟨U, ?_⟩
  intro i
  change L (v i) = w i
  exact hL i

end Sphere3
