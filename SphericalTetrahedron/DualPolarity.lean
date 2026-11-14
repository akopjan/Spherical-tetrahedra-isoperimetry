module

public import SphericalTetrahedron.RegularStationarity

@[expose] public section

/-!
# Polarity of nondegenerate spherical tetrahedra

The four *unit dual vertices* themselves form an admissible set of
unit inward facet normals: their linear independence follows from the
positive diagonal biorthogonal pairings with the original normals.
Taking the unit dual vertices a second time then returns the original
facet normals, with no relabeling or choice of orientation.

This is the exact algebraic link needed to translate a regular dual
vertex Gram matrix into the original `SphericalTetrahedron.Regular`.
No variational theorem or convexity inequality is assumed.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- The four unit dual vertices constitute a linearly independent frame. -/
theorem dualVertex_linearIndependent (T : SphericalTetrahedron) :
    LinearIndependent ℝ T.dualVertex := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hsum i
  have hi : ⟪T.normal i, ∑ j : Fin 4, f j • T.dualVertex j⟫_ℝ = 0 := by
    rw [hsum, inner_zero_right]
  have hcollapse :
      (∑ j : Fin 4, f j * ⟪T.normal i, T.dualVertex j⟫_ℝ) =
        f i * ⟪T.normal i, T.dualVertex i⟫_ℝ := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      rw [T.dualVertex_offdiag i j (Ne.symm hj)]
      ring
    · simp
  rw [inner_sum] at hi
  simp_rw [real_inner_smul_right] at hi
  rw [hcollapse] at hi
  exact (mul_eq_zero.mp hi).resolve_right
    (T.dualVertex_diagonal_pos i).ne'

/-- The polar dual tetrahedron, represented in the same ambient `S³`. -/
def polarDual (T : SphericalTetrahedron) : SphericalTetrahedron where
  normal := T.dualVertex
  unit := T.dualVertex_norm
  independent := T.dualVertex_linearIndependent

/-- Polarity is involutive at the level of *unit facet normals*.
The positive diagonal orientation is essential here. -/
theorem polarDual_dualVertex (T : SphericalTetrahedron) (i : Fin 4) :
    T.polarDual.dualVertex i = T.normal i := by
  have h : ∀ j, T.normal j = T.polarDual.dualVertex j :=
    T.polarDual.dualVertex_unique T.normal T.unit
      (by
        intro j k hjk
        change ⟪T.dualVertex j, T.normal k⟫_ℝ = 0
        rw [real_inner_comm]
        exact T.dualVertex_offdiag k j hjk.symm)
      (by
        intro j
        change 0 < ⟪T.dualVertex j, T.normal j⟫_ℝ
        rw [real_inner_comm]
        exact T.dualVertex_diagonal_pos j)
  exact (h i).symm

/-- Regularity of the positive polar dual implies regularity of the
original unit-normal configuration. The explicit transformed Gram
parameter is obtained from the already-proved forward dual Gram formula. -/
theorem regular_of_polarDual_regular (T : SphericalTetrahedron)
    (hPolar : T.polarDual.Regular) : T.Regular := by
  obtain ⟨t, ht, hGram⟩ := regular_has_parameter T.polarDual hPolar
  refine ⟨-t / (1 + 2 * t), ?_⟩
  intro i j hij
  have h := T.polarDual.regular_dualVertex_inner_offdiag t hGram i j hij
  rw [T.polarDual_dualVertex i, T.polarDual_dualVertex j] at h
  exact h

/-- A tetrahedron with equal pairwise dual-vertex products is regular.
This is the geometric inverse-Gram implication, free of any extra axiom. -/
theorem regular_of_dualVertex_equiangular (T : SphericalTetrahedron)
    (h : ∃ t : ℝ, ∀ i j : Fin 4, i ≠ j →
      ⟪T.dualVertex i, T.dualVertex j⟫_ℝ = t) : T.Regular := by
  apply T.regular_of_polarDual_regular
  exact h

end SphericalTetrahedron
