module

public import SphericalTetrahedron.DualPolarity
public import SphericalTetrahedron.StationaryOrdering
public import SphericalTetrahedron.StationaryKernelDerivative

@[expose] public section

/-!
# Stationary disphenoid dual tetrahedra are equiangular

A partial *global* rigidity theorem, requiring no smallness assumption.
Suppose that the Gram products of the four canonical dual unit vertices
are paired equally on opposite edges:
  H₀₁ = H₂₃, H₀₂ = H₁₃, H₀₃ = H₁₂.
The two opposite-edge identities forced by stationarity then say that
  2 K(H₀₁) = 2 K(H₀₂) = 2 K(H₀₃).
The strict monotonicity of K on (-1,1) makes all six edge products equal.

This covers the disphenoid special case; general stationary rigidity is
proved in `ManuscriptStationaryRigidity`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SphericalTetrahedron

/-- The edge kernel is injective between any two feasible inner products.
This is a direct consequence of its strict monotonicity. -/
theorem stationaryKernel_injective_of_mem
    {x y : ℝ} (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1)
    (h : stationaryKernel x = stationaryKernel y) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hK := stationaryKernel_strictMonoOn hx hy hlt
    exact False.elim ((ne_of_lt hK) h)
  · exact heq
  · have hK := stationaryKernel_strictMonoOn hy hx hgt
    exact False.elim ((ne_of_gt hK) h)

/-- Purely algebraic opposite-pair equality after canceling a common
nonzero multiplier. This lemma works with an arbitrary injective kernel. -/
theorem opposite_pair_kernel_equality_of_stationary
    (x y z : ℝ) (K : ℝ → ℝ)
    (hxy : K x + K x = K y + K y)
    (hxz : K x + K x = K z + K z) :
    K x = K y ∧ K x = K z := by
  constructor <;> linarith

/-- Global partial rigidity: a stationary tetrahedron whose dual
vertices have the disphenoid opposite-edge symmetry has identical
pairings on all six dual edges. -/
theorem stationary_disphenoid_dual_gram
    (T : SphericalTetrahedron) (hStat : T.Stationary)
    (h01 : ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 2, T.dualVertex 3⟫_ℝ)
    (h02 : ⟪T.dualVertex 0, T.dualVertex 2⟫_ℝ =
      ⟪T.dualVertex 1, T.dualVertex 3⟫_ℝ)
    (h03 : ⟪T.dualVertex 0, T.dualVertex 3⟫_ℝ =
      ⟪T.dualVertex 1, T.dualVertex 2⟫_ℝ) :
    ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 0, T.dualVertex 2⟫_ℝ ∧
    ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 0, T.dualVertex 3⟫_ℝ ∧
    ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 2, T.dualVertex 3⟫_ℝ ∧
    ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 1, T.dualVertex 3⟫_ℝ ∧
    ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 1, T.dualVertex 2⟫_ℝ := by
  obtain ⟨hop1, hop2⟩ := T.stationary_opposite_edge_kernel_identities hStat
  have hKxy : stationaryKernel ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      stationaryKernel ⟪T.dualVertex 0, T.dualVertex 2⟫_ℝ := by
    rw [← h01, ← h02] at hop1
    linarith
  have hKxz : stationaryKernel ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      stationaryKernel ⟪T.dualVertex 0, T.dualVertex 3⟫_ℝ := by
    rw [← h01, ← h03] at hop2
    linarith
  have hxy := stationaryKernel_injective_of_mem
    (T.dualVertex_inner_mem (by decide : (0 : Fin 4) ≠ 1))
    (T.dualVertex_inner_mem (by decide : (0 : Fin 4) ≠ 2)) hKxy
  have hxz := stationaryKernel_injective_of_mem
    (T.dualVertex_inner_mem (by decide : (0 : Fin 4) ≠ 1))
    (T.dualVertex_inner_mem (by decide : (0 : Fin 4) ≠ 3)) hKxz
  exact ⟨hxy, hxz, h01, hxy.trans h02, hxz.trans h03⟩


/-- For `Fin 4`, the six explicit off-diagonal entries determine the
full equiangular condition on the dual Gram matrix. -/
theorem stationary_disphenoid_dual_regular
    (T : SphericalTetrahedron) (hStat : T.Stationary)
    (h01 : ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
      ⟪T.dualVertex 2, T.dualVertex 3⟫_ℝ)
    (h02 : ⟪T.dualVertex 0, T.dualVertex 2⟫_ℝ =
      ⟪T.dualVertex 1, T.dualVertex 3⟫_ℝ)
    (h03 : ⟪T.dualVertex 0, T.dualVertex 3⟫_ℝ =
      ⟪T.dualVertex 1, T.dualVertex 2⟫_ℝ) :
    T.Regular := by
  obtain ⟨hxy, hxz, h23, h13, h12⟩ :=
    T.stationary_disphenoid_dual_gram hStat h01 h02 h03
  apply T.regular_of_dualVertex_equiangular
  refine ⟨⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact hxy.symm
    | exact hxz.symm
    | exact h23.symm
    | exact h13.symm
    | exact h12.symm
    | exact (real_inner_comm _ _).trans hxy.symm
    | exact (real_inner_comm _ _).trans hxz.symm
    | exact (real_inner_comm _ _).trans h23.symm
    | exact (real_inner_comm _ _).trans h13.symm
    | exact (real_inner_comm _ _).trans h12.symm
    | exact real_inner_comm _ _
    | rfl

end SphericalTetrahedron
