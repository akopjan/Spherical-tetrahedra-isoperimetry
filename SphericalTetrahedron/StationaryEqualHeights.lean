module

public import SphericalTetrahedron.StationaryDisphenoid

@[expose] public section

/-!
# Global rigidity under equal dual-axis heights

For the canonical unit dual vertices `v i` and normal-dual axis `q`,
stationarity has equations

  `<q,v i> + <q,v j> = c * stationaryKernel <v i,v j>`.

If the four heights `<q,v i>` agree, all six values of the strictly
increasing edge kernel agree. This implies equal dual Gram products,
then regularity of the original tetrahedron by polar involution.

Equal dual-axis heights for arbitrary stationary tetrahedra are proved in
`ManuscriptStationaryRigidity`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SphericalTetrahedron

/-- A stationary tetrahedron with equal dual-axis heights is regular. -/
theorem stationary_regular_of_equal_dual_heights
    (T : SphericalTetrahedron) (hStat : T.Stationary)
    (hHeight : ∀ i j : Fin 4,
      ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ =
        ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) :
    T.Regular := by
  obtain ⟨c, hc, hEq⟩ := (T.stationary_iff_dualVertex_equations).mp hStat
  let t : ℝ := ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h01eq := hEq 0 1 h01
  apply T.regular_of_dualVertex_equiangular
  refine ⟨t, ?_⟩
  intro i j hij
  have hijEq := hEq i j hij
  have hW : c * stationaryKernel t =
      c * stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
    dsimp [t]
    calc
      c * stationaryKernel ⟪T.dualVertex 0, T.dualVertex 1⟫_ℝ =
        ⟪T.normalDualAxis, T.dualVertex 0⟫_ℝ +
          ⟪T.normalDualAxis, T.dualVertex 1⟫_ℝ := h01eq.symm
      _ = ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
            ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ := by
        rw [hHeight 0 i, hHeight 1 j]
      _ = c * stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := hijEq
  have hK : stationaryKernel t =
      stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ :=
    mul_left_cancel₀ hc hW
  exact (stationaryKernel_injective_of_mem
    (T.dualVertex_inner_mem h01)
    (T.dualVertex_inner_mem hij) hK).symm

end SphericalTetrahedron
