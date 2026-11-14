module

public import Mathlib
public import SphericalTetrahedron.ManuscriptAreaGradient
public import SphericalTetrahedron.ManuscriptGaussianSchlafli
public import SphericalTetrahedron.ManuscriptFirstVariationBridge
public import SphericalTetrahedron.DualHeightNoncritical
public import SphericalTetrahedron.ManuscriptStationaryRigidity

@[expose] public section

/-!
# First variation of fixed-area volume maximizers

This module proves `volume_maximizer_is_stationary_manuscript`: any area-constrained
volume maximizer `M : SphericalTetrahedron` satisfies the manuscript stationarity
equations `M.Stationary`.

The proof works in the smooth 6-dimensional Gram coordinate chart `gramOpen`:
1. Both `stdAreaGram` and `gaussVolGram` are strictly differentiable at `M.gramPoint`.
2. Noncriticality of dual heights (`DualHeightNoncritical.exists_nonzero_dual_height_pair`)
   gives a coordinate direction `k₀ : Fin 6` in which `stdAreaFDeriv M.gramPoint` is nonzero.
3. Applying Mathlib's implicit function theorem (`HasStrictFDerivAt.implicitFunction`) along
   level sets of `stdAreaGram` yields a Lagrange multiplier `lam` with
   `gaussVolFDeriv M.gramPoint = lam • stdAreaFDeriv M.gramPoint`.
4. Comparing coordinate derivatives via `gaussVolFDeriv_coord` and `stdAreaFDeriv_coord`
   produces a variational certificate for `stationary_of_manuscript_variational_certificate`.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

private theorem exists_oppIdx_pair {i j : Fin 4} (hij : i ≠ j) :
    ∃ k : Fin 6, oppIdx k = (i, j) ∨ oppIdx k = (j, i) := by
  fin_cases i <;> fin_cases j <;> simp at hij
  · exact ⟨5, Or.inl rfl⟩
  · exact ⟨4, Or.inl rfl⟩
  · exact ⟨3, Or.inl rfl⟩
  · exact ⟨5, Or.inr rfl⟩
  · exact ⟨2, Or.inl rfl⟩
  · exact ⟨1, Or.inl rfl⟩
  · exact ⟨4, Or.inr rfl⟩
  · exact ⟨2, Or.inr rfl⟩
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨3, Or.inr rfl⟩
  · exact ⟨1, Or.inr rfl⟩
  · exact ⟨0, Or.inr rfl⟩

private theorem dualVertex_inner_tetOf (M : SphericalTetrahedron) (i j : Fin 4) :
    ⟪(tetOf M.gramPoint (gramPoint_mem_gramOpen M)).dualVertex i,
        (tetOf M.gramPoint (gramPoint_mem_gramOpen M)).dualVertex j⟫_ℝ =
      ⟪M.dualVertex i, M.dualVertex j⟫_ℝ := by
  let T := tetOf M.gramPoint (gramPoint_mem_gramOpen M)
  rw [T.dualVertex_inner_eq_adj i j, M.dualVertex_inner_eq_adj i j, gramPoint_tetOf]

private theorem dualHeight_tetOf (M : SphericalTetrahedron) (i : Fin 4) :
    ⟪(tetOf M.gramPoint (gramPoint_mem_gramOpen M)).normalDualAxis,
        (tetOf M.gramPoint (gramPoint_mem_gramOpen M)).dualVertex i⟫_ℝ =
      ⟪M.normalDualAxis, M.dualVertex i⟫_ℝ := by
  let T := tetOf M.gramPoint (gramPoint_mem_gramOpen M)
  rw [T.dualHeight_eq_adj i, M.dualHeight_eq_adj i, gramPoint_tetOf]

private theorem stdAreaFDeriv_coord_ne_zero_of_height_add
    (M : SphericalTetrahedron) (k : Fin 6) {i j : Fin 4}
    (hk : oppIdx k = (i, j))
    (hsum : ⟪M.normalDualAxis, M.dualVertex i⟫_ℝ +
      ⟪M.normalDualAxis, M.dualVertex j⟫_ℝ ≠ 0) :
    stdAreaFDeriv M.gramPoint (Pi.single k 1) ≠ 0 := by
  have hx := gramPoint_mem_gramOpen M
  have hij : i ≠ j := by
    have hne := oppIdx_ne k
    rw [hk] at hne
    exact hne
  have hcoord := stdAreaFDeriv_coord hx k
  dsimp only at hcoord
  rw [hk] at hcoord
  dsimp only at hcoord
  rw [dualVertex_inner_tetOf, dualHeight_tetOf, dualHeight_tetOf] at hcoord
  rw [hcoord]
  have hρ : ⟪M.dualVertex i, M.dualVertex j⟫_ℝ ∈ Set.Ioo (-1 : ℝ) 1 :=
    dualVertex_inner_mem_Ioo M hij
  have h1ρ2 : 0 < 1 - ⟪M.dualVertex i, M.dualVertex j⟫_ℝ ^ 2 := by
    nlinarith [hρ.1, hρ.2]
  have h1ρ : 0 < 1 + ⟪M.dualVertex i, M.dualVertex j⟫_ℝ := by
    linarith [hρ.1]
  have haij : 0 < √(1 - ⟪M.dualVertex i, M.dualVertex j⟫_ℝ ^ 2) /
      (1 + ⟪M.dualVertex i, M.dualVertex j⟫_ℝ) :=
    div_pos (Real.sqrt_pos.mpr h1ρ2) h1ρ
  have hxk : |M.gramPoint k| < 1 := gramOpen_offdiag_abs_lt_one hx k
  have h1xk2 : 0 < 1 - M.gramPoint k ^ 2 := by
    rcases abs_cases (M.gramPoint k) <;> nlinarith
  have hden : √(1 - M.gramPoint k ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1xk2).ne'
  exact div_ne_zero (mul_ne_zero hsum haij.ne') hden

private theorem exists_stdAreaFDeriv_ne_zero (M : SphericalTetrahedron) :
    ∃ k : Fin 6, stdAreaFDeriv M.gramPoint (Pi.single k 1) ≠ 0 := by
  rcases exists_nonzero_dual_height_pair M with h01 | h02 | h12 | h03
  · exact ⟨5, stdAreaFDeriv_coord_ne_zero_of_height_add M 5 (by decide) h01⟩
  · exact ⟨4, stdAreaFDeriv_coord_ne_zero_of_height_add M 4 (by decide) h02⟩
  · exact ⟨2, stdAreaFDeriv_coord_ne_zero_of_height_add M 2 (by decide) h12⟩
  · exact ⟨3, stdAreaFDeriv_coord_ne_zero_of_height_add M 3 (by decide) h03⟩

private theorem lagrange_multiplier_of_constrained_local_max
    {U : Set (Fin 6 → ℝ)} (hU : IsOpen U) {x₀ : Fin 6 → ℝ} (hx₀ : x₀ ∈ U)
    {f g : (Fin 6 → ℝ) → ℝ} {f' g' : (Fin 6 → ℝ) →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f f' x₀) (hg : HasStrictFDerivAt g g' x₀)
    (hmax : ∀ y ∈ U, f y = f x₀ → g y ≤ g x₀)
    {k₀ : Fin 6} (hk₀ : f' (Pi.single k₀ 1) ≠ 0) :
    ∃ lam : ℝ, g' = lam • f' := by
  have hrange : LinearMap.range (f' : (Fin 6 → ℝ) →ₗ[ℝ] ℝ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(y / f' (Pi.single k₀ 1)) • Pi.single k₀ 1, ?_⟩
    change f' ((y / f' (Pi.single k₀ 1)) • Pi.single k₀ 1) = y
    simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ hk₀]
  have hker : ∀ v : Fin 6 → ℝ, f' v = 0 → g' v = 0 := by
    intro v hv
    let ψ : (f' : (Fin 6 → ℝ) →L[ℝ] ℝ).ker → Fin 6 → ℝ :=
      HasStrictFDerivAt.implicitFunction f f' hf hrange (f x₀)
    let vKer : (f' : (Fin 6 → ℝ) →L[ℝ] ℝ).ker := ⟨v, hv⟩
    let φ : ℝ → (f' : (Fin 6 → ℝ) →L[ℝ] ℝ).ker := fun t => t • vKer
    let γ : ℝ → Fin 6 → ℝ := fun t => ψ (φ t)
    have hγ0 : γ 0 = x₀ := by
      dsimp [γ, φ, ψ]
      rw [zero_smul]
      exact HasStrictFDerivAt.implicitFunction_apply_image hf hrange
    have hψ_fderiv :
        HasStrictFDerivAt ψ ((f' : (Fin 6 → ℝ) →L[ℝ] ℝ).ker.subtypeL) 0 :=
      HasStrictFDerivAt.to_implicitFunction hf hrange
    have hφ_cont : Continuous φ := continuous_id.smul continuous_const
    have hφ_tend : Filter.Tendsto φ (nhds 0) (nhds 0) := by
      have ht := hφ_cont.tendsto 0
      simpa [φ] using ht
    have hψ_tend : Filter.Tendsto ψ (nhds 0) (nhds x₀) := by
      have ht := hψ_fderiv.hasFDerivAt.continuousAt.tendsto
      have hψ0 : ψ 0 = x₀ := HasStrictFDerivAt.implicitFunction_apply_image hf hrange
      rwa [hψ0] at ht
    have hγ_U : ∀ᶠ t in nhds (0 : ℝ), γ t ∈ U :=
      (hψ_tend.comp hφ_tend).eventually (hU.mem_nhds hx₀)
    have hγ_lvl : ∀ᶠ t in nhds (0 : ℝ), f (γ t) = f x₀ := by
      have hmap := HasStrictFDerivAt.map_implicitFunction_eq hf hrange
      have hp : Filter.Tendsto (fun t : ℝ => (f x₀, φ t)) (nhds 0) (nhds (f x₀, 0)) := by
        rw [nhds_prod_eq]
        exact tendsto_const_nhds.prodMk hφ_tend
      exact hp.eventually hmap
    have hloc : IsLocalMax (g ∘ γ) 0 := by
      rw [IsLocalMax, IsMaxFilter]
      filter_upwards [hγ_U, hγ_lvl] with t htU htlvl
      change g (γ t) ≤ g (γ 0)
      rw [hγ0]
      exact hmax (γ t) htU htlvl
    have hφ_deriv : HasDerivAt φ vKer 0 := by
      simpa [φ] using (hasDerivAt_id (0 : ℝ)).smul_const vKer
    have hψ_comp : HasDerivAt γ v 0 := by
      have h0 : φ 0 = 0 := by simp [φ]
      have hψ_at : HasFDerivAt ψ ((f' : (Fin 6 → ℝ) →L[ℝ] ℝ).ker.subtypeL) (φ 0) := by
        rw [h0]
        exact hψ_fderiv.hasFDerivAt
      exact hψ_at.comp_hasDerivAt 0 hφ_deriv
    have hcomp_deriv : HasDerivAt (g ∘ γ) (g' v) 0 := by
      have hg_at : HasFDerivAt g g' (γ 0) := by
        rw [hγ0]
        exact hg.hasFDerivAt
      exact hg_at.comp_hasDerivAt 0 hψ_comp
    exact hloc.hasDerivAt_eq_zero hcomp_deriv
  let e₀ : Fin 6 → ℝ := Pi.single k₀ 1
  let lam : ℝ := g' e₀ / f' e₀
  refine ⟨lam, ?_⟩
  ext w
  have hw_ker : f' (w - (f' w / f' e₀) • e₀) = 0 := by
    simp [map_sub, map_smul, smul_eq_mul, e₀, div_mul_cancel₀ _ hk₀]
  have hgw := hker (w - (f' w / f' e₀) • e₀) hw_ker
  simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hgw
  change g' w = lam * f' w
  dsimp [lam]
  rw [hgw]
  ring

/-- Any fixed-area volume maximizer is stationary in the manuscript's sense. -/
theorem volume_maximizer_is_stationary_manuscript (M : SphericalTetrahedron)
    (hMax : ∀ S : SphericalTetrahedron, S.area = M.area → S.volume ≤ M.volume) :
    M.Stationary := by
  let x₀ := M.gramPoint
  have hx₀ : x₀ ∈ gramOpen := gramPoint_mem_gramOpen M
  have hconstrained :
      ∀ y ∈ gramOpen, stdAreaGram y = stdAreaGram x₀ → gaussVolGram y ≤ gaussVolGram x₀ := by
    intro y hy harea
    let S := tetOf y hy
    have hS_area : S.area = M.area := by
      rw [S.area_eq_faceScale_mul_stdArea, M.area_eq_faceScale_mul_stdArea,
        S.stdArea_eq_stdAreaGram, M.stdArea_eq_stdAreaGram, gramPoint_tetOf, harea]
    have hS_vol : S.volume ≤ M.volume := hMax S hS_area
    rw [S.volume_eq_two_sphereScale_mul_gaussVolGram,
      M.volume_eq_two_sphereScale_mul_gaussVolGram, gramPoint_tetOf] at hS_vol
    have hscale : 0 < 2 * sphereScale 3 := by
      linarith [sphereScale_pos (d := 3) (by norm_num)]
    nlinarith
  obtain ⟨k₀, hk₀⟩ := exists_stdAreaFDeriv_ne_zero M
  obtain ⟨lam, hlam⟩ := lagrange_multiplier_of_constrained_local_max
    isOpen_gramOpen hx₀
    (hasStrictFDerivAt_stdAreaGram hx₀)
    (hasStrictFDerivAt_gaussVolGram hx₀)
    hconstrained hk₀
  let a : Fin 4 → Fin 4 → ℝ := fun i j =>
    let ρ := ⟪M.dualVertex i, M.dualVertex j⟫_ℝ
    √(1 - ρ ^ 2) / (1 + ρ)
  let ell : Fin 4 → Fin 4 → ℝ := fun i j =>
    Real.arccos ⟪M.dualVertex i, M.dualVertex j⟫_ℝ
  let mu : ℝ := 2 * lam
  refine stationary_of_manuscript_variational_certificate M ell a mu ?_ ?_ ?_ ?_
  · intro i j hij
    have hρ := (dualVertex_inner_mem_Ioo M hij).2
    exact Real.arccos_pos.mpr hρ
  · intro i j hij
    have hρ := dualVertex_inner_mem_Ioo M hij
    have h1ρ2 : 0 < 1 - ⟪M.dualVertex i, M.dualVertex j⟫_ℝ ^ 2 := by nlinarith [hρ.1, hρ.2]
    have h1ρ : 0 < 1 + ⟪M.dualVertex i, M.dualVertex j⟫_ℝ := by linarith [hρ.1]
    exact div_pos (Real.sqrt_pos.mpr h1ρ2) h1ρ
  · intro i j hij
    have hρ := dualVertex_inner_mem_Ioo M hij
    have h1ρ2 : 0 < 1 - ⟪M.dualVertex i, M.dualVertex j⟫_ℝ ^ 2 := by nlinarith [hρ.1, hρ.2]
    have h1ρ : 0 < 1 + ⟪M.dualVertex i, M.dualVertex j⟫_ℝ := by linarith [hρ.1]
    have hsqrt_ne : √(1 - ⟪M.dualVertex i, M.dualVertex j⟫_ℝ ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr h1ρ2).ne'
    dsimp [ell, a]
    rw [stationaryKernel_eq_manuscriptPhi, Sphere3.manuscriptPhi, Sphere3.manuscriptPsi]
    field_simp [h1ρ.ne', hsqrt_ne]
  · intro i j hij
    obtain ⟨k, hk⟩ := exists_oppIdx_pair hij
    have hlam_k : gaussVolFDeriv x₀ (Pi.single k 1) =
        lam * stdAreaFDeriv x₀ (Pi.single k 1) := by
      have := congrArg (fun L : (Fin 6 → ℝ) →L[ℝ] ℝ => L (Pi.single k 1)) hlam
      simpa using this
    have hg_coord := gaussVolFDeriv_coord x₀ k
    have ha_coord := stdAreaFDeriv_coord hx₀ k
    have hxk : |x₀ k| < 1 := gramOpen_offdiag_abs_lt_one hx₀ k
    have h1xk2 : 0 < 1 - x₀ k ^ 2 := by
      rcases abs_cases (x₀ k) <;> nlinarith
    have hden_ne : √(1 - x₀ k ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1xk2).ne'
    rcases hk with hk_eq | hk_swap
    · dsimp only at ha_coord
      rw [hk_eq] at hg_coord ha_coord
      dsimp only at ha_coord
      have hdv :
          symUnitAdj x₀ i j / √(symUnitAdj x₀ i i * symUnitAdj x₀ j j) =
            ⟪M.dualVertex i, M.dualVertex j⟫_ℝ := by
        simpa [x₀] using (M.dualVertex_inner_eq_adj i j).symm
      rw [hdv] at hg_coord
      rw [dualVertex_inner_tetOf, dualHeight_tetOf, dualHeight_tetOf] at ha_coord
      rw [hg_coord, ha_coord] at hlam_k
      dsimp [ell, a, mu]
      have hmul := congrArg (fun r => r * (2 * √(1 - x₀ k ^ 2))) hlam_k
      field_simp [hden_ne] at hmul ⊢
      linarith
    · dsimp only at ha_coord
      rw [hk_swap] at hg_coord ha_coord
      dsimp only at ha_coord
      have hdv :
          symUnitAdj x₀ j i / √(symUnitAdj x₀ j j * symUnitAdj x₀ i i) =
            ⟪M.dualVertex i, M.dualVertex j⟫_ℝ := by
        rw [real_inner_comm]
        simpa [x₀] using (M.dualVertex_inner_eq_adj j i).symm
      have ha_sym :
          √(1 - ⟪(tetOf x₀ hx₀).dualVertex j, (tetOf x₀ hx₀).dualVertex i⟫_ℝ ^ 2) /
              (1 + ⟪(tetOf x₀ hx₀).dualVertex j, (tetOf x₀ hx₀).dualVertex i⟫_ℝ) =
            a i j := by
        rw [dualVertex_inner_tetOf, real_inner_comm]
      rw [hdv] at hg_coord
      rw [dualHeight_tetOf, dualHeight_tetOf, ha_sym] at ha_coord
      rw [hg_coord, ha_coord] at hlam_k
      dsimp [ell, mu]
      have hmul := congrArg (fun r => r * (2 * √(1 - x₀ k ^ 2))) hlam_k
      field_simp [hden_ne] at hmul ⊢
      linarith

end SphericalTetrahedron
