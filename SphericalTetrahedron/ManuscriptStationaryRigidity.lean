module

public import SphericalTetrahedron.ManuscriptRigidityBridge
public import SphericalTetrahedron.ManuscriptFaceProjection
public import SphericalTetrahedron.ManuscriptTriangleOrdering
public import SphericalTetrahedron.StationaryEqualHeights
public import SphericalTetrahedron.DualPolarity

@[expose] public section

/-!
# Global stationary rigidity for spherical tetrahedra

This module completes Step 3 of the manuscript proof: every stationary
spherical tetrahedron `T.Stationary` is regular (`T.Regular`).

Starting from `T.Stationary`, we identify the dual vertices and normal dual
axis, show each complementary 3-vertex triple of normalized heights lies in
`triangleDomain` with common `manuscriptFaceEnergy` equal to
`(c⁻¹)^2 * (‖T.normalDualAxis‖^2 - 1)`, sort the four heights, and apply
`manuscriptFaceEnergy_strict_first`, `manuscriptFaceEnergy_strict_second`, and
(after equating the top three heights) `manuscriptFaceEnergy_iso_lt`, concluding
with `stationary_regular_of_equal_dual_heights`.
-/

noncomputable section

namespace SphericalTetrahedron

open scoped InnerProductSpace BigOperators

theorem dualVertex_inner_mem_Ioo (T : SphericalTetrahedron) {i j : Fin 4} (hij : i ≠ j) :
    ⟪T.dualVertex i, T.dualVertex j⟫_ℝ ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hi : ‖T.dualVertex i‖ = 1 := T.dualVertex_norm i
  have hj : ‖T.dualVertex j‖ = 1 := T.dualVertex_norm j
  have hplus_ne : T.dualVertex i + T.dualVertex j ≠ 0 := by
    intro h0
    let c : Fin 4 → ℝ := fun k => if k = i then 1 else if k = j then 1 else 0
    have hsum : ∑ k : Fin 4, c k • T.dualVertex k = 0 := by
      have hcard : ({i, j} : Finset (Fin 4)).card = 2 := by
        simp [Finset.card_insert_of_notMem, hij]
      have hsub : ∑ k : Fin 4, c k • T.dualVertex k =
          ∑ k ∈ ({i, j} : Finset (Fin 4)), c k • T.dualVertex k := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) ?_
        intro k _ hk
        have hki : k ≠ i := fun h => hk (by simp [h])
        have hkj : k ≠ j := fun h => hk (by simp [h])
        simp [c, hki, hkj]
      rw [hsub, Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
      simp [c, hij.symm, h0]
    have hzero := Fintype.linearIndependent_iff.mp T.dualVertex_linearIndependent c hsum i
    simp [c] at hzero
  have hminus_ne : T.dualVertex i - T.dualVertex j ≠ 0 := by
    intro h0
    let c : Fin 4 → ℝ := fun k => if k = i then 1 else if k = j then (-1 : ℝ) else 0
    have hsum : ∑ k : Fin 4, c k • T.dualVertex k = 0 := by
      have hsub : ∑ k : Fin 4, c k • T.dualVertex k =
          ∑ k ∈ ({i, j} : Finset (Fin 4)), c k • T.dualVertex k := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) ?_
        intro k _ hk
        have hki : k ≠ i := fun h => hk (by simp [h])
        have hkj : k ≠ j := fun h => hk (by simp [h])
        simp [c, hki, hkj]
      rw [hsub, Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
      simp [c, hij.symm, sub_eq_zero.mp h0]
    have hzero := Fintype.linearIndependent_iff.mp T.dualVertex_linearIndependent c hsum i
    simp [c] at hzero
  have hp1 : 0 < ‖T.dualVertex i + T.dualVertex j‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hplus_ne)
  have hm1 : 0 < ‖T.dualVertex i - T.dualVertex j‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hminus_ne)
  rw [norm_add_sq_real, hi, hj] at hp1
  rw [norm_sub_sq_real, hi, hj] at hm1
  exact ⟨by linarith, by linarith⟩

theorem stationary_dual_kernel_equation (T : SphericalTetrahedron) (hT : T.Stationary) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ i j : Fin 4, i ≠ j →
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
          c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ =
            stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
  rcases hT with ⟨v, q, c, hc, hv_norm, hv_orth, hv_pos, hq, hker⟩
  have hv_eq : ∀ j : Fin 4, v j = T.dualVertex j := by
    intro j
    have hcoord :
        T.normalCoordinatesEquiv (v j) =
          T.normalCoordinatesEquiv ((⟪T.normal j, v j⟫_ℝ) • T.normalDualRay j) := by
      ext i
      change ⟪T.normal i, v j⟫_ℝ =
        T.normalCoordinatesEquiv ((⟪T.normal j, v j⟫_ℝ) • T.normalDualRay j) i
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      change ⟪T.normal i, v j⟫_ℝ = ⟪T.normal j, v j⟫_ℝ * ⟪T.normal i, T.normalDualRay j⟫_ℝ
      rw [T.normalDualRay_inner]
      by_cases hij : i = j
      · subst hij; simp
      · rw [hv_orth i j hij]; simp [hij]
    have hv_ray : v j = (⟪T.normal j, v j⟫_ℝ) • T.normalDualRay j :=
      T.normalCoordinatesEquiv.injective hcoord
    have hnorm := congrArg norm hv_ray
    rw [hv_norm j, norm_smul, Real.norm_eq_abs, abs_of_pos (hv_pos j)] at hnorm
    have hray_pos : 0 < ‖T.normalDualRay j‖ := norm_pos_iff.mpr (T.normalDualRay_ne_zero j)
    have hcoeff : ⟪T.normal j, v j⟫_ℝ = ‖T.normalDualRay j‖⁻¹ := by
      calc
        ⟪T.normal j, v j⟫_ℝ = (⟪T.normal j, v j⟫_ℝ * ‖T.normalDualRay j‖) * ‖T.normalDualRay j‖⁻¹ := by
          field_simp [hray_pos.ne']
        _ = 1 * ‖T.normalDualRay j‖⁻¹ := by rw [← hnorm]
        _ = ‖T.normalDualRay j‖⁻¹ := one_mul _
    rw [hv_ray, hcoeff]
    rfl
  have hq_eq : q = T.normalDualAxis := by
    apply T.normalCoordinatesEquiv.injective
    ext i
    change ⟪T.normal i, q⟫_ℝ = ⟪T.normal i, T.normalDualAxis⟫_ℝ
    rw [hq i, T.normalDualAxis_inner i]
  refine ⟨c, hc, ?_⟩
  intro i j hij
  have heq := hker i j hij
  rw [hv_eq i, hv_eq j, hq_eq] at heq
  calc
    c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ
      = c⁻¹ * (⟪T.normalDualAxis, T.dualVertex i⟫_ℝ + ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) := by
          ring
    _ = c⁻¹ * (c * stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ) := by rw [heq]
    _ = stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
          field_simp [hc]

private theorem gram_det_pos_of_linearIndependent (u₁ u₂ u₃ : E4)
    (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) (hu₃ : ‖u₃‖ = 1)
    (hind : LinearIndependent ℝ ![u₁, u₂, u₃]) :
    0 < Sphere3.triangleGramDet ⟪u₂, u₃⟫_ℝ ⟪u₁, u₃⟫_ℝ ⟪u₁, u₂⟫_ℝ := by
  set k₂₃ : ℝ := ⟪u₂, u₃⟫_ℝ
  set k₁₃ : ℝ := ⟪u₁, u₃⟫_ℝ
  set k₁₂ : ℝ := ⟪u₁, u₂⟫_ℝ
  have hu1_sq : ⟪u₁, u₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu₁]; norm_num
  have hu2_sq : ⟪u₂, u₂⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu₂]; norm_num
  have hu3_sq : ⟪u₃, u₃⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu₃]; norm_num
  have hw_ne : u₂ - k₂₃ • u₃ ≠ 0 := by
    intro h0
    let c : Fin 3 → ℝ := ![0, 1, -k₂₃]
    have hsum : ∑ m : Fin 3, c m • ![u₁, u₂, u₃] m = 0 := by
      simp only [Fin.sum_univ_three, c, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, zero_smul, one_smul, zero_add, neg_smul]
      simpa [sub_eq_add_neg] using h0
    have h1 := Fintype.linearIndependent_iff.mp hind c hsum 1
    simp [c] at h1
  have h1k23 : 0 < 1 - k₂₃ ^ 2 := by
    have hpos : 0 < ‖u₂ - k₂₃ • u₃‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw_ne)
    rw [← real_inner_self_eq_norm_sq] at hpos
    have hnorm_eq : ⟪u₂ - k₂₃ • u₃, u₂ - k₂₃ • u₃⟫_ℝ = 1 - k₂₃ ^ 2 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_left, hu2_sq, hu3_sq]
      have h32 : ⟪u₃, u₂⟫_ℝ = k₂₃ := by rw [real_inner_comm]
      rw [h32]
      ring
    linarith
  let v : E4 := (1 - k₂₃ ^ 2) • u₁ + (k₁₃ * k₂₃ - k₁₂) • u₂ + (k₁₂ * k₂₃ - k₁₃) • u₃
  have hv_ne : v ≠ 0 := by
    intro h0
    let c : Fin 3 → ℝ := ![1 - k₂₃ ^ 2, k₁₃ * k₂₃ - k₁₂, k₁₂ * k₂₃ - k₁₃]
    have hsum : ∑ m : Fin 3, c m • ![u₁, u₂, u₃] m = 0 := by
      simp only [Fin.sum_univ_three, c, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      exact h0
    have hzero := Fintype.linearIndependent_iff.mp hind c hsum 0
    simp [c] at hzero
    linarith
  have hv_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv_ne)
  rw [← real_inner_self_eq_norm_sq] at hv_sq_pos
  have hv1 : ⟪u₁, v⟫_ℝ = Sphere3.triangleGramDet k₂₃ k₁₃ k₁₂ := by
    dsimp only [v]
    rw [inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, hu1_sq]
    change (1 - k₂₃ ^ 2) * 1 + (k₁₃ * k₂₃ - k₁₂) * k₁₂ + (k₁₂ * k₂₃ - k₁₃) * k₁₃ =
      Sphere3.triangleGramDet k₂₃ k₁₃ k₁₂
    unfold Sphere3.triangleGramDet
    ring
  have hv2 : ⟪u₂, v⟫_ℝ = 0 := by
    dsimp only [v]
    rw [inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, hu2_sq]
    have h21 : ⟪u₂, u₁⟫_ℝ = k₁₂ := by rw [real_inner_comm]
    rw [h21]
    change (1 - k₂₃ ^ 2) * k₁₂ + (k₁₃ * k₂₃ - k₁₂) * 1 + (k₁₂ * k₂₃ - k₁₃) * k₂₃ = 0
    ring
  have hv3 : ⟪u₃, v⟫_ℝ = 0 := by
    dsimp only [v]
    rw [inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, hu3_sq]
    have h31 : ⟪u₃, u₁⟫_ℝ = k₁₃ := by rw [real_inner_comm]
    have h32 : ⟪u₃, u₂⟫_ℝ = k₂₃ := by rw [real_inner_comm]
    rw [h31, h32]
    change (1 - k₂₃ ^ 2) * k₁₃ + (k₁₃ * k₂₃ - k₁₂) * k₂₃ + (k₁₂ * k₂₃ - k₁₃) * 1 = 0
    ring
  have hvv : ⟪v, v⟫_ℝ = (1 - k₂₃ ^ 2) * Sphere3.triangleGramDet k₂₃ k₁₃ k₁₂ := by
    calc
      ⟪v, v⟫_ℝ =
          (1 - k₂₃ ^ 2) * ⟪u₁, v⟫_ℝ + (k₁₃ * k₂₃ - k₁₂) * ⟪u₂, v⟫_ℝ +
            (k₁₂ * k₂₃ - k₁₃) * ⟪u₃, v⟫_ℝ := by
          nth_rw 1 [show v = (1 - k₂₃ ^ 2) • u₁ + (k₁₃ * k₂₃ - k₁₂) • u₂ + (k₁₂ * k₂₃ - k₁₃) • u₃ from rfl]
          rw [inner_add_left, inner_add_left,
            real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
      _ = (1 - k₂₃ ^ 2) * Sphere3.triangleGramDet k₂₃ k₁₃ k₁₂ := by
          rw [hv1, hv2, hv3]; ring
  rw [hvv] at hv_sq_pos
  exact (mul_pos_iff_of_pos_left h1k23).mp hv_sq_pos

private theorem fin4_sum_of_distinct {i j₁ j₂ j₃ : Fin 4}
    (hi1 : i ≠ j₁) (hi2 : i ≠ j₂) (hi3 : i ≠ j₃)
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃)
    (f : Fin 4 → E4) :
    ∑ k : Fin 4, f k = f i + f j₁ + f j₂ + f j₃ := by
  have hcard : ({i, j₁, j₂, j₃} : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
    · simp [hi1, hi2, hi3]
  have huniv : ({i, j₁, j₂, j₃} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  rw [← huniv, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · abel
  · simp [h23]
  · simp [h12, h13]
  · simp [hi1, hi2, hi3]

private theorem triple_dualVertex_linearIndependent (T : SphericalTetrahedron) {j₁ j₂ j₃ : Fin 4}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) :
    LinearIndependent ℝ ![T.dualVertex j₁, T.dualVertex j₂, T.dualVertex j₃] := by
  let σ : Fin 3 → Fin 4 := ![j₁, j₂, j₃]
  have hσ_inj : Function.Injective σ := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact absurd hab h12 | exact absurd hab h13 |
        exact absurd hab h23 | exact absurd hab.symm h12 |
        exact absurd hab.symm h13 | exact absurd hab.symm h23
  have hcomp := T.dualVertex_linearIndependent.comp σ hσ_inj
  convert hcomp using 1
  ext m
  fin_cases m <;> rfl

theorem stationary_face_triple_mem_and_energy (T : SphericalTetrahedron)
    {c : ℝ} (_hc : c ≠ 0)
    (hker : ∀ i j : Fin 4, i ≠ j →
      c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ =
          stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ)
    {i j₁ j₂ j₃ : Fin 4}
    (hi1 : i ≠ j₁) (hi2 : i ≠ j₂) (hi3 : i ≠ j₃)
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) :
    (c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j₁⟫_ℝ,
     c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j₂⟫_ℝ,
     c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j₃⟫_ℝ) ∈ triangleDomain ∧
    manuscriptFaceEnergy manuscriptKernelInverse
      (c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j₁⟫_ℝ)
      (c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j₂⟫_ℝ)
      (c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j₃⟫_ℝ) =
      (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) := by
  set t : Fin 4 → ℝ := fun k => c⁻¹ * ⟪T.normalDualAxis, T.dualVertex k⟫_ℝ
  have hsum_mem : ∀ {p q : Fin 4}, p ≠ q → t p + t q ∈ Set.Ioo (0 : ℝ) 2 := by
    intro p q hpq
    change c⁻¹ * ⟪T.normalDualAxis, T.dualVertex p⟫_ℝ +
      c⁻¹ * ⟪T.normalDualAxis, T.dualVertex q⟫_ℝ ∈ Set.Ioo (0 : ℝ) 2
    rw [hker p q hpq]
    exact stationaryKernel_mapsTo (T.dualVertex_inner_mem_Ioo hpq)
  have hginv : ∀ {p q : Fin 4}, p ≠ q →
      manuscriptKernelInverse (t p + t q) = ⟪T.dualVertex p, T.dualVertex q⟫_ℝ := by
    intro p q hpq
    change manuscriptKernelInverse
      (c⁻¹ * ⟪T.normalDualAxis, T.dualVertex p⟫_ℝ +
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex q⟫_ℝ) =
      ⟪T.dualVertex p, T.dualVertex q⟫_ℝ
    rw [hker p q hpq]
    exact manuscriptKernelInverse_stationaryKernel _ (T.dualVertex_inner_mem_Ioo hpq)
  have hj23_mem := hsum_mem h23
  have hj13_mem := hsum_mem h13
  have hj12_mem := hsum_mem h12
  have hk23 : manuscriptKernelInverse (t j₂ + t j₃) = ⟪T.dualVertex j₂, T.dualVertex j₃⟫_ℝ :=
    hginv h23
  have hk13 : manuscriptKernelInverse (t j₁ + t j₃) = ⟪T.dualVertex j₁, T.dualVertex j₃⟫_ℝ :=
    hginv h13
  have hk12 : manuscriptKernelInverse (t j₁ + t j₂) = ⟪T.dualVertex j₁, T.dualVertex j₂⟫_ℝ :=
    hginv h12
  have hdet_pos :
      0 < Sphere3.triangleGramDet
        (manuscriptKernelInverse (t j₂ + t j₃))
        (manuscriptKernelInverse (t j₁ + t j₃))
        (manuscriptKernelInverse (t j₁ + t j₂)) := by
    rw [hk23, hk13, hk12]
    exact gram_det_pos_of_linearIndependent (T.dualVertex j₁) (T.dualVertex j₂) (T.dualVertex j₃)
      (T.dualVertex_norm j₁) (T.dualVertex_norm j₂) (T.dualVertex_norm j₃)
      (T.triple_dualVertex_linearIndependent h12 h13 h23)
  have hmem : (t j₁, t j₂, t j₃) ∈ triangleDomain :=
    ⟨hj23_mem, hj13_mem, hj12_mem, hdet_pos⟩
  let w : E4 := T.normalDualAxis - T.normal i
  have hw_exp : w = ∑ k : Fin 4, ⟪T.normal k, w⟫_ℝ • T.normalDualRay k := by
    apply T.normalCoordinatesEquiv.injective
    ext m
    change ⟪T.normal m, w⟫_ℝ =
      T.normalCoordinatesEquiv (∑ k : Fin 4, ⟪T.normal k, w⟫_ℝ • T.normalDualRay k) m
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change ⟪T.normal m, w⟫_ℝ = ∑ k : Fin 4, ⟪T.normal k, w⟫_ℝ * ⟪T.normal m, T.normalDualRay k⟫_ℝ
    rw [Finset.sum_eq_single m]
    · rw [T.normalDualRay_inner]; simp
    · intro k _ hkm
      rw [T.normalDualRay_inner]
      simp [hkm.symm]
    · intro hm; exact absurd (Finset.mem_univ m) hm
  have hwi : ⟪T.normal i, w⟫_ℝ = 0 := by
    dsimp only [w]
    rw [inner_sub_right, T.normalDualAxis_inner i, real_inner_self_eq_norm_sq, T.unit i]
    norm_num
  have hray_smul : ∀ k : Fin 4, T.normalDualRay k = ‖T.normalDualRay k‖ • T.dualVertex k := by
    intro k
    have hpos : 0 < ‖T.normalDualRay k‖ := norm_pos_iff.mpr (T.normalDualRay_ne_zero k)
    unfold dualVertex
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hw_three :
      w = (⟪T.normal j₁, w⟫_ℝ * ‖T.normalDualRay j₁‖) • T.dualVertex j₁ +
          (⟪T.normal j₂, w⟫_ℝ * ‖T.normalDualRay j₂‖) • T.dualVertex j₂ +
          (⟪T.normal j₃, w⟫_ℝ * ‖T.normalDualRay j₃‖) • T.dualVertex j₃ := by
    calc
      w = ∑ k : Fin 4, ⟪T.normal k, w⟫_ℝ • T.normalDualRay k := hw_exp
      _ = ⟪T.normal i, w⟫_ℝ • T.normalDualRay i +
          ⟪T.normal j₁, w⟫_ℝ • T.normalDualRay j₁ +
          ⟪T.normal j₂, w⟫_ℝ • T.normalDualRay j₂ +
          ⟪T.normal j₃, w⟫_ℝ • T.normalDualRay j₃ :=
          fin4_sum_of_distinct hi1 hi2 hi3 h12 h13 h23 _
      _ = ⟪T.normal j₁, w⟫_ℝ • T.normalDualRay j₁ +
          ⟪T.normal j₂, w⟫_ℝ • T.normalDualRay j₂ +
          ⟪T.normal j₃, w⟫_ℝ • T.normalDualRay j₃ := by rw [hwi, zero_smul, zero_add]
      _ = (⟪T.normal j₁, w⟫_ℝ * ‖T.normalDualRay j₁‖) • T.dualVertex j₁ +
          (⟪T.normal j₂, w⟫_ℝ * ‖T.normalDualRay j₂‖) • T.dualVertex j₂ +
          (⟪T.normal j₃, w⟫_ℝ * ‖T.normalDualRay j₃‖) • T.dualVertex j₃ := by
          have hterm : ∀ k : Fin 4,
              ⟪T.normal k, w⟫_ℝ • T.normalDualRay k =
                (⟪T.normal k, w⟫_ℝ * ‖T.normalDualRay k‖) • T.dualVertex k := fun k => by
            calc
              ⟪T.normal k, w⟫_ℝ • T.normalDualRay k =
                  ⟪T.normal k, w⟫_ℝ • (‖T.normalDualRay k‖ • T.dualVertex k) := by
                    conv_lhs => rw [hray_smul k]
              _ = (⟪T.normal k, w⟫_ℝ * ‖T.normalDualRay k‖) • T.dualVertex k := by
                    rw [smul_smul]
          rw [hterm j₁, hterm j₂, hterm j₃]
  let a₁ : ℝ := c⁻¹ * (⟪T.normal j₁, w⟫_ℝ * ‖T.normalDualRay j₁‖)
  let a₂ : ℝ := c⁻¹ * (⟪T.normal j₂, w⟫_ℝ * ‖T.normalDualRay j₂‖)
  let a₃ : ℝ := c⁻¹ * (⟪T.normal j₃, w⟫_ℝ * ‖T.normalDualRay j₃‖)
  have hcw :
      c⁻¹ • w = a₁ • T.dualVertex j₁ + a₂ • T.dualVertex j₂ + a₃ • T.dualVertex j₃ := by
    calc
      c⁻¹ • w = c⁻¹ • ((⟪T.normal j₁, w⟫_ℝ * ‖T.normalDualRay j₁‖) • T.dualVertex j₁ +
          (⟪T.normal j₂, w⟫_ℝ * ‖T.normalDualRay j₂‖) • T.dualVertex j₂ +
          (⟪T.normal j₃, w⟫_ℝ * ‖T.normalDualRay j₃‖) • T.dualVertex j₃) := by rw [← hw_three]
      _ = a₁ • T.dualVertex j₁ + a₂ • T.dualVertex j₂ + a₃ • T.dualVertex j₃ := by
          simp only [smul_add, smul_smul]; rfl
  have hcw_inner : ∀ {k : Fin 4}, i ≠ k → ⟪c⁻¹ • w, T.dualVertex k⟫_ℝ = t k := by
    intro k hik
    rw [real_inner_smul_left]
    dsimp only [w]
    rw [inner_sub_left]
    have horth : ⟪T.normal i, T.dualVertex k⟫_ℝ = 0 := T.dualVertex_offdiag i k hik
    rw [horth, sub_zero]
  set k₂₃ : ℝ := ⟪T.dualVertex j₂, T.dualVertex j₃⟫_ℝ
  set k₁₃ : ℝ := ⟪T.dualVertex j₁, T.dualVertex j₃⟫_ℝ
  set k₁₂ : ℝ := ⟪T.dualVertex j₁, T.dualVertex j₂⟫_ℝ
  have hu1_sq : ⟪T.dualVertex j₁, T.dualVertex j₁⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, T.dualVertex_norm j₁]; norm_num
  have hu2_sq : ⟪T.dualVertex j₂, T.dualVertex j₂⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, T.dualVertex_norm j₂]; norm_num
  have hu3_sq : ⟪T.dualVertex j₃, T.dualVertex j₃⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, T.dualVertex_norm j₃]; norm_num
  have ht1 : t j₁ = a₁ + k₁₂ * a₂ + k₁₃ * a₃ := by
    rw [← hcw_inner hi1, hcw, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hu1_sq]
    have h21 : ⟪T.dualVertex j₂, T.dualVertex j₁⟫_ℝ = k₁₂ := by rw [real_inner_comm]
    have h31 : ⟪T.dualVertex j₃, T.dualVertex j₁⟫_ℝ = k₁₃ := by rw [real_inner_comm]
    rw [h21, h31]
    ring
  have ht2 : t j₂ = k₁₂ * a₁ + a₂ + k₂₃ * a₃ := by
    rw [← hcw_inner hi2, hcw, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hu2_sq]
    have h32 : ⟪T.dualVertex j₃, T.dualVertex j₂⟫_ℝ = k₂₃ := by rw [real_inner_comm]
    rw [h32]
    ring
  have ht3 : t j₃ = k₁₃ * a₁ + k₂₃ * a₂ + a₃ := by
    rw [← hcw_inner hi3, hcw, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, hu3_sq]
    ring
  have hquad :
      (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) =
        a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + 2 * k₁₂ * a₁ * a₂ + 2 * k₁₃ * a₁ * a₃ + 2 * k₂₃ * a₂ * a₃ := by
    have hnorm_cw : ‖c⁻¹ • w‖ ^ 2 = (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, T.manuscript_face_projection_norm_sq i]
    have hdot_cw :
        ‖c⁻¹ • w‖ ^ 2 =
          a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + 2 * k₁₂ * a₁ * a₂ + 2 * k₁₃ * a₁ * a₃ + 2 * k₂₃ * a₂ * a₃ := by
      rw [← real_inner_self_eq_norm_sq, hcw]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hu1_sq, hu2_sq, hu3_sq]
      have h21 : ⟪T.dualVertex j₂, T.dualVertex j₁⟫_ℝ = ⟪T.dualVertex j₁, T.dualVertex j₂⟫_ℝ :=
        real_inner_comm _ _
      have h31 : ⟪T.dualVertex j₃, T.dualVertex j₁⟫_ℝ = ⟪T.dualVertex j₁, T.dualVertex j₃⟫_ℝ :=
        real_inner_comm _ _
      have h32 : ⟪T.dualVertex j₃, T.dualVertex j₂⟫_ℝ = ⟪T.dualVertex j₂, T.dualVertex j₃⟫_ℝ :=
        real_inner_comm _ _
      rw [h21, h31, h32]
      dsimp only [k₁₂, k₁₃, k₂₃]
      ring
    linarith
  have henergy :
      manuscriptFaceEnergy manuscriptKernelInverse (t j₁) (t j₂) (t j₃) =
        (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) := by
    unfold manuscriptFaceEnergy
    rw [hk23, hk13, hk12, ht1, ht2, ht3, hquad]
    exact Sphere3.triangleGramEnergy_of_gram_coefficients k₂₃ k₁₃ k₁₂ a₁ a₂ a₃
      (by rw [← hk23, ← hk13, ← hk12]; exact hdet_pos.ne')
  exact ⟨hmem, henergy⟩


theorem stationary_regular_manuscript (T : SphericalTetrahedron) (hT : T.Stationary) :
    T.Regular := by
  obtain ⟨c, hc, hker⟩ := stationary_dual_kernel_equation T hT
  set t : Fin 4 → ℝ := fun k => c⁻¹ * ⟪T.normalDualAxis, T.dualVertex k⟫_ℝ
  let σ : Equiv.Perm (Fin 4) := Tuple.sort (fun k : Fin 4 => -t k)
  have hmono : Monotone (fun k : Fin 4 => -t (σ k)) :=
    Tuple.monotone_sort (fun k : Fin 4 => -t k)
  have hant : Antitone (fun k : Fin 4 => t (σ k)) := by
    intro i j hij
    linarith [hmono hij]
  let p₀ := σ 0
  let p₁ := σ 1
  let p₂ := σ 2
  let p₃ := σ 3
  have h01 : p₀ ≠ p₁ := σ.injective.ne (by decide)
  have h02 : p₀ ≠ p₂ := σ.injective.ne (by decide)
  have h03 : p₀ ≠ p₃ := σ.injective.ne (by decide)
  have h12 : p₁ ≠ p₂ := σ.injective.ne (by decide)
  have h13 : p₁ ≠ p₃ := σ.injective.ne (by decide)
  have h23 : p₂ ≠ p₃ := σ.injective.ne (by decide)
  set a : ℝ := t p₀
  set b : ℝ := t p₁
  set c' : ℝ := t p₂
  set d : ℝ := t p₃
  have hba : b ≤ a := hant (by decide : (0 : Fin 4) ≤ 1)
  have hcb : c' ≤ b := hant (by decide : (1 : Fin 4) ≤ 2)
  have hdc : d ≤ c' := hant (by decide : (2 : Fin 4) ≤ 3)
  have hf_abc := stationary_face_triple_mem_and_energy T hc hker h03.symm h13.symm h23.symm h01 h02 h12
  have hf_abd := stationary_face_triple_mem_and_energy T hc hker h02.symm h12.symm h23 h01 h03 h13
  have hf_acd := stationary_face_triple_mem_and_energy T hc hker h01.symm h12 h13 h02 h03 h23
  have hf_bcd := stationary_face_triple_mem_and_energy T hc hker h01 h02 h03 h12 h13 h23
  change (a, b, c') ∈ triangleDomain ∧
    manuscriptFaceEnergy manuscriptKernelInverse a b c' =
      (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) at hf_abc
  change (a, b, d) ∈ triangleDomain ∧
    manuscriptFaceEnergy manuscriptKernelInverse a b d =
      (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) at hf_abd
  change (a, c', d) ∈ triangleDomain ∧
    manuscriptFaceEnergy manuscriptKernelInverse a c' d =
      (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) at hf_acd
  change (b, c', d) ∈ triangleDomain ∧
    manuscriptFaceEnergy manuscriptKernelInverse b c' d =
      (c⁻¹) ^ 2 * (‖T.normalDualAxis‖ ^ 2 - 1) at hf_bcd
  have hab_eq : a = b := by
    by_contra hne
    have hlt_ba : b < a := lt_of_le_of_ne hba (Ne.symm hne)
    have hlt_E := manuscriptFaceEnergy_strict_first hdc hcb hlt_ba hf_bcd.1 hf_acd.1
    linarith [hf_acd.2, hf_bcd.2]
  have hbc_eq : b = c' := by
    by_contra hne
    have hlt_cb : c' < b := lt_of_le_of_ne hcb (Ne.symm hne)
    have hdom_bda : (b, d, a) ∈ triangleDomain :=
      triangleDomain_swap23 (triangleDomain_swap12 hf_abd.1)
    have hdom_cda : (c', d, a) ∈ triangleDomain :=
      triangleDomain_swap23 (triangleDomain_swap12 hf_acd.1)
    have hlt_E := manuscriptFaceEnergy_strict_second hdc hlt_cb hba hdom_cda hdom_bda
    have heq_bda :
        manuscriptFaceEnergy manuscriptKernelInverse b d a =
          manuscriptFaceEnergy manuscriptKernelInverse a b d := by
      rw [manuscriptFaceEnergy_swap23, manuscriptFaceEnergy_swap12]
    have heq_cda :
        manuscriptFaceEnergy manuscriptKernelInverse c' d a =
          manuscriptFaceEnergy manuscriptKernelInverse a c' d := by
      rw [manuscriptFaceEnergy_swap23, manuscriptFaceEnergy_swap12]
    linarith [hlt_E, heq_bda, heq_cda, hf_abd.2, hf_acd.2]
  have hcd_eq : c' = d := by
    by_contra hne
    have hlt_dc : d < c' := lt_of_le_of_ne hdc (Ne.symm hne)
    have hlt_da : d < a := lt_of_lt_of_le hlt_dc (hcb.trans hba)
    have hdom_daa : (d, a, a) ∈ triangleDomain := by
      have h1 : (a, a, d) ∈ triangleDomain := by
        simpa [← hab_eq, ← hbc_eq] using hf_bcd.1
      exact triangleDomain_swap12 (triangleDomain_swap23 h1)
    have hdom_aaa : (a, a, a) ∈ triangleDomain := by
      simpa [← hab_eq, ← hbc_eq] using hf_abc.1
    have hlt_E := manuscriptFaceEnergy_iso_lt hlt_da hdom_daa hdom_aaa
    have heq_daa :
        manuscriptFaceEnergy manuscriptKernelInverse d a a =
          manuscriptFaceEnergy manuscriptKernelInverse a b d := by
      rw [← hab_eq, manuscriptFaceEnergy_swap12, manuscriptFaceEnergy_swap23]
    have heq_aaa :
        manuscriptFaceEnergy manuscriptKernelInverse a a a =
          manuscriptFaceEnergy manuscriptKernelInverse a b c' := by
      rw [← hbc_eq, ← hab_eq]
    linarith [hlt_E, heq_daa, heq_aaa, hf_abc.2, hf_abd.2]
  have hperm_eq : ∀ k : Fin 4, t (σ k) = a := by
    intro k
    fin_cases k
    · rfl
    · exact hab_eq.symm
    · exact (hab_eq.trans hbc_eq).symm
    · exact (hab_eq.trans (hbc_eq.trans hcd_eq)).symm
  have h_heights : ∀ i j : Fin 4,
      ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ = ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ := by
    intro i j
    have hi_eq : t i = a := by
      have := hperm_eq (σ.symm i)
      simpa using this
    have hj_eq : t j = a := by
      have := hperm_eq (σ.symm j)
      simpa using this
    have ht_eq : c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ =
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ :=
      hi_eq.trans hj_eq.symm
    exact mul_left_cancel₀ (inv_ne_zero hc) ht_eq
  exact stationary_regular_of_equal_dual_heights T hT h_heights

end SphericalTetrahedron
