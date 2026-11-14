module

public import SphericalTetrahedron.ManuscriptMeasureBridge
public import SphericalTetrahedron.ManuscriptGramChart
public import SphericalTetrahedron.ManuscriptAreaGradient
public import Sphere3.ManuscriptPsiIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Gaussian integral representation and Schläfli first-variation formula

This file implements the Gaussian cone integral representation of the spherical
volume of a nondegenerate spherical tetrahedron in the Gram chart `gramOpen`,
proves its continuous differentiability via dominated differentiation under the
integral sign, and evaluates the partial derivatives by two-step 1D integration
by parts plus the manuscript's `manuscriptPsi` integral identity.
-/

noncomputable section

open scoped InnerProductSpace Matrix
open MeasureTheory Filter Topology

namespace SphericalTetrahedron

/-! ### Gaussian representation on `gramOpen` -/

/-- Open positive orthant `(0, ∞)^4` in `Fin 4 → ℝ`. -/
def orthant4 : Set (Fin 4 → ℝ) :=
  Set.univ.pi fun _ : Fin 4 => Set.Ioi (0 : ℝ)

theorem measurableSet_orthant4 : MeasurableSet orthant4 :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

/-- Quadratic form `z ↦ zᵀ (symUnitInv x) z`. -/
def gaussQuadForm (x : Fin 6 → ℝ) (z : Fin 4 → ℝ) : ℝ :=
  z ⬝ᵥ (symUnitInv x *ᵥ z)

/-- Gaussian integrand `z ↦ exp (- zᵀ (symUnitInv x) z)`. -/
def gaussIntegrand (x : Fin 6 → ℝ) (z : Fin 4 → ℝ) : ℝ :=
  Real.exp (-gaussQuadForm x z)

/-- Unnormalized Gaussian orthant integral. -/
def gaussInt (x : Fin 6 → ℝ) : ℝ :=
  ∫ z in orthant4, gaussIntegrand x z

/-- Normalized Gaussian Gram-chart volume function.
Matches `(2 * sphereScale 3)⁻¹ * T.volume` at `x = gramPoint T`. -/
def gaussVolGram (x : Fin 6 → ℝ) : ℝ :=
  (Real.sqrt (symUnitMat x).det)⁻¹ * gaussInt x

/-- Closed-form Schläfli gradient of `gaussVolGram` in the Gram chart `gramOpen`. -/
def gaussVolFDeriv (x : Fin 6 → ℝ) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin 6,
    (((1 / 4 : ℝ) *
        Real.arccos (symUnitAdj x (oppIdx k).1 (oppIdx k).2 /
          Real.sqrt (symUnitAdj x (oppIdx k).1 (oppIdx k).1 *
            symUnitAdj x (oppIdx k).2 (oppIdx k).2))) /
      Real.sqrt (1 - x k ^ 2)) • coordProj6 k

/-! ### Measure bridge: `T.volume = (2 * sphereScale 3) * gaussVolGram (gramPoint T)` -/

/-- Normal matrix `N` whose `i`-th row is `T.normal i`. -/
def normalMat (T : SphericalTetrahedron) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => T.normal i j

theorem normalMat_mul_transpose (T : SphericalTetrahedron) :
    normalMat T * (normalMat T)ᵀ = symUnitMat (gramPoint T) := by
  ext i j
  rw [Matrix.mul_apply, symUnitMat_gramPoint]
  simp only [normalMat, Matrix.of_apply, Matrix.transpose_apply]
  rw [real_inner_comm]
  simp [PiLp.inner_apply, RCLike.inner_apply]

theorem normalMat_det_sq (T : SphericalTetrahedron) :
    (normalMat T).det ^ 2 = (symUnitMat (gramPoint T)).det := by
  have h := congrArg Matrix.det (normalMat_mul_transpose T)
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq] at h
  exact h

theorem normalMat_det_ne_zero (T : SphericalTetrahedron) : (normalMat T).det ≠ 0 := by
  have hpos := gramOpen_det_pos (gramPoint_mem_gramOpen T)
  rw [← normalMat_det_sq T] at hpos
  exact fun h0 => by simp [h0] at hpos

theorem abs_normalMat_det (T : SphericalTetrahedron) :
    |(normalMat T).det| = Real.sqrt (symUnitMat (gramPoint T)).det := by
  rw [← normalMat_det_sq T, Real.sqrt_sq_eq_abs]

theorem normalMat_mulVec_ofLp (T : SphericalTetrahedron) (y : E4) (i : Fin 4) :
    (normalMat T *ᵥ y.ofLp) i = ⟪T.normal i, y⟫_ℝ := by
  simp [normalMat, Matrix.mulVec, dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem gaussQuadForm_eq_norm_sq (T : SphericalTetrahedron) (u z : Fin 4 → ℝ)
    (hz : normalMat T *ᵥ u = z) :
    u ⬝ᵥ u = gaussQuadForm (gramPoint T) z := by
  set x := gramPoint T
  have hx := gramPoint_mem_gramOpen T
  have hdet := gramOpen_det_ne_zero hx
  have hmul : symUnitMat x * symUnitInv x = 1 := symUnitMat_mul_inv x hdet
  set v : Fin 4 → ℝ := (normalMat T)ᵀ *ᵥ (symUnitInv x *ᵥ z)
  have hv : normalMat T *ᵥ v = z := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, normalMat_mul_transpose T]
    change symUnitMat x *ᵥ (symUnitInv x *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have huv : u = v := by
    have hsub : normalMat T *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, hz, hv, sub_self]
    have hinv : (normalMat T)⁻¹ * normalMat T = 1 :=
      Matrix.nonsing_inv_mul (normalMat T) (isUnit_iff_ne_zero.mpr (normalMat_det_ne_zero T))
    have hzero : u - v = 0 := by
      calc
        u - v = ((1 : Matrix (Fin 4) (Fin 4) ℝ)) *ᵥ (u - v) := (Matrix.one_mulVec _).symm
        _ = ((normalMat T)⁻¹ * normalMat T) *ᵥ (u - v) := by rw [hinv]
        _ = (normalMat T)⁻¹ *ᵥ (normalMat T *ᵥ (u - v)) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = (normalMat T)⁻¹ *ᵥ 0 := by rw [hsub]
        _ = 0 := Matrix.mulVec_zero _
    exact sub_eq_zero.mp hzero
  calc
    u ⬝ᵥ u = u ⬝ᵥ ((normalMat T)ᵀ *ᵥ (symUnitInv x *ᵥ z)) := by
      dsimp only [v] at huv
      rw [← huv]
    _ = (normalMat T *ᵥ u) ⬝ᵥ (symUnitInv x *ᵥ z) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = z ⬝ᵥ (symUnitInv x *ᵥ z) := by rw [hz]
    _ = gaussQuadForm x z := rfl

private theorem radial_cube_exp_integral :
    ∫ r in Set.Ioi (0 : ℝ), r ^ 3 * Real.exp (-r ^ 2) = 1 / 2 := by
  let F : ℝ → ℝ := fun r => -(1 / 2 : ℝ) * (r ^ 2 + 1) * Real.exp (-r ^ 2)
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ), HasDerivAt F (r ^ 3 * Real.exp (-r ^ 2)) r := by
    intro r _
    have hpoly : HasDerivAt (fun t : ℝ => -(1 / 2 : ℝ) * (t ^ 2 + 1)) (-(1 / 2 : ℝ) * (2 * r)) r := by
      have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
        simpa using (hasDerivAt_pow 2 r)
      have h2 : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * r) r := by
        simpa using h1.add_const (1 : ℝ)
      exact h2.const_mul (-(1 / 2 : ℝ))
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2)) (Real.exp (-r ^ 2) * (-(2 * r))) r := by
      have hsq : HasDerivAt (fun t : ℝ => -(t ^ 2)) (-(2 * r)) r :=
        by simpa using (hasDerivAt_pow 2 r).fun_neg
      exact hsq.exp
    convert hpoly.mul hexp using 1
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hsqTop : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : 2 ≠ 0)
    have h1 : Tendsto (fun r : ℝ => r ^ 2 * Real.exp (-r ^ 2)) atTop (𝓝 0) := by
      have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hsqTop
      simpa [Function.comp_def, pow_one] using ht
    have h2 : Tendsto (fun r : ℝ => Real.exp (-r ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsqTop)
    have h3 : Tendsto (fun r : ℝ => -(1 / 2 : ℝ) * (r ^ 2 * Real.exp (-r ^ 2) + Real.exp (-r ^ 2)))
        atTop (𝓝 (-(1 / 2 : ℝ) * (0 + 0))) :=
      (h1.add h2).const_mul _
    simp only [add_zero, mul_zero] at h3
    refine h3.congr fun r => ?_
    dsimp [F]
    ring
  have hint : IntegrableOn (fun r : ℝ => r ^ 3 * Real.exp (-r ^ 2)) (Set.Ioi 0) MeasureTheory.volume := by
    have hdom : Integrable (fun r : ℝ => 2 * (r * Real.exp (-(1 / 2 : ℝ) * r ^ 2))) MeasureTheory.volume :=
      (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
    refine (hdom.integrableOn).mono' ?_ ?_
    · exact ((continuous_pow 3).mul (Real.continuous_exp.comp (Continuous.neg (continuous_pow 2)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      have hexp_ge : r ^ 2 / 2 + 1 ≤ Real.exp (r ^ 2 / 2) := Real.add_one_le_exp (r ^ 2 / 2)
      have hr2_le : r ^ 2 ≤ 2 * Real.exp (r ^ 2 / 2) := by linarith
      have hpow_nonneg : 0 ≤ r ^ 3 * Real.exp (-r ^ 2) :=
        mul_nonneg (pow_nonneg hr0 3) (Real.exp_pos _).le
      rw [Real.norm_of_nonneg hpow_nonneg]
      calc
        r ^ 3 * Real.exp (-r ^ 2)
            = r * r ^ 2 * (Real.exp (-(r ^ 2 / 2)) * Real.exp (-(r ^ 2 / 2))) := by
              rw [← Real.exp_add]; ring_nf
        _ ≤ r * (2 * Real.exp (r ^ 2 / 2)) * (Real.exp (-(r ^ 2 / 2)) * Real.exp (-(r ^ 2 / 2))) := by
              gcongr
        _ = 2 * (r * (Real.exp (r ^ 2 / 2) * Real.exp (-(r ^ 2 / 2))) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
              ring_nf
        _ = 2 * (r * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hF0 : F 0 = -(1 / 2 : ℝ) := by simp [F]
  linarith

private theorem volume_cone_gaussian_eq_sphere (T : SphericalTetrahedron) :
    ∫ y in {y : E4 | ∀ i : Fin 4, 0 < ⟪T.normal i, y⟫_ℝ}, Real.exp (-‖y‖ ^ 2) =
      (1 / 2 : ℝ) * MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' T.body) := by
  let coneT : Set E4 := {y : E4 | ∀ i : Fin 4, 0 < ⟪T.normal i, y⟫_ℝ}
  let posCone : Set E4 := {y : E4 | y ≠ 0 ∧ (‖y‖⁻¹ • y) ∈ T.body}
  have hposCone_eq : posCone = {y : E4 | y ≠ 0} ∩ ⋂ i : Fin 4, {y : E4 | 0 ≤ ⟪T.normal i, y⟫_ℝ} := by
    ext y
    simp only [posCone, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      T.body_eq_sphere_inter_cone, Metric.mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨hy0, _, hcone⟩
      refine ⟨hy0, fun i => ?_⟩
      have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hi := hcone i
      rw [inner_smul_right] at hi
      exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp hi
    · rintro ⟨hy0, hcone⟩
      have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      refine ⟨hy0, ?_, fun i => ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      · rw [inner_smul_right]
        exact mul_nonneg (inv_nonneg.mpr hn.le) (hcone i)
  have hposCone_meas : MeasurableSet posCone := by
    rw [hposCone_eq]
    refine (measurableSet_singleton (0 : E4)).compl.inter ?_
    refine MeasurableSet.iInter fun i => ?_
    exact isClosed_le continuous_const (continuous_const.inner continuous_id) |>.measurableSet
  have hcone_ae : (coneT : Set E4) =ᵐ[MeasureTheory.volume] posCone := by
    rw [Filter.eventuallyEqSet_iff]
    have hnull : MeasureTheory.volume
        (⋃ i : Fin 4, (LinearMap.ker (innerSL ℝ (T.normal i) : E4 →ₗ[ℝ] ℝ) : Set E4)) = 0 := by
      rw [measure_iUnion_null_iff]
      intro i
      refine Measure.addHaar_submodule MeasureTheory.volume _ ?_
      intro htop
      have hmem : T.normal i ∈ LinearMap.ker (innerSL ℝ (T.normal i) : E4 →ₗ[ℝ] ℝ) :=
        htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hmem
      have h1 : ⟪T.normal i, T.normal i⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, T.unit i, one_pow]
      change ⟪T.normal i, T.normal i⟫_ℝ = 0 at hmem
      linarith
    filter_upwards [compl_mem_ae_iff.mpr hnull] with y hy
    simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, LinearMap.mem_ker,
      not_exists] at hy
    rw [hposCone_eq]
    simp only [coneT, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨fun hy0 => ?_, fun i => (h i).le⟩
      have := h 0
      simp [hy0] at this
    · rintro ⟨_, h⟩ i
      exact lt_of_le_of_ne (h i) (Ne.symm (hy i))
  have hset_congr :
      ∫ y in coneT, Real.exp (-‖y‖ ^ 2) = ∫ y in posCone, Real.exp (-‖y‖ ^ 2) :=
    setIntegral_congr_set hcone_ae
  rw [hset_congr]
  have hzero_ae : ({(0 : E4)}ᶜ : Set E4) =ᵐ[MeasureTheory.volume] Set.univ := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : E4))] with y hy
    simp [hy]
  have hcompl_meas : MeasurableSet ({(0 : E4)}ᶜ : Set E4) :=
    (measurableSet_singleton (0 : E4)).compl
  have hind :
      ∫ y in posCone, Real.exp (-‖y‖ ^ 2) =
        ∫ y : ↑({(0 : E4)}ᶜ : Set E4) in Subtype.val ⁻¹' posCone, Real.exp (-‖(y : E4)‖ ^ 2)
          ∂(Measure.comap Subtype.val MeasureTheory.volume) := by
    have h1 :
        ∫ y in posCone, Real.exp (-‖y‖ ^ 2) =
          ∫ y in ({(0 : E4)}ᶜ : Set E4), posCone.indicator (fun y => Real.exp (-‖y‖ ^ 2)) y := by
      rw [← integral_indicator hposCone_meas, ← setIntegral_univ, ← setIntegral_congr_set hzero_ae]
    rw [h1, ← integral_subtype_comap hcompl_meas
      (fun y : E4 => posCone.indicator (fun y => Real.exp (-‖y‖ ^ 2)) y)]
    have hpre_meas : MeasurableSet (Subtype.val ⁻¹' posCone : Set ↑({(0 : E4)}ᶜ : Set E4)) :=
      hposCone_meas.preimage measurable_subtype_coe
    rw [← integral_indicator hpre_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : (y : E4) ∈ posCone
    · simp [hy]
    · simp [hy]
  rw [hind]
  let e := homeomorphUnitSphereProd E4
  have hmp : MeasurePreserving e (Measure.comap Subtype.val MeasureTheory.volume)
      (MeasureTheory.volume.toSphere.prod (Measure.volumeIoiPow 3)) := by
    have hmp0 := Measure.measurePreserving_homeomorphUnitSphereProd (MeasureTheory.volume : Measure E4)
    have hdim : Module.finrank ℝ E4 - 1 = 3 := by simp [E4]
    rwa [hdim] at hmp0
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  let S : Set ↑(Metric.sphere (0 : E4) 1) := Subtype.val ⁻¹' T.body
  have hpre :
      (Subtype.val ⁻¹' posCone : Set ↑({(0 : E4)}ᶜ : Set E4)) =
        e ⁻¹' (S ×ˢ Set.univ) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, S, posCone,
      Set.mem_ofPred_eq]
    have hy0 : (y : E4) ≠ 0 := y.2
    have he1 : ((e y).1 : E4) = ‖(y : E4)‖⁻¹ • (y : E4) := by
      simp [e, homeomorphUnitSphereProd, homeomorphSphereProd]
    rw [he1]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy0, h⟩⟩
  have hfn :
      ∀ y : ↑({(0 : E4)}ᶜ : Set E4),
        Real.exp (-‖(y : E4)‖ ^ 2) = (fun p : ↑(Metric.sphere (0 : E4) 1) × ↑(Set.Ioi (0 : ℝ)) =>
          (1 : ℝ) * Real.exp (-((p.2 : ℝ) ^ 2))) (e y) := by
    intro y
    have he2 : ((e y).2 : ℝ) = ‖(y : E4)‖ := by
      simp [e, homeomorphUnitSphereProd, homeomorphSphereProd]
    dsimp only
    rw [he2, one_mul]
  rw [hpre]
  simp_rw [hfn]
  rw [hmp.setIntegral_preimage_emb hemb
    (fun p : ↑(Metric.sphere (0 : E4) 1) × ↑(Set.Ioi (0 : ℝ)) =>
      (1 : ℝ) * Real.exp (-((p.2 : ℝ) ^ 2))) (S ×ˢ Set.univ)]
  have hprod :
      ∫ p in S ×ˢ (Set.univ : Set ↑(Set.Ioi (0 : ℝ))),
          (1 : ℝ) * Real.exp (-((p.2 : ℝ) ^ 2))
            ∂(MeasureTheory.volume.toSphere.prod (Measure.volumeIoiPow 3)) =
        (∫ _ in S, (1 : ℝ) ∂MeasureTheory.volume.toSphere) *
          (∫ r : ↑(Set.Ioi (0 : ℝ)) in Set.univ, Real.exp (-((r : ℝ) ^ 2))
            ∂Measure.volumeIoiPow 3) :=
    setIntegral_prod_mul (fun _ : ↑(Metric.sphere (0 : E4) 1) => (1 : ℝ))
      (fun r : ↑(Set.Ioi (0 : ℝ)) => Real.exp (-((r : ℝ) ^ 2))) S Set.univ
  rw [hprod]
  have hsphere : ∫ _ in S, (1 : ℝ) ∂MeasureTheory.volume.toSphere = MeasureTheory.volume.toSphere.real S := by
    simp [smul_eq_mul, Measure.real]
  have hrad :
      (∫ r : ↑(Set.Ioi (0 : ℝ)) in Set.univ, Real.exp (-((r : ℝ) ^ 2)) ∂Measure.volumeIoiPow 3) =
        1 / 2 := by
    rw [Measure.restrict_univ, Measure.volumeIoiPow]
    have hm : Measurable (fun r : ↑(Set.Ioi (0 : ℝ)) => ENNReal.ofReal ((r : ℝ) ^ 3)) :=
      (measurable_subtype_coe.pow_const 3).ennreal_ofReal
    have hae : ∀ᵐ (r : ↑(Set.Ioi (0 : ℝ))) ∂(Measure.comap Subtype.val MeasureTheory.volume),
        ENNReal.ofReal ((r : ℝ) ^ 3) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integral_withDensity_eq_integral_toReal_smul hm hae]
    have hcongr :
        (fun r : ↑(Set.Ioi (0 : ℝ)) =>
            (ENNReal.ofReal ((r : ℝ) ^ 3)).toReal • Real.exp (-((r : ℝ) ^ 2))) =
          (fun r : ↑(Set.Ioi (0 : ℝ)) => (r : ℝ) ^ 3 * Real.exp (-((r : ℝ) ^ 2))) := by
      ext r
      rw [smul_eq_mul, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) 3)]
    rw [hcongr, integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ 3 * Real.exp (-r ^ 2))]
    exact radial_cube_exp_integral
  rw [hsphere, hrad, mul_comm]

theorem volume_eq_two_sphereScale_mul_gaussVolGram (T : SphericalTetrahedron) :
    T.volume = (2 * sphereScale 3) * gaussVolGram (gramPoint T) := by
  rw [T.volume_eq_sphereScale_mul_toSphere]
  have hsphere := volume_cone_gaussian_eq_sphere T
  have hsph_eq : MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' T.body) =
      2 * ∫ y in {y : E4 | ∀ i : Fin 4, 0 < ⟪T.normal i, y⟫_ℝ}, Real.exp (-‖y‖ ^ 2) := by
    linarith
  rw [hsph_eq]
  let coneU : Set (Fin 4 → ℝ) := {u : Fin 4 → ℝ | ∀ i : Fin 4, 0 < ∑ j : Fin 4, T.normal i j * u j}
  have hmp_toLp :
      MeasurePreserving (⇑(MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm)
        MeasureTheory.volume MeasureTheory.volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)
  have hemb_toLp : MeasurableEmbedding (⇑(MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm) :=
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.measurableEmbedding
  have hpre_toLp :
      ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm ⁻¹' coneU) =
        {y : E4 | ∀ i : Fin 4, 0 < ⟪T.normal i, y⟫_ℝ} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, coneU]
    refine forall_congr' fun i => ?_
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hfn_toLp :
      ∀ y : E4, Real.exp (-‖y‖ ^ 2) =
        (fun u : Fin 4 → ℝ => Real.exp (-(u ⬝ᵥ u)))
          ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm y) := by
    intro y
    congr 2
    rw [PiLp.norm_sq_eq_of_L2]
    simp [dotProduct, sq]
  have htoLp_int :
      ∫ y in {y : E4 | ∀ i : Fin 4, 0 < ⟪T.normal i, y⟫_ℝ}, Real.exp (-‖y‖ ^ 2) =
        ∫ u in coneU, Real.exp (-(u ⬝ᵥ u)) := by
    rw [← hpre_toLp]
    simp_rw [hfn_toLp]
    exact hmp_toLp.setIntegral_preimage_emb hemb_toLp (fun u : Fin 4 → ℝ => Real.exp (-(u ⬝ᵥ u))) coneU
  rw [htoLp_int]
  let L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := Matrix.toLin' (normalMat T)
  have hL_det : LinearMap.det L ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact normalMat_det_ne_zero T
  let eL : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) :=
    LinearEquiv.toContinuousLinearEquiv (L.equivOfDetNeZero hL_det)
  have heL_apply : ∀ u, eL u = normalMat T *ᵥ u := fun u => rfl
  have hpre_L : eL ⁻¹' orthant4 = coneU := by
    ext u
    simp only [Set.mem_preimage, orthant4, Set.mem_univ_pi, Set.mem_Ioi, coneU,
      Set.mem_ofPred_eq, heL_apply, normalMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hfn_L :
      ∀ u : Fin 4 → ℝ, Real.exp (-(u ⬝ᵥ u)) = gaussIntegrand (gramPoint T) (eL u) := by
    intro u
    simp only [gaussIntegrand]
    rw [gaussQuadForm_eq_norm_sq T u (eL u) (heL_apply u)]
  have hmap_L : Measure.map (⇑eL.toHomeomorph) MeasureTheory.volume =
      ENNReal.ofReal |(LinearMap.det (eL : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)))⁻¹| • MeasureTheory.volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar MeasureTheory.volume hL_det
  have hint_L :
      ∫ u in coneU, Real.exp (-(u ⬝ᵥ u)) =
        (Real.sqrt (symUnitMat (gramPoint T)).det)⁻¹ * gaussInt (gramPoint T) := by
    rw [← hpre_L]
    simp_rw [hfn_L]
    change ∫ u in (⇑eL.toHomeomorph) ⁻¹' orthant4,
        gaussIntegrand (gramPoint T) (eL.toHomeomorph u) = _
    rw [← eL.toHomeomorph.measurableEmbedding.setIntegral_map, hmap_L,
      Measure.restrict_smul, integral_smul_measure, smul_eq_mul]
    have hdet_abs : |(LinearMap.det (eL : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)))⁻¹| =
        (Real.sqrt (symUnitMat (gramPoint T)).det)⁻¹ := by
      have hdet_eq : LinearMap.det (eL : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) = (normalMat T).det := by
        change LinearMap.det L = (normalMat T).det
        exact LinearMap.det_toLin' (normalMat T)
      rw [abs_inv, hdet_eq, abs_normalMat_det T]
    rw [ENNReal.toReal_ofReal (abs_nonneg _), hdet_abs]
    rfl
  rw [hint_L]
  change sphereScale 3 * (2 * gaussVolGram (gramPoint T)) =
    2 * sphereScale 3 * gaussVolGram (gramPoint T)
  ring

/-! ### Smoothness and local coercivity on `gramOpen` -/

/-- Linear part of `symUnitMat` as a map into matrices. -/
def symUnitMatLin (v : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  symUnitMat v - 1

theorem symUnitMat_add_eq (x v : Fin 6 → ℝ) :
    symUnitMat (x + v) = symUnitMat x + symUnitMatLin v := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [symUnitMat, symUnitMatLin]

/-- Coordinate projection linear map for entry `(a, b)` of `symUnitMatLin`. -/
def symUnitEntryCLM (a b : Fin 4) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => symUnitMatLin v a b
      map_add' := fun u v => by
        fin_cases a <;> fin_cases b <;> simp [symUnitMatLin, symUnitMat]
      map_smul' := fun c v => by
        fin_cases a <;> fin_cases b <;> simp [symUnitMatLin, symUnitMat] }

theorem symUnitMat_entry_hasFDerivAt (a b : Fin 4) (x : Fin 6 → ℝ) :
    HasFDerivAt (fun y => symUnitMat y a b) (symUnitEntryCLM a b) x := by
  have heq : (fun y => symUnitMat y a b) =
      fun y => (symUnitMat 0 a b) + symUnitEntryCLM a b y := by
    ext y
    fin_cases a <;> fin_cases b <;>
      simp [symUnitEntryCLM, symUnitMatLin, symUnitMat]
  rw [heq]
  simpa using (symUnitEntryCLM a b).hasFDerivAt.const_add (symUnitMat 0 a b)

theorem symUnitMat_entry_contDiff (a b : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => symUnitMat y a b) := by
  have heq : (fun y => symUnitMat y a b) =
      fun y => (symUnitMat 0 a b) + symUnitEntryCLM a b y := by
    ext y
    fin_cases a <;> fin_cases b <;>
      simp [symUnitEntryCLM, symUnitMatLin, symUnitMat]
  rw [heq]
  exact contDiff_const.add (symUnitEntryCLM a b).contDiff

private theorem contDiff_finsetProd {ι : Type*} (s : Finset ι)
    {f : ι → (Fin 6 → ℝ) → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contDiff_const]
  | insert a s ha ih =>
    have hf_a : ContDiff ℝ (⊤ : ℕ∞) (f a) := hf a (Finset.mem_insert_self a s)
    have hf_s : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∏ i ∈ s, f i x) :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa [Finset.prod_insert ha] using hf_a.mul hf_s

theorem symUnitMat_det_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (symUnitMat x).det) := by
  have hdet : (fun x => (symUnitMat x).det) =
      fun x => ∑ σ : Equiv.Perm (Fin 4),
        ((Equiv.Perm.sign σ : ℝ) * ∏ i : Fin 4, symUnitMat x (σ i) i) := by
    ext x
    exact Matrix.det_apply' (symUnitMat x)
  rw [hdet]
  refine ContDiff.sum fun σ _ => ?_
  exact contDiff_const.mul (contDiff_finsetProd Finset.univ fun i _ => symUnitMat_entry_contDiff (σ i) i)

theorem symUnitAdj_eq_matrixAdjugate {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    symUnitAdj x = (symUnitMat x).adjugate := by
  have hdet : IsUnit (symUnitMat x).det := isUnit_iff_ne_zero.mpr (gramOpen_det_ne_zero hx)
  have h1 : symUnitMat x * symUnitAdj x = symUnitMat x * (symUnitMat x).adjugate := by
    rw [symUnitMat_mul_adj, Matrix.mul_adjugate]
  have hinv := congrArg (symUnitInv x * ·) h1
  simpa [← Matrix.mul_assoc, symUnitInv_mul_mat x (gramOpen_det_ne_zero hx)] using hinv

theorem symUnitMat_adjugate_entry_contDiff (a b : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (symUnitMat x).adjugate a b) := by
  have heq : (fun x => (symUnitMat x).adjugate a b) =
      fun x => ∑ σ : Equiv.Perm (Fin 4),
        ((Equiv.Perm.sign σ : ℝ) *
          ∏ i : Fin 4, ((symUnitMat x).updateRow b (Pi.single a 1)) (σ i) i) := by
    ext x
    rw [Matrix.adjugate_apply, Matrix.det_apply']
  rw [heq]
  refine ContDiff.sum fun σ _ => ?_
  refine contDiff_const.mul (contDiff_finsetProd Finset.univ fun i _ => ?_)
  by_cases hσ : σ i = b
  · simp [Matrix.updateRow_apply, hσ, contDiff_const]
  · simp only [Matrix.updateRow_apply, hσ, ↓reduceIte]
    exact symUnitMat_entry_contDiff (σ i) i

theorem symUnitAdj_entry_contDiffOn (a b : Fin 4) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => symUnitAdj x a b) gramOpen := by
  refine (symUnitMat_adjugate_entry_contDiff a b).contDiffOn.congr fun x hx => ?_
  rw [symUnitAdj_eq_matrixAdjugate hx]

theorem symUnitInv_entry_contDiffOn (a b : Fin 4) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => symUnitInv x a b) gramOpen := by
  have heq : (fun x => symUnitInv x a b) =
      fun x => (symUnitMat x).det⁻¹ * symUnitAdj x a b := by
    ext x
    simp [symUnitInv]
  rw [heq]
  have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (symUnitMat x).det⁻¹) gramOpen := by
    intro x hx
    exact (symUnitMat_det_contDiff.contDiffAt.inv (gramOpen_det_ne_zero hx)).contDiffWithinAt
  exact hinv.mul (symUnitAdj_entry_contDiffOn a b)

theorem symUnitSqrtDet_inv_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (Real.sqrt (symUnitMat x).det)⁻¹) gramOpen := by
  intro x hx
  have hdet_pos : 0 < (symUnitMat x).det := gramOpen_det_pos hx
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Real.sqrt (symUnitMat y).det) x :=
    symUnitMat_det_contDiff.contDiffAt.sqrt hdet_pos.ne'
  exact (hsqrt.inv (Real.sqrt_ne_zero'.mpr hdet_pos)).contDiffWithinAt

/-- Derivative of `symUnitInv · a b` at `x ∈ gramOpen`:
`v ↦ (- (symUnitInv x * symUnitMatLin v * symUnitInv x)) a b`. -/
def symUnitInvDeriv (x : Fin 6 → ℝ) (a b : Fin 4) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  ∑ p : Fin 4, ∑ q : Fin 4,
    (-(symUnitInv x a p * symUnitInv x q b)) • symUnitEntryCLM p q

theorem symUnitInvDeriv_apply (x : Fin 6 → ℝ) (a b : Fin 4) (v : Fin 6 → ℝ) :
    symUnitInvDeriv x a b v = (-(symUnitInv x * symUnitMatLin v * symUnitInv x)) a b := by
  simp only [symUnitInvDeriv, sum_apply, smul_apply,
    smul_eq_mul, symUnitEntryCLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, neg_mul]
  rw [← Finset.sum_neg_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => by ring

theorem continuousOn_symUnitInvDeriv (a b : Fin 4) :
    ContinuousOn (fun x => symUnitInvDeriv x a b) gramOpen := by
  refine continuousOn_finsetSum Finset.univ fun p _ =>
    continuousOn_finsetSum Finset.univ fun q _ => ?_
  exact (((symUnitInv_entry_contDiffOn a p).continuousOn.mul
    (symUnitInv_entry_contDiffOn q b).continuousOn).neg).smul continuousOn_const

theorem hasFDerivAt_symUnitInv {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (a b : Fin 4) :
    HasFDerivAt (fun y => symUnitInv y a b) (symUnitInvDeriv x a b) x := by
  have hnhds : gramOpen ∈ 𝓝 x := isOpen_gramOpen.mem_nhds hx
  have hdiff : ∀ c d : Fin 4, DifferentiableAt ℝ (fun y => symUnitInv y c d) x := by
    intro c d
    have hc := (symUnitInv_entry_contDiffOn c d x hx).contDiffAt hnhds
    exact hc.differentiableAt (by simp)
  have hfderiv : ∀ c d : Fin 4,
      HasFDerivAt (fun y => symUnitInv y c d) (fderiv ℝ (fun y => symUnitInv y c d) x) x :=
    fun c d => (hdiff c d).hasFDerivAt
  have hderiv_zero : ∀ p d : Fin 4,
      (∑ c : Fin 4, (symUnitInv x c d • symUnitEntryCLM p c +
        symUnitMat x p c • fderiv ℝ (fun y => symUnitInv y c d) x)) = 0 := by
    intro p d
    have hsum :
        HasFDerivAt (fun y => ∑ c : Fin 4, symUnitMat y p c * symUnitInv y c d)
          (∑ c : Fin 4, (symUnitMat x p c • fderiv ℝ (fun y => symUnitInv y c d) x +
            symUnitInv x c d • symUnitEntryCLM p c)) x := by
      refine HasFDerivAt.fun_sum fun c _ => ?_
      exact (symUnitMat_entry_hasFDerivAt p c x).fun_mul (hfderiv c d)
    have hconst : HasFDerivAt (fun _ : Fin 6 → ℝ => (1 : Matrix (Fin 4) (Fin 4) ℝ) p d)
        (0 : (Fin 6 → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_const ((1 : Matrix (Fin 4) (Fin 4) ℝ) p d) x
    have heq' : (fun y => ∑ c : Fin 4, symUnitMat y p c * symUnitInv y c d) =ᶠ[𝓝 x]
        fun _ => (1 : Matrix (Fin 4) (Fin 4) ℝ) p d := by
      filter_upwards [hnhds] with y hy
      have hmul := symUnitMat_mul_inv y (gramOpen_det_ne_zero hy)
      have hent := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M p d) hmul
      simpa [Matrix.mul_apply] using hent
    have huniq := (hsum.congr_of_eventuallyEq heq'.symm).unique hconst
    rw [← huniq]
    refine Finset.sum_congr rfl fun c _ => add_comm _ _
  have hclm : fderiv ℝ (fun y => symUnitInv y a b) x = symUnitInvDeriv x a b := by
    ext v
    rw [symUnitInvDeriv_apply]
    let M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun c d => fderiv ℝ (fun y => symUnitInv y c d) x v
    have hM : symUnitMatLin v * symUnitInv x + symUnitMat x * M = 0 := by
      ext p d
      have hp := congrArg (fun L : (Fin 6 → ℝ) →L[ℝ] ℝ => L v) (hderiv_zero p d)
      simp only [FunLike.coe_sum, FunLike.coe_add,
        FunLike.coe_smul, zero_apply, Finset.sum_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib] at hp
      have hlin : ∀ c, symUnitEntryCLM p c v = symUnitMatLin v p c := fun c => rfl
      simpa [M, Matrix.add_apply, Matrix.mul_apply, hlin, Matrix.zero_apply, mul_comm] using hp
    have hM2 : M = -(symUnitInv x * symUnitMatLin v * symUnitInv x) := by
      have h1 := congrArg (symUnitInv x * ·) hM
      rw [Matrix.mul_zero, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        symUnitInv_mul_mat x (gramOpen_det_ne_zero hx), Matrix.one_mul] at h1
      have h2 := eq_neg_of_add_eq_zero_right h1
      simpa [Matrix.mul_assoc] using h2
    have hent := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A a b) hM2
    simpa [M] using hent
  rw [← hclm]
  exact hfderiv a b

theorem symUnitMat_det_deriv_zero_apply {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (k : Fin 6) :
    HasDerivAt (fun (y : ℝ) => (Real.sqrt (symUnitMat (x + y • Pi.single k 1)).det)⁻¹)
      (-(Real.sqrt (symUnitMat x).det)⁻¹ * symUnitInv x (pairIdx k).1 (pairIdx k).2) 0 := by
  have hdet_deriv := symUnitMat_det_deriv_coord x k
  have hdet_pos : 0 < (symUnitMat x).det := gramOpen_det_pos hx
  have hdet_pos0 : (symUnitMat (x + (0 : ℝ) • Pi.single k 1)).det ≠ 0 := by
    rw [zero_smul, add_zero]
    exact hdet_pos.ne'
  have hsqrt : HasDerivAt (fun (y : ℝ) => Real.sqrt (symUnitMat (x + y • Pi.single k 1)).det)
      ((2 * symUnitAdj x (pairIdx k).1 (pairIdx k).2) / (2 * Real.sqrt (symUnitMat x).det)) 0 := by
    have h0 := hdet_deriv.sqrt hdet_pos0
    rwa [zero_smul, add_zero] at h0
  have hsqrt_ne : Real.sqrt (symUnitMat (x + (0 : ℝ) • Pi.single k 1)).det ≠ 0 := by
    rw [zero_smul, add_zero]
    exact Real.sqrt_ne_zero'.mpr hdet_pos
  have hinv := hsqrt.fun_inv hsqrt_ne
  refine hinv.congr_deriv ?_
  simp only [zero_smul, add_zero]
  have hdet_ne : (symUnitMat x).det ≠ 0 := hdet_pos.ne'
  have hsq : Real.sqrt (symUnitMat x).det ^ 2 = (symUnitMat x).det := Real.sq_sqrt hdet_pos.le
  simp only [symUnitInv, Matrix.smul_apply, smul_eq_mul]
  field_simp [hsqrt_ne, hdet_ne]
  rw [hsq]

theorem gaussQuadForm_pos {x : Fin 6 → ℝ} (hx : x ∈ gramOpen)
    {u : Fin 4 → ℝ} (hu : u ≠ 0) :
    0 < gaussQuadForm x u := by
  let T := tetOf x hx
  have hxT : gramPoint T = x := gramPoint_tetOf hx
  have hinv : ∀ i j : Fin 4, symUnitInv x i j = ⟪T.normalDualRay i, T.normalDualRay j⟫_ℝ := by
    intro i j
    rw [← hxT, ← normalDualRay_inner_eq_inv T i j]
  let w : E4 := ∑ i : Fin 4, u i • T.normalDualRay i
  have hquad : gaussQuadForm x u = ‖w‖ ^ 2 := by
    simp only [gaussQuadForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
    have hw : ‖w‖ ^ 2 = ⟪w, w⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
    rw [hw]
    simp only [w, sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hinv i j, real_inner_comm]
    ring
  rw [hquad]
  have hw_ne : w ≠ 0 := by
    intro hw0
    apply hu
    ext i
    have hi := congrArg (fun v : E4 => ⟪T.normal i, v⟫_ℝ) hw0
    simp only [w, inner_sum, inner_smul_right, T.normalDualRay_inner, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, inner_zero_right] at hi
    exact hi
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw_ne)

theorem gaussQuadForm_local_coercive {x₀ : Fin 6 → ℝ} (hx₀ : x₀ ∈ gramOpen) :
    ∃ r > 0, Metric.closedBall x₀ r ⊆ gramOpen ∧
      ∃ c > 0, ∀ x ∈ Metric.closedBall x₀ r, ∀ z : Fin 4 → ℝ,
        c * (∑ i : Fin 4, z i ^ 2) ≤ gaussQuadForm x z := by
  let S : Set (Fin 4 → ℝ) := {u : Fin 4 → ℝ | ∑ i : Fin 4, u i ^ 2 = 1}
  have hS_closed : IsClosed S := by
    refine isClosed_eq ?_ continuous_const
    exact continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).pow 2
  have hS_bdd : S ⊆ Metric.closedBall (0 : Fin 4 → ℝ) 1 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hsq : u i ^ 2 ≤ 1 ^ 2 := by
      have hi : u i ^ 2 ≤ ∑ j : Fin 4, u j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      linarith [show ∑ j : Fin 4, u j ^ 2 = 1 from hu]
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq zero_le_one)
  have hS_compact : IsCompact S := (isCompact_closedBall (0 : Fin 4 → ℝ) 1).of_isClosed_subset hS_closed hS_bdd
  have hS_ne : S.Nonempty := by
    refine ⟨Pi.single 0 1, ?_⟩
    simp [S, Fin.sum_univ_four]
  have hquad_cont : ContinuousOn (fun p : (Fin 6 → ℝ) × (Fin 4 → ℝ) => gaussQuadForm p.1 p.2)
      (gramOpen ×ˢ Set.univ) := by
    change ContinuousOn (fun p : (Fin 6 → ℝ) × (Fin 4 → ℝ) =>
      ∑ a : Fin 4, p.2 a * ∑ b : Fin 4, symUnitInv p.1 a b * p.2 b) (gramOpen ×ˢ Set.univ)
    refine continuousOn_finsetSum Finset.univ fun i _ => ?_
    refine (continuous_apply i).comp continuous_snd |>.continuousOn.mul ?_
    refine continuousOn_finsetSum Finset.univ fun j _ => ?_
    exact ((symUnitInv_entry_contDiffOn i j).continuousOn.comp continuousOn_fst
      (fun _ hp => hp.1)).mul ((continuous_apply j).comp continuous_snd |>.continuousOn)
  have hn_open : IsOpen {p : (Fin 6 → ℝ) × (Fin 4 → ℝ) | p.1 ∈ gramOpen ∧ 0 < gaussQuadForm p.1 p.2} := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, u⟩ ⟨hx, hpos⟩
    have hmem : (gramOpen ×ˢ (Set.univ : Set (Fin 4 → ℝ))) ∈ 𝓝 (x, u) :=
      (isOpen_gramOpen.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ u⟩
    have hcont_at : ContinuousAt (fun p : (Fin 6 → ℝ) × (Fin 4 → ℝ) => gaussQuadForm p.1 p.2) (x, u) :=
      (hquad_cont (x, u) ⟨hx, Set.mem_univ u⟩).continuousAt hmem
    have hlt := hcont_at.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    exact Filter.mem_of_superset (Filter.inter_mem hmem hlt) fun p ⟨⟨hp1, _⟩, hp2⟩ => ⟨hp1, hp2⟩
  have hsub : ({x₀} ×ˢ S) ⊆ {p : (Fin 6 → ℝ) × (Fin 4 → ℝ) | p.1 ∈ gramOpen ∧ 0 < gaussQuadForm p.1 p.2} := by
    rintro ⟨x, u⟩ ⟨hx, hu⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hu_ne : u ≠ 0 := by
      intro h0
      simp [S, h0] at hu
    exact ⟨hx₀, gaussQuadForm_pos hx₀ hu_ne⟩
  obtain ⟨U, V, hU_open, _, hxU, hSV, hUV_sub⟩ :=
    generalized_tube_lemma isCompact_singleton hS_compact hn_open hsub
  have hU_mem : x₀ ∈ gramOpen ∩ U := ⟨hx₀, hxU (Set.mem_singleton x₀)⟩
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp (isOpen_gramOpen.inter hU_open) x₀ hU_mem
  have hr2_pos : 0 < r / 2 := half_pos hr_pos
  have hball_sub : Metric.closedBall x₀ (r / 2) ⊆ gramOpen ∩ U := by
    intro x hx
    exact hr_sub (lt_of_le_of_lt hx (half_lt_self hr_pos))
  have hball_gram : Metric.closedBall x₀ (r / 2) ⊆ gramOpen := fun x hx => (hball_sub hx).1
  have hcompact : IsCompact (Metric.closedBall x₀ (r / 2) ×ˢ S) :=
    (isCompact_closedBall x₀ (r / 2)).prod hS_compact
  have hne : (Metric.closedBall x₀ (r / 2) ×ˢ S).Nonempty := by
    refine ⟨(x₀, hS_ne.some), ?_⟩
    exact ⟨Metric.mem_closedBall_self hr2_pos.le, hS_ne.some_mem⟩
  have hcont_on : ContinuousOn (fun p : (Fin 6 → ℝ) × (Fin 4 → ℝ) => gaussQuadForm p.1 p.2)
      (Metric.closedBall x₀ (r / 2) ×ˢ S) :=
    hquad_cont.mono fun p hp => ⟨hball_gram hp.1, Set.mem_univ _⟩
  obtain ⟨⟨x_min, u_min⟩, hmin_mem, hmin⟩ := hcompact.exists_isMinOn hne hcont_on
  have hc_pos : 0 < gaussQuadForm x_min u_min :=
    (hUV_sub ⟨(hball_sub hmin_mem.1).2, hSV hmin_mem.2⟩).2
  refine ⟨r / 2, hr2_pos, hball_gram, gaussQuadForm x_min u_min, hc_pos, fun x hx z => ?_⟩
  by_cases hz : ∑ i : Fin 4, z i ^ 2 = 0
  · have hz0 : ∀ i, z i = 0 := fun i => by
      have hi : z i ^ 2 ≤ 0 := by
        calc
          z i ^ 2 ≤ ∑ j : Fin 4, z j ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
          _ = 0 := hz
      exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
    have hzeq : z = 0 := funext hz0
    simp [hzeq, gaussQuadForm]
  · have hsum_pos : 0 < ∑ i : Fin 4, z i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (z i)) (Ne.symm hz)
    let t : ℝ := Real.sqrt (∑ i : Fin 4, z i ^ 2)
    have ht_pos : 0 < t := Real.sqrt_pos.mpr hsum_pos
    let u : Fin 4 → ℝ := t⁻¹ • z
    have hu_mem : u ∈ S := by
      simp only [S, Set.mem_ofPred_eq, u, Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt hsum_pos.le, inv_mul_cancel₀ hsum_pos.ne']
    have hcu := hmin (show (x, u) ∈ Metric.closedBall x₀ (r / 2) ×ˢ S from ⟨hx, hu_mem⟩)
    have hscale : gaussQuadForm x z = t ^ 2 * gaussQuadForm x u := by
      simp only [gaussQuadForm, u, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      field_simp [ht_pos.ne']
    rw [hscale, show t ^ 2 = ∑ i : Fin 4, z i ^ 2 from Real.sq_sqrt hsum_pos.le,
      mul_comm (∑ i : Fin 4, z i ^ 2)]
    exact mul_le_mul_of_nonneg_right hcu hsum_pos.le

private theorem integrable_fin2_exp_prod {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Fin 2 → ℝ => ∏ i : Fin 2, Real.exp (-a * z i ^ 2)) MeasureTheory.volume := by
  have h3 := (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  have h1d : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2)) MeasureTheory.volume :=
    integrable_exp_neg_mul_sq ha
  have h2d : Integrable (fun p : ℝ × ℝ => Real.exp (-a * p.1 ^ 2) * Real.exp (-a * p.2 ^ 2))
      MeasureTheory.volume :=
    h1d.mul_prod h1d
  rw [← h3.integrable_comp_emb (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.measurableEmbedding]
  refine h2d.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [Fin.prod_univ_two]

private theorem integrable_fin3_exp_prod {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Fin 3 → ℝ => ∏ i : Fin 3, Real.exp (-a * z i ^ 2)) MeasureTheory.volume := by
  have h2 := (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin 3 => ℝ) 0).symm
  have h1d : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2)) MeasureTheory.volume :=
    integrable_exp_neg_mul_sq ha
  rw [← h2.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.measurableEmbedding]
  have hprod := h1d.mul_prod (integrable_fin2_exp_prod ha)
  refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
  dsimp only [Function.comp_apply]
  rw [Fin.prod_univ_succ (n := 2)]
  simp

private theorem integrable_fin4_exp_prod {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Fin 4 → ℝ => ∏ i : Fin 4, Real.exp (-a * z i ^ 2)) MeasureTheory.volume := by
  have h1 := (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin 4 => ℝ) 0).symm
  have h1d : Integrable (fun t : ℝ => Real.exp (-a * t ^ 2)) MeasureTheory.volume :=
    integrable_exp_neg_mul_sq ha
  rw [← h1.integrable_comp_emb
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm.measurableEmbedding]
  have hprod := h1d.mul_prod (integrable_fin3_exp_prod ha)
  refine hprod.congr (Filter.Eventually.of_forall fun p => ?_)
  dsimp only [Function.comp_apply]
  rw [Fin.prod_univ_succ (n := 3)]
  simp

theorem integrableOn_gaussIntegrand {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    IntegrableOn (gaussIntegrand x) orthant4 MeasureTheory.volume := by
  obtain ⟨r, hr, _, c, hc, hcoerc⟩ := gaussQuadForm_local_coercive hx
  have hmem : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hdom : Integrable (fun z : Fin 4 → ℝ => ∏ i : Fin 4, Real.exp (-c * z i ^ 2))
      MeasureTheory.volume :=
    integrable_fin4_exp_prod hc
  refine hdom.integrableOn.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine Real.continuous_exp.comp (Continuous.neg ?_)
    change Continuous (fun z : Fin 4 → ℝ => ∑ i : Fin 4, z i * ∑ j : Fin 4, symUnitInv x i j * z j)
    exact continuous_finsetSum Finset.univ fun i _ =>
      (continuous_apply i).mul (continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul (continuous_apply j))
  · refine Filter.Eventually.of_forall fun z => ?_
    have hnonneg : 0 ≤ gaussIntegrand x z := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hnonneg, gaussIntegrand]
    calc
      Real.exp (-gaussQuadForm x z) ≤ Real.exp (-(c * ∑ i : Fin 4, z i ^ 2)) :=
        Real.exp_le_exp.mpr (neg_le_neg (hcoerc x hmem z))
      _ = Real.exp (∑ i : Fin 4, -c * z i ^ 2) := by
        congr 1
        simp [Finset.mul_sum, neg_mul]
      _ = ∏ i : Fin 4, Real.exp (-c * z i ^ 2) := Real.exp_sum _ _

/-- Derivative of `x ↦ gaussQuadForm x z` at `x ∈ gramOpen`. -/
def gaussQuadFormFDeriv (x : Fin 6 → ℝ) (z : Fin 4 → ℝ) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, (z a * z b) • symUnitInvDeriv x a b

/-- Derivative of `x ↦ gaussIntegrand x z` at `x ∈ gramOpen`. -/
def gaussIntegrandFDeriv (x : Fin 6 → ℝ) (z : Fin 4 → ℝ) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  (-gaussIntegrand x z) • gaussQuadFormFDeriv x z

theorem hasFDerivAt_gaussQuadForm {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (z : Fin 4 → ℝ) :
    HasFDerivAt (fun y => gaussQuadForm y z) (gaussQuadFormFDeriv x z) x := by
  have heq : (fun y => gaussQuadForm y z) =
      fun y => ∑ a : Fin 4, ∑ b : Fin 4, (z a * z b) * symUnitInv y a b := by
    ext y
    simp only [gaussQuadForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [heq]
  refine HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
  exact (hasFDerivAt_symUnitInv hx a b).const_mul (z a * z b)

theorem hasFDerivAt_gaussIntegrand {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (z : Fin 4 → ℝ) :
    HasFDerivAt (fun y => gaussIntegrand y z) (gaussIntegrandFDeriv x z) x := by
  have h := ((hasFDerivAt_gaussQuadForm hx z).fun_neg).exp
  dsimp only [gaussIntegrand, gaussIntegrandFDeriv] at h ⊢
  rwa [smul_neg, ← neg_smul] at h

theorem hasFDerivAt_gaussInt {x₀ : Fin 6 → ℝ} (hx₀ : x₀ ∈ gramOpen) :
    HasFDerivAt gaussInt (∫ z in orthant4, gaussIntegrandFDeriv x₀ z) x₀ := by
  obtain ⟨r, hr, hball_gram, c, hc, hcoerc⟩ := gaussQuadForm_local_coercive hx₀
  let s := Metric.closedBall x₀ r
  have hs_nhds : s ∈ 𝓝 x₀ := Metric.closedBall_mem_nhds x₀ hr
  have hs_compact : IsCompact s := isCompact_closedBall x₀ r
  have hs_ne : s.Nonempty := ⟨x₀, Metric.mem_closedBall_self hr.le⟩
  have hcont_deriv : ∀ a b : Fin 4, ContinuousOn (fun y => ‖symUnitInvDeriv y a b‖) s :=
    fun a b => continuous_norm.comp_continuousOn ((continuousOn_symUnitInvDeriv a b).mono hball_gram)
  have hbound_ab : ∀ a b : Fin 4, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ s, ‖symUnitInvDeriv y a b‖ ≤ M := by
    intro a b
    obtain ⟨y₀, _, hy₀⟩ := hs_compact.exists_isMaxOn hs_ne (hcont_deriv a b)
    exact ⟨‖symUnitInvDeriv y₀ a b‖, norm_nonneg _, fun y hy => hy₀ hy⟩
  choose Mab hMab_nonneg hMab using hbound_ab
  let C0 : ℝ := ∑ a : Fin 4, ∑ b : Fin 4, Mab a b
  let bound : (Fin 4 → ℝ) → ℝ :=
    fun z => (C0 * (2 / c)) * ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2)
  have hint_bound : Integrable bound (MeasureTheory.volume.restrict orthant4) :=
    ((integrable_fin4_exp_prod (half_pos hc)).const_mul (C0 * (2 / c))).integrableOn
  have hcont_gauss : ∀ y : Fin 6 → ℝ, Continuous (gaussIntegrand y) := by
    intro y
    refine Real.continuous_exp.comp (Continuous.neg ?_)
    change Continuous (fun z : Fin 4 → ℝ => ∑ i : Fin 4, z i * ∑ j : Fin 4, symUnitInv y i j * z j)
    exact continuous_finsetSum Finset.univ fun i _ =>
      (continuous_apply i).mul (continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul (continuous_apply j))
  have hmeas_F : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun z => gaussIntegrand x z) (MeasureTheory.volume.restrict orthant4) := by
    filter_upwards [isOpen_gramOpen.mem_nhds hx₀] with x _
    exact (hcont_gauss x).aestronglyMeasurable
  have hmeas_F' : AEStronglyMeasurable (fun z => gaussIntegrandFDeriv x₀ z)
      (MeasureTheory.volume.restrict orthant4) := by
    refine Continuous.aestronglyMeasurable ?_
    refine (Continuous.neg (hcont_gauss x₀)).smul ?_
    refine continuous_finsetSum Finset.univ fun a _ =>
      continuous_finsetSum Finset.univ fun b _ => ?_
    exact ((continuous_apply a).mul (continuous_apply b)).smul continuous_const
  have hbound_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict orthant4), ∀ x ∈ s,
      ‖gaussIntegrandFDeriv x z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall fun z x hx => ?_
    have hnorm_smul : ‖gaussIntegrandFDeriv x z‖ = gaussIntegrand x z * ‖gaussQuadFormFDeriv x z‖ := by
      simp only [gaussIntegrandFDeriv, norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_pos (Real.exp_pos _), gaussIntegrand]
    have hnorm_q : ‖gaussQuadFormFDeriv x z‖ ≤ C0 * (∑ i : Fin 4, z i ^ 2) := by
      calc
        ‖gaussQuadFormFDeriv x z‖
            ≤ ∑ a : Fin 4, ∑ b : Fin 4, ‖(z a * z b) • symUnitInvDeriv x a b‖ := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
        _ = ∑ a : Fin 4, ∑ b : Fin 4, |z a * z b| * ‖symUnitInvDeriv x a b‖ := by
              simp [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ a : Fin 4, ∑ b : Fin 4, (∑ i : Fin 4, z i ^ 2) * Mab a b := by
              refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
              refine mul_le_mul ?_ (hMab a b x hx) (norm_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
              have hab : |z a * z b| ≤ (z a ^ 2 + z b ^ 2) / 2 := by
                rw [abs_mul]
                nlinarith [abs_nonneg (z a), abs_nonneg (z b), sq_abs (z a), sq_abs (z b),
                  sq_nonneg (|z a| - |z b|)]
              have ha_le : z a ^ 2 ≤ ∑ i : Fin 4, z i ^ 2 :=
                Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ a)
              have hb_le : z b ^ 2 ≤ ∑ i : Fin 4, z i ^ 2 :=
                Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ b)
              linarith
        _ = C0 * (∑ i : Fin 4, z i ^ 2) := by
              dsimp [C0]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have hexp_le : gaussIntegrand x z * (∑ i : Fin 4, z i ^ 2) ≤
        (2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2) := by
      let u : ℝ := (c / 2) * ∑ i : Fin 4, z i ^ 2
      have hu_nonneg : 0 ≤ u := mul_nonneg (half_pos hc).le (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have hu_exp : u ≤ Real.exp u := le_trans (by linarith) (Real.add_one_le_exp u)
      have hgauss_le : gaussIntegrand x z ≤ Real.exp (-2 * u) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 := hcoerc x hx z
        linarith [show 2 * u = c * ∑ i : Fin 4, z i ^ 2 by dsimp [u]; ring]
      have hmul_le : Real.exp (-2 * u) * u ≤ Real.exp (-u) := by
        have h := mul_le_mul_of_nonneg_left hu_exp (Real.exp_pos (-2 * u)).le
        rwa [← Real.exp_add, show -2 * u + u = -u by ring] at h
      have hsum_eq : ∑ i : Fin 4, z i ^ 2 = (2 / c) * u := by
        dsimp [u]
        field_simp [hc.ne']
      have hprod_eq : Real.exp (-u) = ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        dsimp [u]
        simp [Finset.mul_sum, neg_mul]
      calc
        gaussIntegrand x z * (∑ i : Fin 4, z i ^ 2)
            ≤ Real.exp (-2 * u) * ((2 / c) * u) := by
              rw [hsum_eq]
              exact mul_le_mul_of_nonneg_right hgauss_le (mul_nonneg (by positivity) hu_nonneg)
        _ = (2 / c) * (Real.exp (-2 * u) * u) := by ring
        _ ≤ (2 / c) * Real.exp (-u) := mul_le_mul_of_nonneg_left hmul_le (by positivity)
        _ = (2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2) := by rw [hprod_eq]
    have hC0_nonneg : 0 ≤ C0 := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hMab_nonneg a b
    rw [hnorm_smul]
    calc
      gaussIntegrand x z * ‖gaussQuadFormFDeriv x z‖
          ≤ gaussIntegrand x z * (C0 * ∑ i : Fin 4, z i ^ 2) :=
            mul_le_mul_of_nonneg_left hnorm_q (Real.exp_pos _).le
      _ = C0 * (gaussIntegrand x z * ∑ i : Fin 4, z i ^ 2) := by ring
      _ ≤ C0 * ((2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp_le hC0_nonneg
      _ = bound z := by dsimp [bound]; ring
  have hfderiv_all : ∀ᵐ z ∂(MeasureTheory.volume.restrict orthant4), ∀ x ∈ s,
      HasFDerivAt (fun y => gaussIntegrand y z) (gaussIntegrandFDeriv x z) x :=
    Filter.Eventually.of_forall fun z x hx => hasFDerivAt_gaussIntegrand (hball_gram hx) z
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs_nhds hmeas_F
    (integrableOn_gaussIntegrand hx₀) hmeas_F' hbound_le hint_bound hfderiv_all

/-! ### Schläfli partial derivatives via coordinatewise IBP and `manuscriptPsi` -/

theorem symUnitMat_transpose (x : Fin 6 → ℝ) : (symUnitMat x)ᵀ = symUnitMat x := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem symUnitAdj_transpose {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    (symUnitAdj x)ᵀ = symUnitAdj x := by
  rw [symUnitAdj_eq_matrixAdjugate hx, Matrix.adjugate_transpose, symUnitMat_transpose]

theorem symUnitInv_transpose {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    (symUnitInv x)ᵀ = symUnitInv x := by
  simp only [symUnitInv, Matrix.transpose_smul, symUnitAdj_transpose hx]

/-- Permutation of `Fin 4` sending `(0, 1, 2, 3)` to `((oppIdx k).1, (oppIdx k).2, (pairIdx k).1, (pairIdx k).2)`. -/
private def pairOppEquiv (k : Fin 6) : Equiv.Perm (Fin 4) :=
  match k with
  | 0 => ⟨![2, 3, 0, 1], ![2, 3, 0, 1], fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
  | 1 => ⟨![1, 3, 0, 2], ![2, 0, 3, 1], fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
  | 2 => ⟨![1, 2, 0, 3], ![2, 0, 1, 3], fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
  | 3 => ⟨![0, 3, 1, 2], ![0, 2, 3, 1], fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
  | 4 => ⟨![0, 2, 1, 3], ![0, 2, 1, 3], fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩
  | 5 => Equiv.refl (Fin 4)

private theorem pairOppEquiv_zero (k : Fin 6) : pairOppEquiv k 0 = (oppIdx k).1 := by
  fin_cases k <;> rfl

private theorem pairOppEquiv_one (k : Fin 6) : pairOppEquiv k 1 = (oppIdx k).2 := by
  fin_cases k <;> rfl

private theorem pairOppEquiv_two (k : Fin 6) : pairOppEquiv k 2 = (pairIdx k).1 := by
  fin_cases k <;> rfl

private theorem pairOppEquiv_three (k : Fin 6) : pairOppEquiv k 3 = (pairIdx k).2 := by
  fin_cases k <;> rfl

private theorem symUnitMatLin_single_mulVec (k : Fin 6) (w : Fin 4 → ℝ) :
    w ⬝ᵥ (symUnitMatLin (Pi.single k 1) *ᵥ w) = 2 * w (pairIdx k).1 * w (pairIdx k).2 := by
  fin_cases k <;>
    simp [symUnitMatLin, symUnitMat, pairIdx, dotProduct, Matrix.mulVec, Fin.sum_univ_four] <;>
    ring

theorem gaussQuadFormFDeriv_single {x : Fin 6 → ℝ} (hx : x ∈ gramOpen)
    (z : Fin 4 → ℝ) (k : Fin 6) :
    gaussQuadFormFDeriv x z (Pi.single k 1) =
      -(2 * (symUnitInv x *ᵥ z) (pairIdx k).1 * (symUnitInv x *ᵥ z) (pairIdx k).2) := by
  have hsum : gaussQuadFormFDeriv x z (Pi.single k 1) =
      -(z ⬝ᵥ ((symUnitInv x * symUnitMatLin (Pi.single k 1) * symUnitInv x) *ᵥ z)) := by
    simp only [gaussQuadFormFDeriv, sum_apply, smul_apply, smul_eq_mul,
      symUnitInvDeriv_apply, Matrix.neg_apply]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hsum, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  nth_rw 1 [← symUnitInv_transpose hx]
  rw [Matrix.vecMul_transpose, symUnitMatLin_single_mulVec]

theorem gaussIntegrandFDeriv_single {x : Fin 6 → ℝ} (hx : x ∈ gramOpen)
    (z : Fin 4 → ℝ) (k : Fin 6) :
    gaussIntegrandFDeriv x z (Pi.single k 1) =
      (2 * (symUnitInv x *ᵥ z) (pairIdx k).1 * (symUnitInv x *ᵥ z) (pairIdx k).2) *
        gaussIntegrand x z := by
  simp only [gaussIntegrandFDeriv, smul_apply, smul_eq_mul, gaussQuadFormFDeriv_single hx z k]
  ring

theorem integrableOn_gaussIntegrandFDeriv {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    IntegrableOn (gaussIntegrandFDeriv x) orthant4 MeasureTheory.volume := by
  obtain ⟨_, _, _, c, hc, hcoerc⟩ := gaussQuadForm_local_coercive hx
  let C0 : ℝ := ∑ a : Fin 4, ∑ b : Fin 4, ‖symUnitInvDeriv x a b‖
  have hC0_nonneg : 0 ≤ C0 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  let bound : (Fin 4 → ℝ) → ℝ := fun z => C0 * (2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2)
  have hint_bound : IntegrableOn bound orthant4 MeasureTheory.volume :=
    ((integrable_fin4_exp_prod (half_pos hc)).const_mul (C0 * (2 / c))).integrableOn
  refine hint_bound.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have hcont_g : Continuous (fun z : Fin 4 → ℝ => -gaussIntegrand x z) := by
      refine Continuous.neg (Real.continuous_exp.comp (Continuous.neg ?_))
      change Continuous (fun z : Fin 4 → ℝ => ∑ a : Fin 4, z a * ∑ b : Fin 4, symUnitInv x a b * z b)
      exact continuous_finsetSum Finset.univ fun a _ =>
        (continuous_apply a).mul (continuous_finsetSum Finset.univ fun b _ =>
          continuous_const.mul (continuous_apply b))
    have hcont_q : Continuous (gaussQuadFormFDeriv x) := by
      change Continuous (fun z : Fin 4 → ℝ =>
        ∑ a : Fin 4, ∑ b : Fin 4, (z a * z b) • symUnitInvDeriv x a b)
      exact continuous_finsetSum Finset.univ fun a _ =>
        continuous_finsetSum Finset.univ fun b _ =>
          ((continuous_apply a).mul (continuous_apply b)).smul
            (continuous_const : Continuous fun _ : Fin 4 → ℝ => symUnitInvDeriv x a b)
    change Continuous (fun z : Fin 4 → ℝ => (-gaussIntegrand x z) • gaussQuadFormFDeriv x z)
    exact hcont_g.smul hcont_q
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [gaussIntegrandFDeriv, norm_smul, Real.norm_eq_abs, abs_neg, gaussIntegrand,
      abs_of_nonneg (Real.exp_pos _).le]
    have hnorm_q : ‖gaussQuadFormFDeriv x z‖ ≤ C0 * ∑ i : Fin 4, z i ^ 2 := by
      calc
        ‖∑ a : Fin 4, ∑ b : Fin 4, (z a * z b) • symUnitInvDeriv x a b‖
            ≤ ∑ a : Fin 4, ‖∑ b : Fin 4, (z a * z b) • symUnitInvDeriv x a b‖ :=
              norm_sum_le Finset.univ _
        _ ≤ ∑ a : Fin 4, ∑ b : Fin 4, ‖(z a * z b) • symUnitInvDeriv x a b‖ :=
              Finset.sum_le_sum fun a _ => norm_sum_le Finset.univ _
        _ = ∑ a : Fin 4, ∑ b : Fin 4, |z a * z b| * ‖symUnitInvDeriv x a b‖ := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
              rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ a : Fin 4, ∑ b : Fin 4, (∑ i : Fin 4, z i ^ 2) * ‖symUnitInvDeriv x a b‖ := by
              refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              have h2ab : 2 * |z a * z b| ≤ z a ^ 2 + z b ^ 2 := by
                have hsq : 0 ≤ (|z a| - |z b|) ^ 2 := sq_nonneg _
                rw [abs_mul]
                nlinarith [sq_abs (z a), sq_abs (z b)]
              have ha_le : z a ^ 2 ≤ ∑ i : Fin 4, z i ^ 2 :=
                Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ a)
              have hb_le : z b ^ 2 ≤ ∑ i : Fin 4, z i ^ 2 :=
                Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ b)
              linarith
        _ = C0 * ∑ i : Fin 4, z i ^ 2 := by
              simp only [C0, Finset.sum_mul, mul_comm (∑ i : Fin 4, z i ^ 2)]
    let u : ℝ := (c / 2) * ∑ i : Fin 4, z i ^ 2
    have hu_nonneg : 0 ≤ u := mul_nonneg (half_pos hc).le (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hu_exp : u ≤ Real.exp u := le_trans (by linarith) (Real.add_one_le_exp u)
    have hgauss_le : gaussIntegrand x z ≤ Real.exp (-2 * u) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 := hcoerc x (Metric.mem_closedBall_self (le_of_lt (by positivity))) z
      linarith [show 2 * u = c * ∑ i : Fin 4, z i ^ 2 by dsimp [u]; ring]
    have hmul_le : Real.exp (-2 * u) * u ≤ Real.exp (-u) := by
      have h := mul_le_mul_of_nonneg_left hu_exp (Real.exp_pos (-2 * u)).le
      rwa [← Real.exp_add, show -2 * u + u = -u by ring] at h
    have hsum_eq : ∑ i : Fin 4, z i ^ 2 = (2 / c) * u := by
      dsimp [u]
      field_simp [hc.ne']
    have hprod_eq : Real.exp (-u) = ∏ i : Fin 4, Real.exp (-(c / 2) * z i ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      dsimp [u]
      simp [Finset.mul_sum, neg_mul]
    calc
      gaussIntegrand x z * ‖gaussQuadFormFDeriv x z‖
          ≤ gaussIntegrand x z * (C0 * ∑ i : Fin 4, z i ^ 2) :=
            mul_le_mul_of_nonneg_left hnorm_q (Real.exp_pos _).le
      _ = C0 * (gaussIntegrand x z * ((2 / c) * u)) := by rw [hsum_eq]; ring
      _ ≤ C0 * (Real.exp (-2 * u) * ((2 / c) * u)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0_nonneg
            exact mul_le_mul_of_nonneg_right hgauss_le (mul_nonneg (by positivity) hu_nonneg)
      _ = C0 * (2 / c) * (Real.exp (-2 * u) * u) := by ring
      _ ≤ C0 * (2 / c) * Real.exp (-u) := mul_le_mul_of_nonneg_left hmul_le (by positivity)
      _ = bound z := by dsimp [bound]; rw [hprod_eq]

private theorem integrableOn_gaussIntegrandFDeriv_single {x : Fin 6 → ℝ} (hx : x ∈ gramOpen)
    (k : Fin 6) :
    IntegrableOn (fun z => gaussIntegrandFDeriv x z (Pi.single k 1))
      orthant4 MeasureTheory.volume :=
  (ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1) :
      ((Fin 6 → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ).integrable_comp
    (integrableOn_gaussIntegrandFDeriv hx).integrable

private theorem integral_gaussIntegrandFDeriv_single {x : Fin 6 → ℝ} (hx : x ∈ gramOpen)
    (k : Fin 6) :
    (∫ z in orthant4, gaussIntegrandFDeriv x z) (Pi.single k 1) =
      ∫ z in orthant4, gaussIntegrandFDeriv x z (Pi.single k 1) := by
  have h := (ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)).integral_comp_comm
    (integrableOn_gaussIntegrandFDeriv hx).integrable
  simpa [ContinuousLinearMap.apply_apply] using h.symm

private theorem tendsto_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.exp (-c * t ^ 2)) atTop (nhds 0) := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Filter.Eventually.of_forall fun t => (Real.exp_pos _).le
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have ht2 : t ≤ t ^ 2 := by nlinarith
    refine Real.exp_le_exp.mpr ?_
    nlinarith

private theorem tendsto_affine_mul_exp_neg_mul_sq {a b c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (a * t + b) * Real.exp (-c * t ^ 2)) atTop (nhds 0) := by
  let M : ℝ := |a| + |b|
  have hlim : Tendsto (fun t : ℝ => M * (2 / c) * Real.exp (-(c / 2 * t))) atTop (nhds 0) := by
    have h0 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_const_mul_atTop_of_pos (half_pos hc)).mpr tendsto_id)
    simpa [mul_zero] using h0.const_mul (M * (2 / c))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hlim.neg) hlim ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have hnonneg : 0 ≤ t := by linarith
    have ht2 : t ≤ t ^ 2 := by nlinarith
    have hab : -(M * t) ≤ a * t + b := by
      have : |a * t + b| ≤ M * t := by
        calc
          |a * t + b| ≤ |a * t| + |b| := abs_add_le _ _
          _ = |a| * t + |b| := by rw [abs_mul, abs_of_nonneg hnonneg]
          _ ≤ |a| * t + |b| * t := by nlinarith [abs_nonneg b]
          _ = M * t := by dsimp [M]; ring
      exact neg_le_of_abs_le this
    have hexp_sq : Real.exp (-c * t ^ 2) ≤ Real.exp (-c * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hlin : (c / 2) * t ≤ Real.exp ((c / 2) * t) :=
      le_trans (by linarith) (Real.add_one_le_exp ((c / 2) * t))
    have ht_exp : t * Real.exp (-c * t) ≤ (2 / c) * Real.exp (-(c / 2 * t)) := by
      have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-c * t)).le
      have h2 : (c / 2) * (t * Real.exp (-c * t)) ≤ Real.exp (-(c / 2 * t)) := by
        calc
          (c / 2) * (t * Real.exp (-c * t)) = ((c / 2) * t) * Real.exp (-c * t) := by ring
          _ ≤ Real.exp ((c / 2) * t) * Real.exp (-c * t) := hmul
          _ = Real.exp (-(c / 2 * t)) := by rw [← Real.exp_add]; ring_nf
      have hpos : 0 < c / 2 := half_pos hc
      have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hpos.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, show (c / 2)⁻¹ = 2 / c by ring] at this
    calc
      -(M * (2 / c) * Real.exp (-(c / 2 * t)))
          = -(M * ((2 / c) * Real.exp (-(c / 2 * t)))) := by ring
      _ ≤ -(M * (t * Real.exp (-c * t))) := by
            refine neg_le_neg (mul_le_mul_of_nonneg_left ht_exp (by positivity))
      _ = -(M * t) * Real.exp (-c * t) := by ring
      _ ≤ -(M * t) * Real.exp (-c * t ^ 2) := by
            nlinarith [show 0 ≤ M * t from mul_nonneg (by positivity) hnonneg]
      _ ≤ (a * t + b) * Real.exp (-c * t ^ 2) :=
            mul_le_mul_of_nonneg_right hab (Real.exp_pos _).le
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have hnonneg : 0 ≤ t := by linarith
    have ht2 : t ≤ t ^ 2 := by nlinarith
    have hab : a * t + b ≤ M * t := by
      calc
        a * t + b ≤ |a * t + b| := le_abs_self _
        _ ≤ |a * t| + |b| := abs_add_le _ _
        _ = |a| * t + |b| := by rw [abs_mul, abs_of_nonneg hnonneg]
        _ ≤ |a| * t + |b| * t := by nlinarith [abs_nonneg b]
        _ = M * t := by dsimp [M]; ring
    have hexp_sq : Real.exp (-c * t ^ 2) ≤ Real.exp (-c * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hlin : (c / 2) * t ≤ Real.exp ((c / 2) * t) :=
      le_trans (by linarith) (Real.add_one_le_exp ((c / 2) * t))
    have ht_exp : t * Real.exp (-c * t) ≤ (2 / c) * Real.exp (-(c / 2 * t)) := by
      have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-c * t)).le
      have h2 : (c / 2) * (t * Real.exp (-c * t)) ≤ Real.exp (-(c / 2 * t)) := by
        calc
          (c / 2) * (t * Real.exp (-c * t)) = ((c / 2) * t) * Real.exp (-c * t) := by ring
          _ ≤ Real.exp ((c / 2) * t) * Real.exp (-c * t) := hmul
          _ = Real.exp (-(c / 2 * t)) := by rw [← Real.exp_add]; ring_nf
      have hpos : 0 < c / 2 := half_pos hc
      have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hpos.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, show (c / 2)⁻¹ = 2 / c by ring] at this
    calc
      (a * t + b) * Real.exp (-c * t ^ 2)
          ≤ (M * t) * Real.exp (-c * t ^ 2) :=
            mul_le_mul_of_nonneg_right hab (Real.exp_pos _).le
      _ ≤ (M * t) * Real.exp (-c * t) :=
            mul_le_mul_of_nonneg_left hexp_sq (mul_nonneg (by positivity) hnonneg)
      _ = M * (t * Real.exp (-c * t)) := by ring
      _ ≤ M * ((2 / c) * Real.exp (-(c / 2 * t))) :=
            mul_le_mul_of_nonneg_left ht_exp (by positivity)
      _ = M * (2 / c) * Real.exp (-(c / 2 * t)) := by ring

private theorem integrable_poly2_exp_neg_mul_sq {α β γ c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (α * t ^ 2 + β * t + γ) * Real.exp (-c * t ^ 2))
      MeasureTheory.volume := by
  let M : ℝ := (|α| + |β| + |γ|) * (1 + 2 / c)
  refine ((integrable_exp_neg_mul_sq (half_pos hc)).const_mul M).mono' ?_ ?_
  · exact ((continuous_const.mul (continuous_id.pow 2)).add
      (continuous_const.mul continuous_id) |>.add continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))) |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have ht_le : |t| ≤ 1 + t ^ 2 := by
      rw [← sq_abs t]
      nlinarith [sq_nonneg (|t| - 1)]
    have hpoly : |α * t ^ 2 + β * t + γ| ≤ (|α| + |β| + |γ|) * (1 + t ^ 2) := by
      calc
        |α * t ^ 2 + β * t + γ|
            ≤ |α * t ^ 2 + β * t| + |γ| := abs_add_le _ _
        _ ≤ |α * t ^ 2| + |β * t| + |γ| := by linarith [abs_add_le (α * t ^ 2) (β * t)]
        _ = |α| * t ^ 2 + |β| * |t| + |γ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg t)]
        _ ≤ |α| * (1 + t ^ 2) + |β| * (1 + t ^ 2) + |γ| * (1 + t ^ 2) := by
              nlinarith [sq_nonneg t, abs_nonneg α, abs_nonneg β, abs_nonneg γ]
        _ = (|α| + |β| + |γ|) * (1 + t ^ 2) := by ring
    have hsq_exp : (1 + t ^ 2) * Real.exp (-c * t ^ 2) ≤ (1 + 2 / c) * Real.exp (-(c / 2) * t ^ 2) := by
      have hlin : (c / 2) * t ^ 2 ≤ Real.exp ((c / 2) * t ^ 2) :=
        le_trans (by linarith [mul_nonneg (half_pos hc).le (sq_nonneg t)])
          (Real.add_one_le_exp ((c / 2) * t ^ 2))
      have h1 : Real.exp (-c * t ^ 2) ≤ Real.exp (-(c / 2) * t ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])
      have h2 : t ^ 2 * Real.exp (-c * t ^ 2) ≤ (2 / c) * Real.exp (-(c / 2) * t ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-c * t ^ 2)).le
        have h2' : (c / 2) * (t ^ 2 * Real.exp (-c * t ^ 2)) ≤ Real.exp (-(c / 2) * t ^ 2) := by
          calc
            (c / 2) * (t ^ 2 * Real.exp (-c * t ^ 2))
                = ((c / 2) * t ^ 2) * Real.exp (-c * t ^ 2) := by ring
            _ ≤ Real.exp ((c / 2) * t ^ 2) * Real.exp (-c * t ^ 2) := hmul
            _ = Real.exp (-(c / 2) * t ^ 2) := by rw [← Real.exp_add]; ring_nf
        have hpos : 0 < c / 2 := half_pos hc
        have := mul_le_mul_of_nonneg_left h2' (inv_nonneg.mpr hpos.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, show (c / 2)⁻¹ = 2 / c by ring] at this
      linarith
    calc
      |α * t ^ 2 + β * t + γ| * Real.exp (-c * t ^ 2)
          ≤ (|α| + |β| + |γ|) * (1 + t ^ 2) * Real.exp (-c * t ^ 2) :=
            mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = (|α| + |β| + |γ|) * ((1 + t ^ 2) * Real.exp (-c * t ^ 2)) := by ring
      _ ≤ (|α| + |β| + |γ|) * ((1 + 2 / c) * Real.exp (-(c / 2) * t ^ 2)) :=
            mul_le_mul_of_nonneg_left hsq_exp (by positivity)
      _ = M * Real.exp (-(c / 2) * t ^ 2) := by dsimp [M]; ring

private theorem hasDerivAt_quadForm_line {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ = A)
    (u₀ d : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (u₀ + s • d) ⬝ᵥ (A *ᵥ (u₀ + s • d)))
      (2 * (d ⬝ᵥ (A *ᵥ (u₀ + t • d)))) t := by
  have heq : (fun s : ℝ => (u₀ + s • d) ⬝ᵥ (A *ᵥ (u₀ + s • d))) =
      fun s : ℝ => (u₀ ⬝ᵥ (A *ᵥ u₀)) + 2 * (d ⬝ᵥ (A *ᵥ u₀)) * s + (d ⬝ᵥ (A *ᵥ d)) * s ^ 2 := by
    ext s
    have hsymm : u₀ ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ (A *ᵥ u₀) := by
      rw [Matrix.dotProduct_mulVec]
      nth_rw 1 [← hA]
      rw [Matrix.vecMul_transpose, dotProduct_comm]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, hsymm]
    ring
  rw [heq]
  have hd : HasDerivAt
      (fun s : ℝ => (u₀ ⬝ᵥ (A *ᵥ u₀)) + 2 * (d ⬝ᵥ (A *ᵥ u₀)) * s + (d ⬝ᵥ (A *ᵥ d)) * s ^ 2)
      (0 + (2 * (d ⬝ᵥ (A *ᵥ u₀))) * 1 + (d ⬝ᵥ (A *ᵥ d)) * (2 * t)) t := by
    refine ((hasDerivAt_const t _).add ((hasDerivAt_id t).const_mul (2 * (d ⬝ᵥ (A *ᵥ u₀))))).add ?_
    simpa [pow_one] using ((hasDerivAt_id t).pow 2).const_mul (d ⬝ᵥ (A *ᵥ d))
  refine hd.congr_deriv ?_
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

private def orthant3 : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun _ : Fin 3 => Set.Ioi (0 : ℝ)

private theorem measurableSet_orthant3 : MeasurableSet orthant3 :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

private def orthant2 : Set (Fin 2 → ℝ) :=
  Set.univ.pi fun _ : Fin 2 => Set.Ioi (0 : ℝ)

private theorem measurableSet_orthant2 : MeasurableSet orthant2 :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

private theorem insertNth3_eq (t : ℝ) (v : Fin 3 → ℝ) :
    Fin.insertNth (3 : Fin 4) t v = ![v 0, v 1, v 2, t] := by
  ext i
  fin_cases i
  · exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 4 => ℝ) 3 t v 0
  · exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 4 => ℝ) 3 t v 1
  · exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 4 => ℝ) 3 t v 2
  · exact Fin.insertNth_apply_same (α := fun _ : Fin 4 => ℝ) (3 : Fin 4) t v

private theorem insertNth2_eq (s : ℝ) (y : Fin 2 → ℝ) :
    Fin.insertNth (2 : Fin 3) s y = ![y 0, y 1, s] := by
  ext i
  fin_cases i
  · exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℝ) 2 s y 0
  · exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℝ) 2 s y 1
  · exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) (2 : Fin 3) s y

private theorem orthant4_ibp_q (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ = A)
    {c : ℝ} (hc : 0 < c)
    (hcoerc : ∀ u : Fin 4 → ℝ, c * (∑ i : Fin 4, u i ^ 2) ≤ u ⬝ᵥ (A *ᵥ u)) :
    ∫ u in orthant4, (2 * (A *ᵥ u) 2 * (A *ᵥ u) 3 - A 2 3) * Real.exp (-(u ⬝ᵥ (A *ᵥ u))) =
      ∫ v in orthant3,
        (A *ᵥ ![v 0, v 1, v 2, 0]) 2 *
          Real.exp (-(![v 0, v 1, v 2, 0] ⬝ᵥ (A *ᵥ ![v 0, v 1, v 2, 0]))) := by
  let e3 : (ℝ × (Fin 3 → ℝ)) ≃ᵐ (Fin 4 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 3).symm
  have hmp3 : MeasurePreserving e3 MeasureTheory.volume MeasureTheory.volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 3).symm
  have he3_eq : ∀ p : ℝ × (Fin 3 → ℝ), e3 p = ![p.2 0, p.2 1, p.2 2, p.1] := fun ⟨t, v⟩ => by
    ext j
    dsimp only [e3]
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, insertNth3_eq]
  have hpre3 : e3 ⁻¹' orthant4 = Set.Ioi (0 : ℝ) ×ˢ orthant3 := by
    ext ⟨t, v⟩
    rw [Set.mem_preimage, he3_eq (t, v)]
    simp only [orthant4, orthant3, Set.mem_univ_pi, Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro h
      refine ⟨h 3, fun i => ?_⟩
      fin_cases i
      · exact h 0
      · exact h 1
      · exact h 2
    · rintro ⟨ht, hv⟩ i
      fin_cases i
      · exact hv 0
      · exact hv 1
      · exact hv 2
      · exact ht
  let f : (Fin 4 → ℝ) → ℝ :=
    fun u => (2 * (A *ᵥ u) 2 * (A *ᵥ u) 3 - A 2 3) * Real.exp (-(u ⬝ᵥ (A *ᵥ u)))
  have hf_int : Integrable f MeasureTheory.volume := by
    let wnorm : ℝ := (∑ a : Fin 4, ∑ b : Fin 4, |A a b|)
    let C1 : ℝ := 2 * wnorm ^ 2 + |A 2 3|
    have hC1 : 0 ≤ C1 := by positivity
    let udom := fun u : Fin 4 → ℝ => C1 * (1 + ∑ i : Fin 4, u i ^ 2) * Real.exp (-(c * ∑ i : Fin 4, u i ^ 2))
    have hdom_int : Integrable (fun u : Fin 4 → ℝ => C1 * (1 + 2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * u i ^ 2))
        MeasureTheory.volume :=
      (integrable_fin4_exp_prod (half_pos hc)).const_mul (C1 * (1 + 2 / c))
    refine hdom_int.mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hmulVec_cont : ∀ i : Fin 4, Continuous (fun u : Fin 4 → ℝ => (A *ᵥ u) i) := fun i =>
        continuous_finsetSum Finset.univ fun j _ => continuous_const.mul (continuous_apply j)
      exact (((continuous_const.mul (hmulVec_cont 2)).mul (hmulVec_cont 3)).sub continuous_const).mul
        (Real.continuous_exp.comp (Continuous.neg (continuous_finsetSum Finset.univ fun i _ =>
          (continuous_apply i).mul (hmulVec_cont i))))
    · refine Filter.Eventually.of_forall fun u => ?_
      have hw_le : ∀ i : Fin 4, |(A *ᵥ u) i| ^ 2 ≤ wnorm ^ 2 * ∑ j : Fin 4, u j ^ 2 := by
        intro i
        have hi : |(A *ᵥ u) i| ≤ ∑ j : Fin 4, |A i j| * |u j| := by
          simp only [Matrix.mulVec, dotProduct]
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => (abs_mul _ _).le)
        have hwn : ∑ j : Fin 4, |A i j| ≤ wnorm := by
          dsimp [wnorm]
          exact Finset.single_le_sum
            (fun r _ => Finset.sum_nonneg fun s _ => abs_nonneg (A r s)) (Finset.mem_univ i)
        have hstep : |(A *ᵥ u) i| ≤ wnorm * Real.sqrt (∑ j : Fin 4, u j ^ 2) := by
          calc
            |(A *ᵥ u) i| ≤ ∑ j : Fin 4, |A i j| * |u j| := hi
            _ ≤ ∑ j : Fin 4, |A i j| * Real.sqrt (∑ m : Fin 4, u m ^ 2) :=
                Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
                  ((Real.sqrt_sq_eq_abs _).symm ▸ Real.sqrt_le_sqrt
                    (Finset.single_le_sum (fun m _ => sq_nonneg _) (Finset.mem_univ j)))
                  (abs_nonneg _)
            _ = (∑ j : Fin 4, |A i j|) * Real.sqrt (∑ m : Fin 4, u m ^ 2) := (Finset.sum_mul _ _ _).symm
            _ ≤ wnorm * Real.sqrt (∑ m : Fin 4, u m ^ 2) :=
                mul_le_mul_of_nonneg_right hwn (Real.sqrt_nonneg _)
        have hsq := sq_le_sq' (by nlinarith [abs_nonneg ((A *ᵥ u) i), mul_nonneg (show 0 ≤ wnorm from
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _) (Real.sqrt_nonneg (∑ m : Fin 4, u m ^ 2))]) hstep
        simpa [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun m _ => sq_nonneg (u m))] using hsq
      have hpoly : |2 * (A *ᵥ u) 2 * (A *ᵥ u) 3 - A 2 3| ≤ C1 * (1 + ∑ i : Fin 4, u i ^ 2) := by
        have hprod : 2 * |(A *ᵥ u) 2| * |(A *ᵥ u) 3| ≤ |(A *ᵥ u) 2| ^ 2 + |(A *ᵥ u) 3| ^ 2 := by
          nlinarith [sq_nonneg (|(A *ᵥ u) 2| - |(A *ᵥ u) 3|)]
        have hsum_nn : 0 ≤ ∑ i : Fin 4, u i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hmul_nn : 0 ≤ |A 2 3| * ∑ i : Fin 4, u i ^ 2 := mul_nonneg (abs_nonneg _) hsum_nn
        have hw_nn : 0 ≤ 2 * wnorm ^ 2 := by positivity
        calc
          |2 * (A *ᵥ u) 2 * (A *ᵥ u) 3 - A 2 3|
              ≤ |2 * (A *ᵥ u) 2 * (A *ᵥ u) 3| + |A 2 3| := abs_sub _ _
          _ = 2 * |(A *ᵥ u) 2| * |(A *ᵥ u) 3| + |A 2 3| := by
                simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
          _ ≤ (|(A *ᵥ u) 2| ^ 2 + |(A *ᵥ u) 3| ^ 2) + |A 2 3| := by linarith [hprod]
          _ ≤ 2 * wnorm ^ 2 * (∑ i : Fin 4, u i ^ 2) + |A 2 3| := by linarith [hw_le 2, hw_le 3]
          _ ≤ C1 * (1 + ∑ i : Fin 4, u i ^ 2) := by
                dsimp [C1]
                nlinarith
      have hquad_exp : (1 + ∑ i : Fin 4, u i ^ 2) * Real.exp (-(u ⬝ᵥ (A *ᵥ u))) ≤
          (1 + 2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * u i ^ 2) := by
        let ssum := ∑ i : Fin 4, u i ^ 2
        have hss_nn : 0 ≤ ssum := Finset.sum_nonneg fun i _ => sq_nonneg _
        have hexp_le : Real.exp (-(u ⬝ᵥ (A *ᵥ u))) ≤ Real.exp (-c * ssum) :=
          Real.exp_le_exp.mpr (by linarith [hcoerc u])
        have hlin : (c / 2) * ssum ≤ Real.exp ((c / 2) * ssum) :=
          le_trans (by linarith [mul_nonneg (half_pos hc).le hss_nn])
            (Real.add_one_le_exp ((c / 2) * ssum))
        have h2 : ssum * Real.exp (-c * ssum) ≤ (2 / c) * Real.exp (-(c / 2) * ssum) := by
          have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-c * ssum)).le
          have h2' : (c / 2) * (ssum * Real.exp (-c * ssum)) ≤ Real.exp (-(c / 2) * ssum) := by
            calc
              (c / 2) * (ssum * Real.exp (-c * ssum)) = ((c / 2) * ssum) * Real.exp (-c * ssum) := by ring
              _ ≤ Real.exp ((c / 2) * ssum) * Real.exp (-c * ssum) := hmul
              _ = Real.exp (-(c / 2) * ssum) := by rw [← Real.exp_add]; ring_nf
          have hpos : 0 < c / 2 := half_pos hc
          have := mul_le_mul_of_nonneg_left h2' (inv_nonneg.mpr hpos.le)
          rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, show (c / 2)⁻¹ = 2 / c by ring] at this
        have h1 : Real.exp (-c * ssum) ≤ Real.exp (-(c / 2) * ssum) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hprod : Real.exp (-(c / 2) * ssum) = ∏ i : Fin 4, Real.exp (-(c / 2) * u i ^ 2) := by
          rw [← Real.exp_sum]
          congr 1
          dsimp [ssum]
          simp [Finset.mul_sum, neg_mul]
        calc
          (1 + ssum) * Real.exp (-(u ⬝ᵥ (A *ᵥ u)))
              ≤ (1 + ssum) * Real.exp (-c * ssum) :=
                mul_le_mul_of_nonneg_left hexp_le (by linarith)
          _ = Real.exp (-c * ssum) + ssum * Real.exp (-c * ssum) := by ring
          _ ≤ Real.exp (-(c / 2) * ssum) + (2 / c) * Real.exp (-(c / 2) * ssum) := add_le_add h1 h2
          _ = (1 + 2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * u i ^ 2) := by rw [hprod]; ring
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        |2 * (A *ᵥ u) 2 * (A *ᵥ u) 3 - A 2 3| * Real.exp (-(u ⬝ᵥ (A *ᵥ u)))
            ≤ C1 * (1 + ∑ i : Fin 4, u i ^ 2) * Real.exp (-(u ⬝ᵥ (A *ᵥ u))) :=
              mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
        _ = C1 * ((1 + ∑ i : Fin 4, u i ^ 2) * Real.exp (-(u ⬝ᵥ (A *ᵥ u)))) := by ring
        _ ≤ C1 * ((1 + 2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * u i ^ 2)) :=
              mul_le_mul_of_nonneg_left hquad_exp hC1
        _ = C1 * (1 + 2 / c) * ∏ i : Fin 4, Real.exp (-(c / 2) * u i ^ 2) := by ring
  rw [← hmp3.setIntegral_preimage_emb e3.measurableEmbedding f orthant4, hpre3]
  have hswap := (Measure.measurePreserving_swap (μ := MeasureTheory.volume)
    (ν := MeasureTheory.volume)).setIntegral_preimage_emb
    (MeasurableEquiv.prodComm (α := Fin 3 → ℝ) (β := ℝ)).measurableEmbedding
    (fun p : ℝ × (Fin 3 → ℝ) => f (e3 p)) (Set.Ioi (0 : ℝ) ×ˢ orthant3)
  have hpre_swap : (Prod.swap ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ orthant3) : Set ((Fin 3 → ℝ) × ℝ)) =
      orthant3 ×ˢ Set.Ioi (0 : ℝ) := by
    ext ⟨v, t⟩
    simp [Set.mem_prod, and_comm]
  rw [hpre_swap] at hswap
  have hswap_vol :
      (∫ x in orthant3 ×ˢ Set.Ioi (0 : ℝ), f (e3 x.swap)) =
        ∫ y in Set.Ioi (0 : ℝ) ×ˢ orthant3, f (e3 y) := by
    rw [Measure.volume_eq_prod (α := Fin 3 → ℝ) (β := ℝ),
      Measure.volume_eq_prod (α := ℝ) (β := Fin 3 → ℝ)]
    exact hswap
  rw [← hswap_vol]
  have hint_prod : IntegrableOn (fun q : (Fin 3 → ℝ) × ℝ => f (e3 q.swap))
      (orthant3 ×ˢ Set.Ioi (0 : ℝ))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine Integrable.integrableOn ?_
    let e3swap : ((Fin 3 → ℝ) × ℝ) ≃ᵐ (Fin 4 → ℝ) :=
      (MeasurableEquiv.prodComm (α := Fin 3 → ℝ) (β := ℝ)).trans e3
    have hmp_comp : MeasurePreserving e3swap
        (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume :=
      hmp3.comp (Measure.measurePreserving_swap (μ := MeasureTheory.volume)
        (ν := MeasureTheory.volume))
    exact (hmp_comp.integrable_comp_emb e3swap.measurableEmbedding).mpr hf_int
  rw [Measure.volume_eq_prod (α := Fin 3 → ℝ) (β := ℝ)]
  rw [setIntegral_prod (fun q : (Fin 3 → ℝ) × ℝ => f (e3 q.swap)) hint_prod]
  refine setIntegral_congr_fun measurableSet_orthant3 fun v _ => ?_
  let u0 : Fin 4 → ℝ := ![v 0, v 1, v 2, 0]
  have hline : ∀ t : ℝ, (e3 (t, v)) = u0 + t • Pi.single (3 : Fin 4) 1 := by
    intro t
    rw [he3_eq (t, v)]
    dsimp [u0]
    ext i
    fin_cases i <;> simp
  let F : ℝ → ℝ := fun t => -((A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2) *
    Real.exp (-((u0 + t • Pi.single (3 : Fin 4) 1) ⬝ᵥ (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1))))
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt F (f (e3 (t, v))) t := by
    intro t _
    rw [hline t]
    have hlin2 : HasDerivAt (fun s : ℝ => -((A *ᵥ (u0 + s • Pi.single (3 : Fin 4) 1)) 2)) (-A 2 3) t := by
      have heq : (fun s : ℝ => -((A *ᵥ (u0 + s • Pi.single (3 : Fin 4) 1)) 2)) =
          fun s : ℝ => -(A *ᵥ u0) 2 + (-A 2 3) * s := by
        ext s
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Matrix.mulVec_single, Matrix.col_apply, MulOpposite.op_one, one_smul]
        ring
      rw [heq]
      simpa using ((hasDerivAt_id t).const_mul (-A 2 3)).const_add (-(A *ᵥ u0) 2)
    have hq := hasDerivAt_quadForm_line hA u0 (Pi.single (3 : Fin 4) 1) t
    have hexp : HasDerivAt
        (fun s : ℝ => Real.exp (-((u0 + s • Pi.single (3 : Fin 4) 1) ⬝ᵥ
          (A *ᵥ (u0 + s • Pi.single (3 : Fin 4) 1)))))
        ((-(2 * (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 3)) *
          Real.exp (-((u0 + t • Pi.single (3 : Fin 4) 1) ⬝ᵥ
            (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1))))) t := by
      have hq' := hq.neg
      have hdot : (Pi.single (3 : Fin 4) 1 : Fin 4 → ℝ) ⬝ᵥ (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) =
          (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 3 := by simp
      rw [hdot] at hq'
      simpa [mul_comm] using hq'.exp
    refine (hlin2.mul hexp).congr_deriv ?_
    dsimp [f]
    ring
  have htend : Tendsto F atTop (nhds 0) := by
    let a1 : ℝ := A 2 3
    let b1 : ℝ := (A *ᵥ u0) 2
    let M : ℝ := |a1| + |b1|
    have hbound_F : ∀ t : ℝ, 0 ≤ t → ‖F t‖ ≤ (M * t + M) * Real.exp (-c * t ^ 2) := by
      intro t ht
      have hw : |(A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2| ≤ M * t + M := by
        have heq : (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2 = a1 * t + b1 := by
          simp [Matrix.mulVec_add, Matrix.mulVec_smul, a1, b1]
          ring
        rw [heq]
        calc
          |a1 * t + b1| ≤ |a1 * t| + |b1| := abs_add_le _ _
          _ = |a1| * t + |b1| := by rw [abs_mul, abs_of_nonneg ht]
          _ ≤ M * t + M := by dsimp [M]; nlinarith [abs_nonneg a1, abs_nonneg b1]
      have hq_ge : c * t ^ 2 ≤
          (u0 + t • Pi.single (3 : Fin 4) 1) ⬝ᵥ (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) := by
        let w : Fin 4 → ℝ := u0 + t • Pi.single (3 : Fin 4) 1
        have h1 : c * ∑ i : Fin 4, w i ^ 2 ≤ w ⬝ᵥ (A *ᵥ w) := hcoerc w
        have h2 : t ^ 2 ≤ ∑ i : Fin 4, w i ^ 2 := by
          rw [Fin.sum_univ_four]
          have hw3 : w 3 = t := by dsimp [w]; rw [Pi.single_eq_same]; simp [u0]
          rw [hw3]
          nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
        nlinarith
      have hexp : Real.exp (-((u0 + t • Pi.single (3 : Fin 4) 1) ⬝ᵥ
          (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)))) ≤ Real.exp (-c * t ^ 2) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.norm_eq_abs]
      dsimp [F]
      rw [abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
      calc
        |(A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2| * Real.exp _
            ≤ (M * t + M) * Real.exp _ := mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
        _ ≤ (M * t + M) * Real.exp (-c * t ^ 2) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
    have h0 := tendsto_affine_mul_exp_neg_mul_sq (a := M) (b := M) hc
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h0 (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_)
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact hbound_F t ht
  have hint_slice : IntegrableOn (fun t => f (e3 (t, v))) (Set.Ioi 0) MeasureTheory.volume := by
    let α : ℝ := 2 * |A 2 3| * |A 3 3|
    let β : ℝ := 2 * (|A 2 3| * |(A *ᵥ u0) 3| + |(A *ᵥ u0) 2| * |A 3 3|)
    let γ : ℝ := 2 * |(A *ᵥ u0) 2| * |(A *ᵥ u0) 3| + |A 2 3|
    refine ((integrable_poly2_exp_neg_mul_sq (α := α) (β := β) (γ := γ) hc).integrableOn).mono'
      ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hu2 : Continuous (fun t : ℝ => (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) (1 : ℝ))) 2) := by
        have heq : (fun t : ℝ => (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) (1 : ℝ))) 2) =
            fun t : ℝ => (A *ᵥ u0) 2 + A 2 3 * t := by
          ext t; simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
        rw [heq]; fun_prop
      have hu3 : Continuous (fun t : ℝ => (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) (1 : ℝ))) 3) := by
        have heq : (fun t : ℝ => (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) (1 : ℝ))) 3) =
            fun t : ℝ => (A *ᵥ u0) 3 + A 3 3 * t := by
          ext t; simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
        rw [heq]; fun_prop
      have hq : Continuous (fun t : ℝ => (u0 + t • (Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
          (A *ᵥ (u0 + t • (Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)))) := by
        refine continuous_finsetSum Finset.univ fun i _ => ?_
        have hi : Continuous (fun t : ℝ => (u0 + t • (Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)) i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          fun_prop
        have hwi : Continuous (fun t : ℝ =>
            (A *ᵥ (u0 + t • (Pi.single (3 : Fin 4) (1 : ℝ) : Fin 4 → ℝ))) i) := by
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          fun_prop
        exact hi.fun_mul hwi
      simpa only [f, hline, Function.comp_apply] using
        (((continuous_const.fun_mul hu2).fun_mul hu3).fun_sub continuous_const).fun_mul
          (Real.continuous_exp.comp hq.fun_neg)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hline t]
      have ht0 : 0 ≤ t := ht.le
      have hw2 : (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2 = A 2 3 * t + (A *ᵥ u0) 2 := by
        simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
      have hw3 : (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 3 = A 3 3 * t + (A *ᵥ u0) 3 := by
        simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
      have hpoly : |2 * (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2 *
          (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 3 - A 2 3| ≤ α * t ^ 2 + β * t + γ := by
        rw [hw2, hw3]
        have h1 : |A 2 3 * t + (A *ᵥ u0) 2| ≤ |A 2 3| * t + |(A *ᵥ u0) 2| := by
          calc
            |A 2 3 * t + (A *ᵥ u0) 2| ≤ |A 2 3 * t| + |(A *ᵥ u0) 2| := abs_add_le _ _
            _ = |A 2 3| * t + |(A *ᵥ u0) 2| := by rw [abs_mul, abs_of_nonneg ht0]
        have h2 : |A 3 3 * t + (A *ᵥ u0) 3| ≤ |A 3 3| * t + |(A *ᵥ u0) 3| := by
          calc
            |A 3 3 * t + (A *ᵥ u0) 3| ≤ |A 3 3 * t| + |(A *ᵥ u0) 3| := abs_add_le _ _
            _ = |A 3 3| * t + |(A *ᵥ u0) 3| := by rw [abs_mul, abs_of_nonneg ht0]
        calc
          |2 * (A 2 3 * t + (A *ᵥ u0) 2) * (A 3 3 * t + (A *ᵥ u0) 3) - A 2 3|
              ≤ 2 * |A 2 3 * t + (A *ᵥ u0) 2| * |A 3 3 * t + (A *ᵥ u0) 3| + |A 2 3| := by
                have := abs_sub (2 * (A 2 3 * t + (A *ᵥ u0) 2) * (A 3 3 * t + (A *ᵥ u0) 3)) (A 2 3)
                simpa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc] using this
          _ ≤ 2 * (|A 2 3| * t + |(A *ᵥ u0) 2|) * (|A 3 3| * t + |(A *ᵥ u0) 3|) + |A 2 3| := by
                have hmul := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2))
                  h2 (abs_nonneg _) (by positivity)
                linarith
          _ = α * t ^ 2 + β * t + γ := by dsimp [α, β, γ]; ring
      have hq_ge : c * t ^ 2 ≤
          (u0 + t • Pi.single (3 : Fin 4) 1) ⬝ᵥ (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) := by
        let w : Fin 4 → ℝ := u0 + t • Pi.single (3 : Fin 4) 1
        have h1 : c * ∑ i : Fin 4, w i ^ 2 ≤ w ⬝ᵥ (A *ᵥ w) := hcoerc w
        have h2 : t ^ 2 ≤ ∑ i : Fin 4, w i ^ 2 := by
          rw [Fin.sum_univ_four]
          have hw3 : w 3 = t := by dsimp [w]; rw [Pi.single_eq_same]; simp [u0]
          rw [hw3]
          nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
        nlinarith
      have hexp : Real.exp (-((u0 + t • Pi.single (3 : Fin 4) 1) ⬝ᵥ
          (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)))) ≤ Real.exp (-c * t ^ 2) :=
        Real.exp_le_exp.mpr (by linarith)
      dsimp [f]
      rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        |2 * (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 2 *
            (A *ᵥ (u0 + t • Pi.single (3 : Fin 4) 1)) 3 - A 2 3| * Real.exp _
            ≤ (α * t ^ 2 + β * t + γ) * Real.exp _ :=
              mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
        _ ≤ (α * t ^ 2 + β * t + γ) * Real.exp (-c * t ^ 2) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_slice htend
  change ∫ t in Set.Ioi (0 : ℝ), f (e3 (t, v)) = _
  rw [hftc]
  dsimp [F, u0]
  simp [zero_smul, add_zero]

private theorem orthant3_ibp_p (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Aᵀ = A)
    {c : ℝ} (hc : 0 < c)
    (hcoerc : ∀ u : Fin 4 → ℝ, c * (∑ i : Fin 4, u i ^ 2) ≤ u ⬝ᵥ (A *ᵥ u)) :
    ∫ v in orthant3,
        (A *ᵥ ![v 0, v 1, v 2, 0]) 2 *
          Real.exp (-(![v 0, v 1, v 2, 0] ⬝ᵥ (A *ᵥ ![v 0, v 1, v 2, 0]))) =
      (1 / 2 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
        Real.exp (-(A 0 0 * t ^ 2 + 2 * A 0 1 * t * r + A 1 1 * r ^ 2)) := by
  let e2 : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  have hmp2 : MeasurePreserving e2 MeasureTheory.volume MeasureTheory.volume :=
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  have he2_eq : ∀ p : ℝ × (Fin 2 → ℝ), e2 p = ![p.2 0, p.2 1, p.1] := fun ⟨s, y⟩ => by
    ext j
    dsimp only [e2]
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply, insertNth2_eq]
  have hpre2 : e2 ⁻¹' orthant3 = Set.Ioi (0 : ℝ) ×ˢ orthant2 := by
    ext ⟨s, y⟩
    rw [Set.mem_preimage, he2_eq (s, y)]
    simp only [orthant3, orthant2, Set.mem_univ_pi, Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro h
      refine ⟨h 2, fun i => ?_⟩
      fin_cases i
      · exact h 0
      · exact h 1
    · rintro ⟨hs, hy⟩ i
      fin_cases i
      · exact hy 0
      · exact hy 1
      · exact hs
  let g : (Fin 3 → ℝ) → ℝ := fun v =>
    (A *ᵥ ![v 0, v 1, v 2, 0]) 2 *
      Real.exp (-(![v 0, v 1, v 2, 0] ⬝ᵥ (A *ᵥ ![v 0, v 1, v 2, 0])))
  have hg_int : Integrable g MeasureTheory.volume := by
    let wnorm : ℝ := ∑ j : Fin 4, |A 2 j|
    have hwn_nn : 0 ≤ wnorm := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ((integrable_fin3_exp_prod (half_pos hc)).const_mul (wnorm * (1 + 2 / c))).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have hvec : Continuous (fun v : Fin 3 → ℝ => (![v 0, v 1, v 2, 0] : Fin 4 → ℝ)) := by
        refine continuous_pi fun i => ?_
        fin_cases i
        · exact continuous_apply 0
        · exact continuous_apply 1
        · exact continuous_apply 2
        · exact continuous_const
      have hw2 : Continuous (fun v : Fin 3 → ℝ => (A *ᵥ ![v 0, v 1, v 2, 0]) 2) :=
        continuous_finsetSum Finset.univ fun j _ => continuous_const.mul ((continuous_apply j).comp hvec)
      have hq : Continuous (fun v : Fin 3 → ℝ =>
          ![v 0, v 1, v 2, 0] ⬝ᵥ (A *ᵥ ![v 0, v 1, v 2, 0])) :=
        continuous_finsetSum Finset.univ fun i _ => ((continuous_apply i).comp hvec).mul
          (continuous_finsetSum Finset.univ fun j _ => continuous_const.mul ((continuous_apply j).comp hvec))
      exact hw2.mul (Real.continuous_exp.comp hq.neg)
    · refine Filter.Eventually.of_forall fun v => ?_
      let u : Fin 4 → ℝ := ![v 0, v 1, v 2, 0]
      have hsum_u : ∑ i : Fin 4, u i ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
        simp [u, Fin.sum_univ_four, Fin.sum_univ_three]
      have hw2_le : |(A *ᵥ u) 2| ≤ wnorm * (1 + ∑ i : Fin 3, v i ^ 2) := by
        have hi : |(A *ᵥ u) 2| ≤ ∑ j : Fin 4, |A 2 j| * |u j| := by
          simp only [Matrix.mulVec, dotProduct]
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => (abs_mul _ _).le)
        calc
          |(A *ᵥ u) 2| ≤ ∑ j : Fin 4, |A 2 j| * |u j| := hi
          _ ≤ ∑ j : Fin 4, |A 2 j| * (1 + ∑ i : Fin 4, u i ^ 2) := by
                refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                have hj_sq : u j ^ 2 ≤ ∑ i : Fin 4, u i ^ 2 :=
                  Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
                have habs : |u j| ≤ 1 + u j ^ 2 := by
                  rw [← sq_abs]
                  nlinarith [sq_nonneg (|u j| - 1)]
                linarith
          _ = wnorm * (1 + ∑ i : Fin 3, v i ^ 2) := by
                rw [← Finset.sum_mul, hsum_u]
      let ssum := ∑ i : Fin 3, v i ^ 2
      have hss_nn : 0 ≤ ssum := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hexp_le : Real.exp (-(u ⬝ᵥ (A *ᵥ u))) ≤ Real.exp (-c * ssum) := by
        refine Real.exp_le_exp.mpr ?_
        have hcu : c * ssum ≤ u ⬝ᵥ (A *ᵥ u) := by
          simpa [ssum, hsum_u] using hcoerc u
        rw [neg_mul]
        exact neg_le_neg hcu
      have hlin : (c / 2) * ssum ≤ Real.exp ((c / 2) * ssum) :=
        le_trans (by linarith [mul_nonneg (half_pos hc).le hss_nn])
          (Real.add_one_le_exp ((c / 2) * ssum))
      have h2 : ssum * Real.exp (-c * ssum) ≤ (2 / c) * Real.exp (-(c / 2) * ssum) := by
        have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-c * ssum)).le
        have h2' : (c / 2) * (ssum * Real.exp (-c * ssum)) ≤ Real.exp (-(c / 2) * ssum) := by
          calc
            (c / 2) * (ssum * Real.exp (-c * ssum)) = ((c / 2) * ssum) * Real.exp (-c * ssum) := by ring
            _ ≤ Real.exp ((c / 2) * ssum) * Real.exp (-c * ssum) := hmul
            _ = Real.exp (-(c / 2) * ssum) := by rw [← Real.exp_add]; ring_nf
        have hpos : 0 < c / 2 := half_pos hc
        have := mul_le_mul_of_nonneg_left h2' (inv_nonneg.mpr hpos.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, show (c / 2)⁻¹ = 2 / c by ring] at this
      have h1 : Real.exp (-c * ssum) ≤ Real.exp (-(c / 2) * ssum) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hprod : Real.exp (-(c / 2) * ssum) = ∏ i : Fin 3, Real.exp (-(c / 2) * v i ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        dsimp [ssum]
        simp [Finset.mul_sum, neg_mul]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        |(A *ᵥ u) 2| * Real.exp (-(u ⬝ᵥ (A *ᵥ u)))
            ≤ wnorm * (1 + ssum) * Real.exp (-c * ssum) := by
              refine mul_le_mul hw2_le hexp_le (Real.exp_pos _).le (by positivity)
        _ = wnorm * (Real.exp (-c * ssum) + ssum * Real.exp (-c * ssum)) := by ring
        _ ≤ wnorm * (Real.exp (-(c / 2) * ssum) + (2 / c) * Real.exp (-(c / 2) * ssum)) :=
              mul_le_mul_of_nonneg_left (add_le_add h1 h2) hwn_nn
        _ = wnorm * (1 + 2 / c) * ∏ i : Fin 3, Real.exp (-(c / 2) * v i ^ 2) := by rw [hprod]; ring
  rw [← hmp2.setIntegral_preimage_emb e2.measurableEmbedding g orthant3, hpre2]
  have hswap := (Measure.measurePreserving_swap (μ := MeasureTheory.volume)
    (ν := MeasureTheory.volume)).setIntegral_preimage_emb
    (MeasurableEquiv.prodComm (α := Fin 2 → ℝ) (β := ℝ)).measurableEmbedding
    (fun p : ℝ × (Fin 2 → ℝ) => g (e2 p)) (Set.Ioi (0 : ℝ) ×ˢ orthant2)
  have hpre_swap : (Prod.swap ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ orthant2) : Set ((Fin 2 → ℝ) × ℝ)) =
      orthant2 ×ˢ Set.Ioi (0 : ℝ) := by
    ext ⟨y, s⟩
    simp [Set.mem_prod, and_comm]
  rw [hpre_swap] at hswap
  have hswap_vol :
      (∫ x in orthant2 ×ˢ Set.Ioi (0 : ℝ), g (e2 x.swap)) =
        ∫ y in Set.Ioi (0 : ℝ) ×ˢ orthant2, g (e2 y) := by
    rw [Measure.volume_eq_prod (α := Fin 2 → ℝ) (β := ℝ),
      Measure.volume_eq_prod (α := ℝ) (β := Fin 2 → ℝ)]
    exact hswap
  rw [← hswap_vol]
  have hint_prod : IntegrableOn (fun q : (Fin 2 → ℝ) × ℝ => g (e2 q.swap))
      (orthant2 ×ˢ Set.Ioi (0 : ℝ))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine Integrable.integrableOn ?_
    let e2swap : ((Fin 2 → ℝ) × ℝ) ≃ᵐ (Fin 3 → ℝ) :=
      (MeasurableEquiv.prodComm (α := Fin 2 → ℝ) (β := ℝ)).trans e2
    have hmp_comp : MeasurePreserving e2swap
        (MeasureTheory.volume.prod MeasureTheory.volume) MeasureTheory.volume :=
      hmp2.comp (Measure.measurePreserving_swap (μ := MeasureTheory.volume)
        (ν := MeasureTheory.volume))
    exact (hmp_comp.integrable_comp_emb e2swap.measurableEmbedding).mpr hg_int
  rw [Measure.volume_eq_prod (α := Fin 2 → ℝ) (β := ℝ)]
  rw [setIntegral_prod (fun q : (Fin 2 → ℝ) × ℝ => g (e2 q.swap)) hint_prod]
  have hstep2 :
      ∫ y in orthant2, ∫ s in Set.Ioi (0 : ℝ), g (e2 (s, y)) =
        ∫ y in orthant2, (1 / 2 : ℝ) *
          Real.exp (-(![y 0, y 1, 0, 0] ⬝ᵥ (A *ᵥ ![y 0, y 1, 0, 0]))) := by
    refine setIntegral_congr_fun measurableSet_orthant2 fun y _ => ?_
    let u0 : Fin 4 → ℝ := ![y 0, y 1, 0, 0]
    have hline : ∀ s : ℝ, (![(e2 (s, y)) 0, (e2 (s, y)) 1, (e2 (s, y)) 2, 0] : Fin 4 → ℝ) =
        u0 + s • Pi.single (2 : Fin 4) 1 := by
      intro s
      rw [he2_eq (s, y)]
      dsimp [u0]
      ext i
      fin_cases i <;> simp
    let F : ℝ → ℝ := fun s => -(1 / 2 : ℝ) *
      Real.exp (-((u0 + s • Pi.single (2 : Fin 4) 1) ⬝ᵥ (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1))))
    have hderiv : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivAt F (g (e2 (s, y))) s := by
      intro s _
      dsimp [g, F]
      rw [hline s]
      have hq := hasDerivAt_quadForm_line hA u0 (Pi.single (2 : Fin 4) 1) s
      have hdot : (Pi.single (2 : Fin 4) 1 : Fin 4 → ℝ) ⬝ᵥ (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1)) =
          (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1)) 2 := by simp
      rw [hdot] at hq
      have hexp := (hq.neg.exp).const_mul (-(1 / 2 : ℝ))
      refine hexp.congr_deriv ?_
      simp only [Pi.neg_apply]
      ring
    have htend : Tendsto F atTop (nhds 0) := by
      have h0 : Tendsto (fun s : ℝ => (1 / 2 : ℝ) * Real.exp (-c * s ^ 2)) atTop (nhds 0) := by
        simpa [mul_zero] using (tendsto_exp_neg_mul_sq hc).const_mul (1 / 2 : ℝ)
      refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds h0 (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun s => ?_))
      have hq_ge : c * s ^ 2 ≤
          (u0 + s • Pi.single (2 : Fin 4) 1) ⬝ᵥ (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1)) := by
        let w : Fin 4 → ℝ := u0 + s • Pi.single (2 : Fin 4) 1
        have h1 : c * ∑ i : Fin 4, w i ^ 2 ≤ w ⬝ᵥ (A *ᵥ w) := hcoerc w
        have h2 : s ^ 2 ≤ ∑ i : Fin 4, w i ^ 2 := by
          rw [Fin.sum_univ_four]
          have hw2 : w 2 = s := by dsimp [w]; rw [Pi.single_eq_same]; simp [u0]
          rw [hw2]
          nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 3)]
        nlinarith
      dsimp [F]
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    have hint_slice : IntegrableOn (fun s => g (e2 (s, y))) (Set.Ioi 0) MeasureTheory.volume := by
      let β : ℝ := |A 2 2|
      let γ : ℝ := |(A *ᵥ u0) 2|
      refine ((integrable_poly2_exp_neg_mul_sq (α := 0) (β := β) (γ := γ) hc).integrableOn).mono'
        ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        dsimp [g]
        have heq : ∀ s, (![(e2 (s, y)) 0, (e2 (s, y)) 1, (e2 (s, y)) 2, 0] : Fin 4 → ℝ) =
            u0 + s • Pi.single (2 : Fin 4) 1 := hline
        simp_rw [heq]
        have hw : Continuous (fun s : ℝ => (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) (1 : ℝ))) 2) := by
          have hlin : (fun s : ℝ => (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) (1 : ℝ))) 2) =
              fun s : ℝ => (A *ᵥ u0) 2 + A 2 2 * s := by
            ext s; simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
          rw [hlin]; fun_prop
        have hq : Continuous (fun s : ℝ => (u0 + s • (Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)) ⬝ᵥ
            (A *ᵥ (u0 + s • (Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)))) := by
          refine continuous_finsetSum Finset.univ fun i _ => ?_
          have hi : Continuous (fun s : ℝ => (u0 + s • (Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ)) i) := by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            fun_prop
          have hwi : Continuous (fun s : ℝ =>
              (A *ᵥ (u0 + s • (Pi.single (2 : Fin 4) (1 : ℝ) : Fin 4 → ℝ))) i) := by
            simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            fun_prop
          exact hi.fun_mul hwi
        simpa only [Function.comp_apply] using
          hw.fun_mul (Real.continuous_exp.comp hq.fun_neg)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        dsimp [g]
        rw [hline s]
        have hs0 : 0 ≤ s := hs.le
        have hw : |(A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1)) 2| ≤ 0 * s ^ 2 + β * s + γ := by
          have heq : (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1)) 2 = A 2 2 * s + (A *ᵥ u0) 2 := by
            simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
          rw [heq]
          calc
            |A 2 2 * s + (A *ᵥ u0) 2| ≤ |A 2 2 * s| + |(A *ᵥ u0) 2| := abs_add_le _ _
            _ = 0 * s ^ 2 + β * s + γ := by rw [abs_mul, abs_of_nonneg hs0]; dsimp [β, γ]; ring
        have hq_ge : c * s ^ 2 ≤
            (u0 + s • Pi.single (2 : Fin 4) 1) ⬝ᵥ (A *ᵥ (u0 + s • Pi.single (2 : Fin 4) 1)) := by
          let w : Fin 4 → ℝ := u0 + s • Pi.single (2 : Fin 4) 1
          have h1 : c * ∑ i : Fin 4, w i ^ 2 ≤ w ⬝ᵥ (A *ᵥ w) := hcoerc w
          have h2 : s ^ 2 ≤ ∑ i : Fin 4, w i ^ 2 := by
            rw [Fin.sum_univ_four]
            have hw2 : w 2 = s := by dsimp [w]; rw [Pi.single_eq_same]; simp [u0]
            rw [hw2]
            nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 3)]
          nlinarith
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul hw (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_slice htend]
    dsimp [F, u0]
    simp [zero_smul, add_zero]
  change ∫ y in orthant2, ∫ s in Set.Ioi (0 : ℝ), g (e2 (s, y)) = _
  rw [hstep2, integral_const_mul]
  congr 1
  let e1 : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ) := (MeasurableEquiv.finTwoArrow (α := ℝ)).symm
  have hmp1 : MeasurePreserving e1 MeasureTheory.volume MeasureTheory.volume :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  have hpre1 : e1 ⁻¹' orthant2 = Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    ext ⟨t, r⟩
    simp [e1, orthant2, Set.mem_prod, Set.mem_Ioi, Fin.forall_fin_two]
  let h : (Fin 2 → ℝ) → ℝ := fun y => Real.exp (-(![y 0, y 1, 0, 0] ⬝ᵥ (A *ᵥ ![y 0, y 1, 0, 0])))
  rw [← hmp1.setIntegral_preimage_emb e1.measurableEmbedding h orthant2, hpre1]
  have hint_2d : IntegrableOn (fun p : ℝ × ℝ => h (e1 p))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine Integrable.integrableOn ?_
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (integrable_exp_neg_mul_sq hc).mul_prod (integrable_exp_neg_mul_sq hc)
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun ⟨t, r⟩ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have heq : (fun p : ℝ × ℝ => h (e1 p)) =
          fun p : ℝ × ℝ => Real.exp (-(A 0 0 * p.1 ^ 2 + 2 * A 0 1 * p.1 * p.2 + A 1 1 * p.2 ^ 2)) := by
        ext ⟨t, r⟩
        have hsym : A 1 0 = A 0 1 := by
          have := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hA
          simpa using this
        dsimp [h, e1]
        congr 2
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four, hsym]
        ring
      rw [heq]; fun_prop
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 := hcoerc ![t, r, 0, 0]
      have h2 : ∑ i : Fin 4, (![t, r, 0, 0] : Fin 4 → ℝ) i ^ 2 = t ^ 2 + r ^ 2 := by
        simp [Fin.sum_univ_four]
      dsimp [h]
      have he1_tr : e1 (t, r) = ![t, r] := by
        ext i
        fin_cases i <;> rfl
      rw [he1_tr]
      have hv01 : ![![t, r] 0, ![t, r] 1, 0, 0] = ![t, r, 0, 0] := by
        ext i
        fin_cases i <;> rfl
      rw [hv01]
      rw [h2] at h1
      linarith
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
  rw [setIntegral_prod (fun p : ℝ × ℝ => h (e1 p)) hint_2d]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ =>
    setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  have hsym : A 1 0 = A 0 1 := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hA
    simpa using this
  dsimp [h, e1]
  congr 2
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four, hsym]
  ring

private theorem integral_Ioi_Ioi_exp_neg_quad {a b d c : ℝ} (hc : 0 < c)
    (hcoerc : ∀ t r : ℝ, c * (t ^ 2 + r ^ 2) ≤ a * t ^ 2 + 2 * b * t * r + d * r ^ 2)
    (ha : 0 < a) (hd : 0 < d) (hdet : b ^ 2 < a * d) :
    ∫ t in Set.Ioi (0 : ℝ), ∫ r in Set.Ioi (0 : ℝ),
        Real.exp (-(a * t ^ 2 + 2 * b * t * r + d * r ^ 2)) =
      (1 / 2 : ℝ) * (Real.arccos (b / Real.sqrt (a * d)) / Real.sqrt (a * d - b ^ 2)) := by
  have hpoly_ge : ∀ s : ℝ, c * (1 + s ^ 2) ≤ d * s ^ 2 + 2 * b * s + a := fun s => by
    have := hcoerc 1 s
    linarith
  have hpoly_pos : ∀ s : ℝ, 0 < d * s ^ 2 + 2 * b * s + a := fun s => by
    have h1 : 0 < c * (1 + s ^ 2) := mul_pos hc (by positivity)
    linarith [hpoly_ge s]
  have hint_s : IntegrableOn (fun s : ℝ => 1 / (d * s ^ 2 + 2 * b * s + a))
      (Set.Ioi 0) MeasureTheory.volume := by
    have hpsi0 := Sphere3.manuscriptPsi_quad_integrableOn (x := (0 : ℝ)) (by norm_num)
    refine (hpsi0.const_mul (1 / c)).mono' ?_ ?_
    · exact (continuous_const.div (by fun_prop) fun s => (hpoly_pos s).ne').aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hpoly_pos s))]
      have hs1 : 1 + s ^ 2 ≠ 0 := by positivity
      calc
        1 / (d * s ^ 2 + 2 * b * s + a) ≤ 1 / (c * (1 + s ^ 2)) :=
          one_div_le_one_div_of_le (mul_pos hc (by positivity)) (hpoly_ge s)
        _ = (1 / c) * (1 / (s ^ 2 + 2 * 0 * s + 1)) := by
            rw [show s ^ 2 + 2 * 0 * s + 1 = 1 + s ^ 2 by ring]
            field_simp [hc.ne', hs1]
  let μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let G : ℝ → ℝ := fun t => ∫ r in Set.Ioi (0 : ℝ),
    Real.exp (-(a * t ^ 2 + 2 * b * t * r + d * r ^ 2))
  let innerFun : ℝ → ℝ → ℝ := fun t s => t * Real.exp (-(d * s ^ 2 + 2 * b * s + a) * t ^ 2)
  have hF2d_int : Integrable (fun p : ℝ × ℝ => Real.exp (-(a * p.1 ^ 2 + 2 * b * p.1 * p.2 + d * p.2 ^ 2)))
      (μ.prod μ) := by
    rw [Measure.prod_restrict]
    refine Integrable.integrableOn ?_
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
      (integrable_exp_neg_mul_sq hc).mul_prod (integrable_exp_neg_mul_sq hc)
    refine hdom.mono' (by fun_prop) (Filter.Eventually.of_forall fun ⟨t, r⟩ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hcoerc t r])
  have hG_aem : AEStronglyMeasurable G μ := hF2d_int.integral_prod_left.aestronglyMeasurable
  have hG_nonneg : 0 ≤ᵐ[μ] G :=
    Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => (Real.exp_pos _).le
  have hsub : ∀ t ∈ Set.Ioi (0 : ℝ), G t = ∫ s, innerFun t s ∂μ := by
    intro t ht
    have hcomp := integral_comp_mul_left_Ioi
      (fun r => Real.exp (-(a * t ^ 2 + 2 * b * t * r + d * r ^ 2))) 0 ht
    rw [mul_zero] at hcomp
    have hmul := congrArg (t * ·) hcomp
    have ht_ne : t ≠ 0 := ht.ne'
    dsimp [G, innerFun]
    rw [← integral_const_mul] at hmul
    have heq : (fun s => t * Real.exp (-(a * t ^ 2 + 2 * b * t * (t * s) + d * (t * s) ^ 2))) =
        fun s => t * Real.exp (-(d * s ^ 2 + 2 * b * s + a) * t ^ 2) := by
      ext s
      congr 2
      ring
    rw [heq] at hmul
    simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht_ne, one_mul] at hmul
    exact hmul.symm
  have hinner_int_s : ∀ t ∈ Set.Ioi (0 : ℝ), Integrable (innerFun t) μ := by
    intro t ht
    have hct2 : 0 < c * t ^ 2 := mul_pos hc (sq_pos_of_pos ht)
    refine ((integrable_exp_neg_mul_sq hct2).const_mul t).integrableOn.mono' (by fun_prop) ?_
    refine Filter.Eventually.of_forall fun s => ?_
    dsimp [innerFun]
    rw [abs_mul, abs_of_pos ht, abs_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ht.le
    nlinarith [hpoly_ge s, sq_nonneg t]
  have hinner_int_t : ∀ s : ℝ, IntegrableOn (fun t => innerFun t s) (Set.Ioi 0) MeasureTheory.volume := by
    intro s
    have hAs := hpoly_pos s
    let A := d * s ^ 2 + 2 * b * s + a
    have hA_pos : 0 < A := hAs
    refine ((integrable_exp_neg_mul_sq (half_pos hA_pos)).const_mul (max 1 (2 / A))).integrableOn.mono'
      (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp [innerFun]
    rw [abs_mul, abs_of_pos ht, abs_of_nonneg (Real.exp_pos _).le]
    by_cases ht1 : t ≤ 1
    · calc
        t * Real.exp (-A * t ^ 2) ≤ 1 * Real.exp (-A * t ^ 2) :=
          mul_le_mul_of_nonneg_right ht1 (Real.exp_pos _).le
        _ ≤ 1 * Real.exp (-(A / 2) * t ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t])) zero_le_one
        _ ≤ max 1 (2 / A) * Real.exp (-(A / 2) * t ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have ht_gt : 1 ≤ t := le_of_not_ge ht1
      have ht_sq : t ≤ t ^ 2 := by nlinarith
      have hlin : (A / 2) * t ^ 2 ≤ Real.exp ((A / 2) * t ^ 2) :=
        le_trans (by linarith [mul_nonneg (half_pos hA_pos).le (sq_nonneg t)])
          (Real.add_one_le_exp ((A / 2) * t ^ 2))
      have h2 : t ^ 2 * Real.exp (-A * t ^ 2) ≤ (2 / A) * Real.exp (-(A / 2) * t ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-A * t ^ 2)).le
        have h2' : (A / 2) * (t ^ 2 * Real.exp (-A * t ^ 2)) ≤ Real.exp (-(A / 2) * t ^ 2) := by
          calc
            (A / 2) * (t ^ 2 * Real.exp (-A * t ^ 2)) = ((A / 2) * t ^ 2) * Real.exp (-A * t ^ 2) := by ring
            _ ≤ Real.exp ((A / 2) * t ^ 2) * Real.exp (-A * t ^ 2) := hmul
            _ = Real.exp (-(A / 2) * t ^ 2) := by rw [← Real.exp_add]; ring_nf
        have hpos : 0 < A / 2 := half_pos hA_pos
        have := mul_le_mul_of_nonneg_left h2' (inv_nonneg.mpr hpos.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul, show (A / 2)⁻¹ = 2 / A by ring] at this
      calc
        t * Real.exp (-A * t ^ 2) ≤ t ^ 2 * Real.exp (-A * t ^ 2) :=
          mul_le_mul_of_nonneg_right ht_sq (Real.exp_pos _).le
        _ ≤ (2 / A) * Real.exp (-(A / 2) * t ^ 2) := h2
        _ ≤ max 1 (2 / A) * Real.exp (-(A / 2) * t ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hinner_val : ∀ s : ℝ, ∫ t, innerFun t s ∂μ = 1 / (2 * (d * s ^ 2 + 2 * b * s + a)) := by
    intro s
    let A := d * s ^ 2 + 2 * b * s + a
    have hA_pos : 0 < A := hpoly_pos s
    let F : ℝ → ℝ := fun t => -(1 / (2 * A)) * Real.exp (-A * t ^ 2)
    have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt F (innerFun t s) t := by
      intro t _
      have hexp : HasDerivAt (fun r : ℝ => Real.exp (-A * r ^ 2)) (-2 * A * t * Real.exp (-A * t ^ 2)) t := by
        have hp : HasDerivAt (fun r : ℝ => -A * r ^ 2) (-2 * A * t) t := by
          simpa [pow_one, mul_comm, mul_assoc] using ((hasDerivAt_id t).pow 2).const_mul (-A)
        simpa [mul_comm] using hp.exp
      refine (hexp.const_mul (-(1 / (2 * A)))).congr_deriv ?_
      dsimp [innerFun]
      field_simp [hA_pos.ne']
      dsimp [A]
      ring
    have htend : Tendsto F atTop (nhds 0) := by
      simpa [F, mul_zero] using (tendsto_exp_neg_mul_sq hA_pos).const_mul (-(1 / (2 * A)))
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hinner_int_t s) htend]
    dsimp [F, A]
    simp [mul_zero, zero_pow]
  have htonelli :
      (∫ t, G t ∂μ) = (1 / 2 : ℝ) * ∫ s in Set.Ioi (0 : ℝ), 1 / (d * s ^ 2 + 2 * b * s + a) := by
    have h1 : ∫ t, G t ∂μ = (∫⁻ t, ENNReal.ofReal (G t) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae hG_nonneg hG_aem
    have h2 : ∫⁻ t, ENNReal.ofReal (G t) ∂μ = ∫⁻ t, ∫⁻ s, ENNReal.ofReal (innerFun t s) ∂μ ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hsub t ht]
      refine ofReal_integral_eq_lintegral_ofReal (hinner_int_s t ht) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
      exact mul_nonneg ht.le (Real.exp_pos _).le
    have hswap : ∫⁻ t, ∫⁻ s, ENNReal.ofReal (innerFun t s) ∂μ ∂μ =
        ∫⁻ s, ∫⁻ t, ENNReal.ofReal (innerFun t s) ∂μ ∂μ := by
      refine lintegral_lintegral_swap ?_
      refine Continuous.aemeasurable ?_
      exact ENNReal.continuous_ofReal.comp
        (continuous_fst.mul (Real.continuous_exp.comp
          (((continuous_const.mul (continuous_snd.pow 2)).add
            (continuous_const.mul continuous_snd) |>.add continuous_const).neg.mul
            (continuous_fst.pow 2))))
    have h3 : ∫⁻ s, ∫⁻ t, ENNReal.ofReal (innerFun t s) ∂μ ∂μ =
        ∫⁻ s, ENNReal.ofReal (1 / (2 * (d * s ^ 2 + 2 * b * s + a))) ∂μ := by
      refine lintegral_congr fun s => ?_
      rw [← hinner_val s]
      refine (ofReal_integral_eq_lintegral_ofReal (hinner_int_t s) ?_).symm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg ht.le (Real.exp_pos _).le
    have hint_half : Integrable (fun s : ℝ => 1 / (2 * (d * s ^ 2 + 2 * b * s + a))) μ := by
      have : (fun s : ℝ => 1 / (2 * (d * s ^ 2 + 2 * b * s + a))) =
          fun s => (1 / 2 : ℝ) * (1 / (d * s ^ 2 + 2 * b * s + a)) := by
        ext s
        have hs0 : d * s ^ 2 + 2 * b * s + a ≠ 0 := (hpoly_pos s).ne'
        field_simp [hs0]
      rw [this]
      exact hint_s.const_mul (1 / 2)
    have h4 : ∫⁻ s, ENNReal.ofReal (1 / (2 * (d * s ^ 2 + 2 * b * s + a))) ∂μ =
        ENNReal.ofReal (∫ s, 1 / (2 * (d * s ^ 2 + 2 * b * s + a)) ∂μ) := by
      refine (ofReal_integral_eq_lintegral_ofReal hint_half ?_).symm
      exact Filter.Eventually.of_forall fun s =>
        one_div_nonneg.mpr (mul_nonneg zero_le_two (hpoly_pos s).le)
    rw [h1, h2, hswap, h3, h4, ENNReal.toReal_ofReal (integral_nonneg fun s =>
      one_div_nonneg.mpr (mul_nonneg zero_le_two (hpoly_pos s).le))]
    have heq : (fun s : ℝ => 1 / (2 * (d * s ^ 2 + 2 * b * s + a))) =
        fun s => (1 / 2 : ℝ) * (1 / (d * s ^ 2 + 2 * b * s + a)) := by
      ext s
      have hs0 : d * s ^ 2 + 2 * b * s + a ≠ 0 := (hpoly_pos s).ne'
      field_simp [hs0]
    change ∫ s in Set.Ioi (0 : ℝ), 1 / (2 * (d * s ^ 2 + 2 * b * s + a)) = _
    rw [heq, integral_const_mul]
  change ∫ t, G t ∂μ = _
  rw [htonelli]
  congr 1
  let ρ : ℝ := b / Real.sqrt (a * d)
  have had_pos : 0 < a * d := mul_pos ha hd
  have hsqrt_ad : 0 < Real.sqrt (a * d) := Real.sqrt_pos.mpr had_pos
  have hρ_mem : ρ ∈ Set.Ioo (-1 : ℝ) 1 := by
    have hsq : ρ ^ 2 < 1 := by
      dsimp [ρ]
      rw [div_pow, Real.sq_sqrt had_pos.le, div_lt_one had_pos]
      exact hdet
    rw [Set.mem_Ioo]
    constructor <;> · by_contra hle; push Not at hle; nlinarith [sq_nonneg ρ]
  let κ : ℝ := Real.sqrt (a / d)
  have hκ_pos : 0 < κ := Real.sqrt_pos.mpr (div_pos ha hd)
  have hscale := integral_comp_mul_left_Ioi (fun s => 1 / (d * s ^ 2 + 2 * b * s + a)) 0 hκ_pos
  rw [mul_zero] at hscale
  have hden : ∀ u : ℝ, d * (κ * u) ^ 2 + 2 * b * (κ * u) + a = a * (u ^ 2 + 2 * ρ * u + 1) := by
    intro u
    have hκ_sq : κ ^ 2 = a / d := Real.sq_sqrt (div_pos ha hd).le
    have hκ_mul : b * κ = a * ρ := by
      dsimp [κ, ρ]
      rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
      field_simp [ha.ne', hd.ne', Real.sqrt_ne_zero'.mpr ha, Real.sqrt_ne_zero'.mpr hd]
      rw [Real.sq_sqrt ha.le]
    calc
      d * (κ * u) ^ 2 + 2 * b * (κ * u) + a = d * κ ^ 2 * u ^ 2 + 2 * (b * κ) * u + a := by ring
      _ = d * (a / d) * u ^ 2 + 2 * (a * ρ) * u + a := by rw [hκ_sq, hκ_mul]
      _ = a * (u ^ 2 + 2 * ρ * u + 1) := by field_simp [hd.ne']
  have heq_u : (fun u : ℝ => 1 / (d * (κ * u) ^ 2 + 2 * b * (κ * u) + a)) =
      fun u : ℝ => a⁻¹ * (1 / (u ^ 2 + 2 * ρ * u + 1)) := by
    ext u
    rw [hden u]
    field_simp [ha.ne']
  rw [heq_u, integral_const_mul, ← Sphere3.manuscriptPsi_eq_quad_integral hρ_mem] at hscale
  have hmul_κ := congrArg (κ * ·) hscale
  simp only [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hκ_pos.ne', one_mul] at hmul_κ
  rw [← hmul_κ]
  have hκ_div_a : κ / a = (Real.sqrt (a * d))⁻¹ := by
    dsimp [κ]
    rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
    field_simp [ha.ne', Real.sqrt_ne_zero'.mpr ha, Real.sqrt_ne_zero'.mpr hd]
    rw [Real.sq_sqrt ha.le]
  have hsqrt_rel : Real.sqrt (a * d) * Real.sqrt (1 - ρ ^ 2) = Real.sqrt (a * d - b ^ 2) := by
    rw [← Real.sqrt_mul had_pos.le]
    congr 1
    dsimp [ρ]
    rw [div_pow, Real.sq_sqrt had_pos.le]
    field_simp [had_pos.ne']
  rw [Sphere3.manuscriptPsi]
  calc
    κ * a⁻¹ * (Real.arccos ρ / Real.sqrt (1 - ρ ^ 2))
        = (κ / a) * (Real.arccos ρ / Real.sqrt (1 - ρ ^ 2)) := by ring
    _ = (Real.sqrt (a * d))⁻¹ * (Real.arccos ρ / Real.sqrt (1 - ρ ^ 2)) := by rw [hκ_div_a]
    _ = Real.arccos ρ / (Real.sqrt (a * d) * Real.sqrt (1 - ρ ^ 2)) := by ring
    _ = Real.arccos (b / Real.sqrt (a * d)) / Real.sqrt (a * d - b ^ 2) := by rw [hsqrt_rel]

theorem integral_gaussIntegrand_schlafli_coord {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (k : Fin 6) :
    (Real.sqrt (symUnitMat x).det)⁻¹ *
        ((∫ z in orthant4, gaussIntegrandFDeriv x z (Pi.single k 1)) -
          symUnitInv x (pairIdx k).1 (pairIdx k).2 * gaussInt x) =
      ((1 / 4 : ℝ) *
          Real.arccos (symUnitAdj x (oppIdx k).1 (oppIdx k).2 /
            Real.sqrt (symUnitAdj x (oppIdx k).1 (oppIdx k).1 *
              symUnitAdj x (oppIdx k).2 (oppIdx k).2))) /
        Real.sqrt (1 - x k ^ 2) := by
  let σ : Equiv.Perm (Fin 4) := pairOppEquiv k
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.submatrix (symUnitInv x) σ σ
  have hA_symm : Aᵀ = A := by
    ext r s
    have hsym := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M (σ s) (σ r))
      (symUnitInv_transpose hx)
    simpa [A] using hsym.symm
  obtain ⟨_, _, _, c, hc, hcoerc_x⟩ := gaussQuadForm_local_coercive hx
  have hcoerc_A : ∀ u : Fin 4 → ℝ, c * (∑ m : Fin 4, u m ^ 2) ≤ u ⬝ᵥ (A *ᵥ u) := by
    intro u
    let z : Fin 4 → ℝ := u ∘ σ.symm
    have hsum_eq : ∑ m : Fin 4, u m ^ 2 = ∑ m : Fin 4, z m ^ 2 :=
      Fintype.sum_equiv σ (fun m => u m ^ 2) (fun m => z m ^ 2) (fun m => by simp [z])
    have hq_eq : z ⬝ᵥ (symUnitInv x *ᵥ z) = u ⬝ᵥ (A *ᵥ u) := by
      simp only [dotProduct, Matrix.mulVec, z, A, Matrix.submatrix_apply]
      calc
        ∑ a : Fin 4, u (σ.symm a) * ∑ b : Fin 4, symUnitInv x a b * u (σ.symm b)
            = ∑ m : Fin 4, u (σ.symm (σ m)) * ∑ b : Fin 4, symUnitInv x (σ m) b * u (σ.symm b) :=
              (Fintype.sum_equiv σ _ _ (fun _ => rfl)).symm
        _ = ∑ m : Fin 4, u m * ∑ n : Fin 4, symUnitInv x (σ m) (σ n) * u n := by
              refine Finset.sum_congr rfl fun m _ => ?_
              simp only [Equiv.symm_apply_apply]
              congr 1
              exact (Fintype.sum_equiv σ _ _ (fun _ => by simp)).symm
    rw [hsum_eq, ← hq_eq]
    exact hcoerc_x x (Metric.mem_closedBall_self (le_of_lt (by positivity))) z
  have hint_comb :
      (∫ z in orthant4, gaussIntegrandFDeriv x z (Pi.single k 1)) -
          symUnitInv x (pairIdx k).1 (pairIdx k).2 * gaussInt x =
        ∫ z in orthant4,
          (2 * (symUnitInv x *ᵥ z) (pairIdx k).1 * (symUnitInv x *ᵥ z) (pairIdx k).2 -
            symUnitInv x (pairIdx k).1 (pairIdx k).2) * gaussIntegrand x z := by
    have h1 := integrableOn_gaussIntegrandFDeriv_single hx k
    have h2 := (integrableOn_gaussIntegrand hx).const_mul (symUnitInv x (pairIdx k).1 (pairIdx k).2)
    change _ - symUnitInv x (pairIdx k).1 (pairIdx k).2 * ∫ z in orthant4, gaussIntegrand x z = _
    rw [← integral_const_mul, ← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_orthant4 fun z _ => ?_
    rw [gaussIntegrandFDeriv_single hx z k]
    ring
  rw [hint_comb]
  let perm : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) := MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl ℝ)
  have hmp_perm : MeasurePreserving perm MeasureTheory.volume MeasureTheory.volume :=
    volume_preserving_arrowCongr' σ (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have hpre_perm : perm ⁻¹' orthant4 = orthant4 := by
    ext u
    simp only [Set.mem_preimage, orthant4, Set.mem_univ_pi, Set.mem_Ioi]
    constructor
    · intro h m
      have hm := h (σ m)
      change 0 < u (σ.symm (σ m)) at hm
      simpa using hm
    · intro h m
      change 0 < u (σ.symm m)
      exact h (σ.symm m)
  let origF : (Fin 4 → ℝ) → ℝ := fun z =>
    (2 * (symUnitInv x *ᵥ z) (pairIdx k).1 * (symUnitInv x *ᵥ z) (pairIdx k).2 -
      symUnitInv x (pairIdx k).1 (pairIdx k).2) * gaussIntegrand x z
  have hperm_int : ∫ z in orthant4, origF z =
      ∫ u in orthant4, (2 * (A *ᵥ u) 2 * (A *ᵥ u) 3 - A 2 3) * Real.exp (-(u ⬝ᵥ (A *ᵥ u))) := by
    rw [← hmp_perm.setIntegral_preimage_emb perm.measurableEmbedding origF orthant4, hpre_perm]
    refine setIntegral_congr_fun measurableSet_orthant4 fun u _ => ?_
    have hz_def : ∀ m : Fin 4, perm u m = u (σ.symm m) := fun _ => rfl
    have hw_eq : ∀ r : Fin 4, (symUnitInv x *ᵥ perm u) (σ r) = (A *ᵥ u) r := fun r => by
      simp only [Matrix.mulVec, dotProduct, A, Matrix.submatrix_apply, hz_def]
      exact (Fintype.sum_equiv σ _ _ (fun s => by simp)).symm
    have hq_eq : gaussQuadForm x (perm u) = u ⬝ᵥ (A *ᵥ u) := by
      simp only [gaussQuadForm, dotProduct, Matrix.mulVec, hz_def, A, Matrix.submatrix_apply]
      calc
        ∑ a : Fin 4, u (σ.symm a) * ∑ b : Fin 4, symUnitInv x a b * u (σ.symm b)
            = ∑ r : Fin 4, u r * ∑ b : Fin 4, symUnitInv x (σ r) b * u (σ.symm b) :=
              (Fintype.sum_equiv σ _ _ (fun _ => by simp)).symm
        _ = ∑ r : Fin 4, u r * ∑ s : Fin 4, symUnitInv x (σ r) (σ s) * u s := by
              refine Finset.sum_congr rfl fun r _ => ?_
              congr 1
              exact (Fintype.sum_equiv σ _ _ (fun _ => by simp)).symm
    have hw2 := hw_eq 2
    have hw3 := hw_eq 3
    rw [pairOppEquiv_two k] at hw2
    rw [pairOppEquiv_three k] at hw3
    have hA23 : A 2 3 = symUnitInv x (pairIdx k).1 (pairIdx k).2 := by
      dsimp [A, σ]
      rw [pairOppEquiv_two, pairOppEquiv_three]
    dsimp [origF, gaussIntegrand]
    rw [hw2, hw3, hA23, hq_eq]
  rw [hperm_int, orthant4_ibp_q A hA_symm hc hcoerc_A, orthant3_ibp_p A hA_symm hc hcoerc_A]
  have hcoerc_2d : ∀ t r : ℝ, c * (t ^ 2 + r ^ 2) ≤ A 0 0 * t ^ 2 + 2 * A 0 1 * t * r + A 1 1 * r ^ 2 := by
    intro t r
    have h1 := hcoerc_A ![t, r, 0, 0]
    have h2 : ∑ m : Fin 4, (![t, r, 0, 0] : Fin 4 → ℝ) m ^ 2 = t ^ 2 + r ^ 2 := by
      simp [Fin.sum_univ_four]
    have hsym : A 1 0 = A 0 1 := by
      have := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hA_symm
      simpa using this
    have h3 : ![t, r, 0, 0] ⬝ᵥ (A *ᵥ ![t, r, 0, 0]) = A 0 0 * t ^ 2 + 2 * A 0 1 * t * r + A 1 1 * r ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four, hsym]; ring
    rw [h2, h3] at h1
    exact h1
  have ha_pos : 0 < A 0 0 := by
    dsimp [A, σ]
    rw [pairOppEquiv_zero]
    exact gramOpen_inv_diag_pos hx (oppIdx k).1
  have hd_pos : 0 < A 1 1 := by
    dsimp [A, σ]
    rw [pairOppEquiv_one]
    exact gramOpen_inv_diag_pos hx (oppIdx k).2
  have hdet_pos : 0 < (symUnitMat x).det := gramOpen_det_pos hx
  have hjac_eq := symUnitAdj_jacobi x k
  have hjac_pos := gramOpen_jacobi_pos hx k
  have hA00 : A 0 0 = (symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).1 (oppIdx k).1 := by
    dsimp [A, σ, symUnitInv]
    rw [pairOppEquiv_zero]
  have hA11 : A 1 1 = (symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).2 (oppIdx k).2 := by
    dsimp [A, σ, symUnitInv]
    rw [pairOppEquiv_one]
  have hA01 : A 0 1 = (symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).1 (oppIdx k).2 := by
    dsimp [A, σ, symUnitInv]
    rw [pairOppEquiv_zero, pairOppEquiv_one]
  have hdet_2d : A 0 1 ^ 2 < A 0 0 * A 1 1 := by
    rw [hA00, hA11, hA01]
    have hpos_j : 0 < symUnitAdj x (oppIdx k).1 (oppIdx k).1 * symUnitAdj x (oppIdx k).2 (oppIdx k).2 -
        symUnitAdj x (oppIdx k).1 (oppIdx k).2 ^ 2 := by
      simpa using hjac_pos
    have hinv_pos : 0 < ((symUnitMat x).det⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr hdet_pos)
    nlinarith
  rw [integral_Ioi_Ioi_exp_neg_quad hc hcoerc_2d ha_pos hd_pos hdet_2d]
  have hdet_inv_pos : 0 < (symUnitMat x).det⁻¹ := inv_pos.mpr hdet_pos
  have hadj_i_pos : 0 < symUnitAdj x (oppIdx k).1 (oppIdx k).1 := gramOpen_adj_diag_pos hx (oppIdx k).1
  have hadj_j_pos : 0 < symUnitAdj x (oppIdx k).2 (oppIdx k).2 := gramOpen_adj_diag_pos hx (oppIdx k).2
  have hratio : A 0 1 / Real.sqrt (A 0 0 * A 1 1) =
      symUnitAdj x (oppIdx k).1 (oppIdx k).2 /
        Real.sqrt (symUnitAdj x (oppIdx k).1 (oppIdx k).1 * symUnitAdj x (oppIdx k).2 (oppIdx k).2) := by
    rw [hA00, hA11, hA01]
    have hprod : ((symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).1 (oppIdx k).1) *
        ((symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).2 (oppIdx k).2) =
        ((symUnitMat x).det⁻¹) ^ 2 *
          (symUnitAdj x (oppIdx k).1 (oppIdx k).1 * symUnitAdj x (oppIdx k).2 (oppIdx k).2) := by ring
    rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hdet_inv_pos.le]
    field_simp [hdet_inv_pos.ne']
  have hden_eq : Real.sqrt (A 0 0 * A 1 1 - A 0 1 ^ 2) =
      (Real.sqrt (symUnitMat x).det)⁻¹ * Real.sqrt (1 - x k ^ 2) := by
    rw [hA00, hA11, hA01]
    have hsub : ((symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).1 (oppIdx k).1) *
          ((symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).2 (oppIdx k).2) -
          ((symUnitMat x).det⁻¹ * symUnitAdj x (oppIdx k).1 (oppIdx k).2) ^ 2 =
        ((symUnitMat x).det⁻¹) ^ 2 *
          (symUnitAdj x (oppIdx k).1 (oppIdx k).1 * symUnitAdj x (oppIdx k).2 (oppIdx k).2 -
            symUnitAdj x (oppIdx k).1 (oppIdx k).2 ^ 2) := by ring
    rw [hsub]
    have hjac_k : symUnitAdj x (oppIdx k).1 (oppIdx k).1 * symUnitAdj x (oppIdx k).2 (oppIdx k).2 -
        symUnitAdj x (oppIdx k).1 (oppIdx k).2 ^ 2 = (symUnitMat x).det * (1 - x k ^ 2) := by
      simpa [symUnitMat_pairIdx] using hjac_eq
    rw [hjac_k, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hdet_inv_pos.le,
      Real.sqrt_mul hdet_pos.le]
    have hsq_pos : 0 < Real.sqrt (symUnitMat x).det := Real.sqrt_pos.mpr hdet_pos
    have hdet_eq : (symUnitMat x).det = Real.sqrt (symUnitMat x).det * Real.sqrt (symUnitMat x).det :=
      (Real.mul_self_sqrt hdet_pos.le).symm
    conv_lhs => rw [hdet_eq]
    field_simp [hdet_pos.ne', hsq_pos.ne']
    rw [Real.sqrt_sq hsq_pos.le]
  have hsqrt_det_ne : Real.sqrt (symUnitMat x).det ≠ 0 := (Real.sqrt_pos.mpr hdet_pos).ne'
  have hsqrt_1x_ne : Real.sqrt (1 - x k ^ 2) ≠ 0 := by
    have habs : -1 < x k ∧ x k < 1 := abs_lt.mp (gramOpen_offdiag_abs_lt_one hx k)
    have hlt : x k ^ 2 < 1 := by nlinarith
    exact (Real.sqrt_pos.mpr (by linarith)).ne'
  rw [hratio, hden_eq]
  field_simp [hsqrt_det_ne, hsqrt_1x_ne]
  ring

/-! ### Fréchet derivative, continuity, and strict differentiability of `gaussVolGram` -/

theorem gaussVolFDeriv_coord (x : Fin 6 → ℝ) (k : Fin 6) :
    gaussVolFDeriv x (Pi.single k 1) =
      ((1 / 4 : ℝ) *
          Real.arccos (symUnitAdj x (oppIdx k).1 (oppIdx k).2 /
            Real.sqrt (symUnitAdj x (oppIdx k).1 (oppIdx k).1 *
              symUnitAdj x (oppIdx k).2 (oppIdx k).2))) /
        Real.sqrt (1 - x k ^ 2) := by
  simp only [gaussVolFDeriv, sum_apply, smul_apply, smul_eq_mul, coordProj6,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single k]
  · simp [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

theorem hasFDerivAt_gaussVolGram {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    HasFDerivAt gaussVolGram (gaussVolFDeriv x) x := by
  let detSqrtInv : (Fin 6 → ℝ) → ℝ := fun y => (Real.sqrt (symUnitMat y).det)⁻¹
  have hcont_det : ContDiffAt ℝ (⊤ : ℕ∞) detSqrtInv x :=
    symUnitSqrtDet_inv_contDiffOn.contDiffAt (isOpen_gramOpen.mem_nhds hx)
  have hdiff_det : DifferentiableAt ℝ detSqrtInv x := hcont_det.differentiableAt (by simp)
  have hfderiv_det : HasFDerivAt detSqrtInv (fderiv ℝ detSqrtInv x) x := hdiff_det.hasFDerivAt
  have hfderiv_int : HasFDerivAt gaussInt (∫ z in orthant4, gaussIntegrandFDeriv x z) x :=
    hasFDerivAt_gaussInt hx
  have hprod :
      HasFDerivAt gaussVolGram
        (detSqrtInv x • (∫ z in orthant4, gaussIntegrandFDeriv x z) +
          gaussInt x • fderiv ℝ detSqrtInv x) x :=
    hfderiv_det.fun_mul hfderiv_int
  have heq_clm :
      detSqrtInv x • (∫ z in orthant4, gaussIntegrandFDeriv x z) +
          gaussInt x • fderiv ℝ detSqrtInv x =
        gaussVolFDeriv x := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hv_basis : v = ∑ k : Fin 6, v k • Pi.single k 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv_basis, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_smul, smul_eq_mul]
    congr 1
    have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single k 1) (Pi.single k 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k 1)).const_add x
    have hdet_at : HasFDerivAt detSqrtInv (fderiv ℝ detSqrtInv x) (x + (0 : ℝ) • Pi.single k 1) := by
      rw [zero_smul, add_zero]
      exact hfderiv_det
    have hdet_chain : HasDerivAt (fun t : ℝ => detSqrtInv (x + t • Pi.single k 1))
        ((fderiv ℝ detSqrtInv x) (Pi.single k 1)) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := detSqrtInv) (f := fun t : ℝ => x + t • Pi.single k 1)
        (0 : ℝ) hdet_at hline
    have hdet_k : (fderiv ℝ detSqrtInv x) (Pi.single k 1) =
        -detSqrtInv x * symUnitInv x (pairIdx k).1 (pairIdx k).2 :=
      hdet_chain.unique (symUnitMat_det_deriv_zero_apply hx k)
    simp only [add_apply, smul_apply, smul_eq_mul, hdet_k,
      integral_gaussIntegrandFDeriv_single hx k, gaussVolFDeriv_coord]
    have hrhs := integral_gaussIntegrand_schlafli_coord hx k
    dsimp [detSqrtInv] at hrhs ⊢
    linarith [hrhs]
  rwa [heq_clm] at hprod

theorem continuousOn_gaussVolFDeriv : ContinuousOn gaussVolFDeriv gramOpen := by
  refine continuousOn_finsetSum Finset.univ fun k _ => ?_
  have hcoeff : ContinuousOn (fun x : Fin 6 → ℝ =>
      ((1 / 4 : ℝ) *
          Real.arccos (symUnitAdj x (oppIdx k).1 (oppIdx k).2 /
            Real.sqrt (symUnitAdj x (oppIdx k).1 (oppIdx k).1 *
              symUnitAdj x (oppIdx k).2 (oppIdx k).2))) /
        Real.sqrt (1 - x k ^ 2)) gramOpen := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine continuousOn_const.mul (Real.continuous_arccos.comp_continuousOn ?_)
      refine ContinuousOn.div (symUnitAdj_entry_contDiffOn _ _).continuousOn ?_ ?_
      · refine Real.continuous_sqrt.comp_continuousOn ?_
        exact (symUnitAdj_entry_contDiffOn _ _).continuousOn.mul
          (symUnitAdj_entry_contDiffOn _ _).continuousOn
      · intro x hx
        exact (Real.sqrt_pos.mpr (mul_pos (gramOpen_adj_diag_pos hx (oppIdx k).1)
          (gramOpen_adj_diag_pos hx (oppIdx k).2))).ne'
    · refine Real.continuous_sqrt.comp_continuousOn ?_
      exact (continuousOn_const : ContinuousOn (fun _ : Fin 6 → ℝ => (1 : ℝ)) gramOpen).sub
        (((continuous_apply k : Continuous fun y : Fin 6 → ℝ => y k).pow 2).continuousOn)
    · intro x hx
      have habs : -1 < x k ∧ x k < 1 := abs_lt.mp (gramOpen_offdiag_abs_lt_one hx k)
      have hlt : x k ^ 2 < 1 := by nlinarith
      exact (Real.sqrt_pos.mpr (by linarith)).ne'
  exact hcoeff.smul (continuousOn_const : ContinuousOn (fun _ : Fin 6 → ℝ => coordProj6 k) gramOpen)

theorem hasStrictFDerivAt_gaussVolGram {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    HasStrictFDerivAt gaussVolGram (gaussVolFDeriv x) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Filter.Eventually.mono (isOpen_gramOpen.mem_nhds hx) fun _ hy => hasFDerivAt_gaussVolGram hy)
    (continuousOn_gaussVolFDeriv.continuousAt (isOpen_gramOpen.mem_nhds hx))

end SphericalTetrahedron

