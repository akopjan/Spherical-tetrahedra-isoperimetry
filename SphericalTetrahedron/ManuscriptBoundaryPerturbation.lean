module

public import SphericalTetrahedron.ManuscriptMeasureBridge
public import SphericalTetrahedron.ManuscriptGramChart
public import SphericalTetrahedron.ManuscriptAreaGradient
public import SphericalTetrahedron.ManuscriptGaussianSchlafli
public import Sphere3.ManuscriptBoundaryGram
public import Sphere3.ManuscriptBoundaryAreaAlgebra
public import Sphere3.GirardAlgebra

@[expose] public section

/-!
# Boundary Elimination and Square-Suspension Perturbation

This file develops:
1. Measure tools on `S³ ⊂ E4` (`toSphere_slab_bound`, `toSphere_real_lune4`,
   `toSphere_real_triSusp4`, and `measure_two_suspension_arc`).
2. The 2D spherical `≤ 4`-gon isoperimetric inequality via Euler/L'Huilier excess and
   kite symmetrization.
3. The explicit 2-parameter family of square-suspension spherical tetrahedra `T(a, d)` and the
   area-preserving `d = s² > 0` perturbation with strictly larger volume than the boundary limit.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace SphericalTetrahedron

/-! ### Part 1: Measure Bounds, 4D Lunes, and Suspensions on `S³` -/

lemma measureReal_union_inter_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {A B : Set α} (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : μ (A ∩ B) = 0) : μ.real (A ∪ B) = μ.real A + μ.real B := by
  have h := measure_union_add_inter A hB (μ := μ)
  have hreal := congrArg ENNReal.toReal h
  rw [hAB, ENNReal.toReal_add (measure_ne_top μ _) (by simp),
    ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B)] at hreal
  simpa [MeasureTheory.measureReal_def] using hreal

lemma measureReal_toSphere_preimage_oGroup {n : ℕ} (g : OGroup n)
    {S : Set ↑(Metric.sphere (0 : E n) 1)} (hS : MeasurableSet S) :
    MeasureTheory.volume.toSphere.real (⇑(orthoSphereAct g) ⁻¹' S) =
      MeasureTheory.volume.toSphere.real S := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
  have hm := Measure.map_apply (μ := MeasureTheory.volume.toSphere)
    (orthoSphereAct g).continuous.measurable hS
  rw [toSphere_oGroup_invariant n g] at hm
  rw [hm]

/-- Orthogonal matrix in `OGroup 4` from an orthonormal 4-frame (columns `b 0, b 1, b 2, b 3`). -/
def orthoOfOrthonormal {b : Fin 4 → E4} (hb : Orthonormal ℝ b) : OGroup 4 := by
  refine ⟨Matrix.of (fun i j : Fin 4 => b j i), ?_⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  have hAtA :
      (Matrix.of (fun i j : Fin 4 => b j i)).transpose * Matrix.of (fun i j : Fin 4 => b j i) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    have hinner : ∑ k : Fin 4, b i k * b j k = inner ℝ (b j) (b i) := by
      simp [PiLp.inner_apply, mul_comm]
    rw [hinner, orthonormal_iff_ite.mp hb j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, eq_comm]
  exact mul_eq_one_comm.mp hAtA

lemma mulVecE_orthoOfOrthonormal_basis {b : Fin 4 → E4} (hb : Orthonormal ℝ b) (j : Fin 4) :
    mulVecE (orthoOfOrthonormal hb : Matrix (Fin 4) (Fin 4) ℝ)
      (WithLp.toLp 2 (Pi.single j (1 : ℝ))) = b j := by
  ext i
  simp [orthoOfOrthonormal, mulVecE_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma mulVecE_orthoOfOrthonormal_inv {b : Fin 4 → E4} (hb : Orthonormal ℝ b) (j : Fin 4) :
    mulVecE ((orthoOfOrthonormal hb)⁻¹ : OGroup 4) (b j) =
      WithLp.toLp 2 (Pi.single j (1 : ℝ)) := by
  have hmul :
      mulVecE ((orthoOfOrthonormal hb)⁻¹ : OGroup 4)
          (mulVecE (orthoOfOrthonormal hb : OGroup 4) (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) =
        WithLp.toLp 2 (Pi.single j (1 : ℝ)) := by
    rw [← ortho_mulVecE_mul, inv_mul_cancel, ortho_mulVecE_one]
  rw [mulVecE_orthoOfOrthonormal_basis hb j] at hmul
  exact hmul

/-- A subspace of `E4` of dimension `< 4` admits an orthogonal unit vector. -/
lemma exists_unit_orthogonal_of_finrank_lt {S : Submodule ℝ E4}
    (hS : Module.finrank ℝ S < 4) :
    ∃ w : E4, ‖w‖ = 1 ∧ w ∈ Sᗮ := by
  have hadd : Module.finrank ℝ S + Module.finrank ℝ Sᗮ = Module.finrank ℝ E4 :=
    S.finrank_add_finrank_orthogonal
  have hfin : Module.finrank ℝ E4 = 4 := by simp
  have horth_pos : 0 < Module.finrank ℝ Sᗮ := by omega
  have horth_ne : Sᗮ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at horth_pos
    exact Nat.lt_irrefl 0 horth_pos
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth_ne
  refine ⟨‖x‖⁻¹ • x, ?_, Sᗮ.smul_mem _ hxmem⟩
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hxne)]

/-- Extend an orthonormal pair `(v₀, v₁)` in `E4` to an orthonormal 4-frame `(v₀, v₁, v₂, v₃)`. -/
lemma exists_orthonormal_extension_pair {v₀ v₁ : E4} (h0 : ‖v₀‖ = 1) (h1 : ‖v₁‖ = 1)
    (h01 : inner ℝ v₀ v₁ = 0) :
    ∃ b : Fin 4 → E4, Orthonormal ℝ b ∧ b 0 = v₀ ∧ b 1 = v₁ := by
  have hS2 : Module.finrank ℝ (Submodule.span ℝ {v₀, v₁}) < 4 := by
    have hle : Module.finrank ℝ (Submodule.span ℝ ({v₀, v₁} : Set E4)) ≤
        ({v₀, v₁} : Finset E4).card := by
      simpa using (finrank_span_le_card ({v₀, v₁} : Set E4))
    have hc : ({v₀, v₁} : Finset E4).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v₂, hv2norm, hv2orth⟩ := exists_unit_orthogonal_of_finrank_lt hS2
  have hv02 : inner ℝ v₀ v₂ = 0 := hv2orth v₀ (Submodule.subset_span (by simp))
  have hv12 : inner ℝ v₁ v₂ = 0 := hv2orth v₁ (Submodule.subset_span (by simp))
  have hS3 : Module.finrank ℝ (Submodule.span ℝ {v₀, v₁, v₂}) < 4 := by
    have hle : Module.finrank ℝ (Submodule.span ℝ ({v₀, v₁, v₂} : Set E4)) ≤
        ({v₀, v₁, v₂} : Finset E4).card := by
      simpa using (finrank_span_le_card ({v₀, v₁, v₂} : Set E4))
    have hc : ({v₀, v₁, v₂} : Finset E4).card ≤ 3 :=
      le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ Finset.card_le_two)
    omega
  obtain ⟨v₃, hv3norm, hv3orth⟩ := exists_unit_orthogonal_of_finrank_lt hS3
  have hv03 : inner ℝ v₀ v₃ = 0 := hv3orth v₀ (Submodule.subset_span (by simp))
  have hv13 : inner ℝ v₁ v₃ = 0 := hv3orth v₁ (Submodule.subset_span (by simp))
  have hv23 : inner ℝ v₂ v₃ = 0 := hv3orth v₂ (Submodule.subset_span (by simp))
  refine ⟨![v₀, v₁, v₂, v₃], ?_, rfl, rfl⟩
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [h0, h1, hv2norm, hv3norm, h01, hv02, hv12, hv03, hv13, hv23, real_inner_comm]

/-- A unit normal slab `{x ∈ S³ | |⟪v, x⟫| ≤ ε}` has `volume.toSphere.real` bounded by `64 * ε`. -/
lemma toSphere_slab_bound {v : E4} (hv : ‖v‖ = 1) {ε : ℝ} (hε : 0 ≤ ε) :
    MeasureTheory.volume.toSphere.real
        {x : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ v (x : E4)| ≤ ε} ≤ 64 * ε := by
  let e₀ : E4 := WithLp.toLp 2 (Pi.single (0 : Fin 4) (1 : ℝ))
  have he₀ : ‖e₀‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [e₀, Pi.single_apply]
  let u : ↑(Metric.sphere (0 : E4) 1) := ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
  let w0 : ↑(Metric.sphere (0 : E4) 1) := ⟨e₀, mem_sphere_zero_iff_norm.mpr he₀⟩
  obtain ⟨g, hg⟩ := oGroup_transitive_sphere u w0
  let B₀ : Set ↑(Metric.sphere (0 : E4) 1) :=
    {x | |inner ℝ (w0 : E4) (x : E4)| ≤ ε}
  let B : Set ↑(Metric.sphere (0 : E4) 1) :=
    {x | |inner ℝ (u : E4) (x : E4)| ≤ ε}
  have hpre : B = ⇑(orthoSphereAct g) ⁻¹' B₀ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, B, B₀]
    rw [← hg, orthoSphereAct_val, orthoSphereAct_val, orthoEquiv_apply, orthoEquiv_apply,
      ortho_mulVecE_inner]
  have hB₀_closed : IsClosed B₀ :=
    isClosed_le (continuous_const.inner continuous_subtype_val).abs continuous_const
  have hB₀_meas : MeasurableSet B₀ := hB₀_closed.measurableSet
  have hvol_eq : MeasureTheory.volume.toSphere.real B = MeasureTheory.volume.toSphere.real B₀ := by
    rw [hpre]
    exact measureReal_toSphere_preimage_oGroup g hB₀_meas
  rw [hvol_eq]
  let B₀E : Set E4 := Subtype.val '' B₀
  have hB₀_sub : B₀E ⊆ Metric.sphere (0 : E4) 1 := by
    intro y hy
    rcases hy with ⟨x, _, rfl⟩
    exact x.2
  have hB₀E_meas : MeasurableSet B₀E := by
    have hcomp : IsCompact B₀ :=
      IsCompact.of_isClosed_subset isCompact_univ hB₀_closed (Set.subset_univ _)
    exact (hcomp.image continuous_subtype_val).measurableSet
  have hbox :
      Set.Ioo (0 : ℝ) 1 • B₀E ⊆
        WithLp.ofLp ⁻¹' (Set.univ.pi fun k : Fin 4 =>
          if k = 0 then Set.Icc (-ε) ε else Set.Icc (-1 : ℝ) 1) := by
    intro z hz
    rcases Set.mem_smul.mp hz with ⟨t, ht, y, hy, rfl⟩
    rcases hy with ⟨x, hx, rfl⟩
    have hx_le : |inner ℝ e₀ (x : E4)| ≤ ε := hx
    have hx0 : inner ℝ e₀ (x : E4) = (x : E4).ofLp 0 := by
      simp [e₀, PiLp.inner_apply]
    intro k _
    by_cases hk : k = 0
    · subst hk
      simp only [Set.mem_Icc, PiLp.smul_apply, smul_eq_mul, ↓reduceIte]
      rw [hx0] at hx_le
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have ht1 : t ≤ 1 := le_of_lt ht.2
      rw [abs_le] at hx_le
      constructor <;> nlinarith
    · simp only [hk, ↓reduceIte, Set.mem_Icc]
      have hxnorm : ‖(x : E4)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
      have hcoord : |(x : E4).ofLp k| ≤ 1 := by
        simpa [hxnorm] using PiLp.norm_apply_le (x : E4) k
      rw [abs_le] at hcoord
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have ht1 : t ≤ 1 := le_of_lt ht.2
      simp only [PiLp.smul_apply, smul_eq_mul]
      constructor <;> nlinarith
  have hbox_meas :
      MeasureTheory.volume.real (Set.Ioo (0 : ℝ) 1 • B₀E) ≤ 16 * ε := by
    have hpi_meas : MeasurableSet
        (Set.univ.pi fun k : Fin 4 => if k = 0 then Set.Icc (-ε) ε else Set.Icc (-1 : ℝ) 1) :=
      MeasurableSet.univ_pi fun k => by split_ifs <;> exact measurableSet_Icc
    have hpi_vol :
        MeasureTheory.volume
            ((WithLp.ofLp : E4 → Fin 4 → ℝ) ⁻¹' (Set.univ.pi fun k : Fin 4 =>
              if k = 0 then Set.Icc (-ε) ε else Set.Icc (-1 : ℝ) 1)) =
          ENNReal.ofReal (16 * ε) := by
      rw [(PiLp.volume_preserving_ofLp (Fin 4)).measure_preimage hpi_meas.nullMeasurableSet]
      rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
      have hprod :
          (∏ i : Fin 4,
            MeasureTheory.volume (if i = 0 then Set.Icc (-ε) ε else Set.Icc (-1 : ℝ) 1)) =
            MeasureTheory.volume (Set.Icc (-ε) ε) *
              (MeasureTheory.volume (Set.Icc (-1 : ℝ) 1)) ^ 3 := by
        rw [Fin.prod_univ_four]
        simp [pow_three, mul_assoc]
      rw [hprod, Real.volume_Icc, Real.volume_Icc]
      have h1 : ε - -ε = 2 * ε := by ring
      have h2 : (1 : ℝ) - -1 = 2 := by ring
      rw [h1, h2]
      have hpow : (ENNReal.ofReal 2) ^ 3 = ENNReal.ofReal 8 := by
        rw [← ENNReal.ofReal_pow (by norm_num)]
        norm_num
      rw [hpow, ← ENNReal.ofReal_mul (by linarith)]
      congr 1; ring
    have hvol_le := MeasureTheory.measureReal_mono hbox (by rw [hpi_vol]; exact ENNReal.ofReal_ne_top)
    have hpi :
        MeasureTheory.volume.real
            ((WithLp.ofLp : E4 → Fin 4 → ℝ) ⁻¹' (Set.univ.pi fun k : Fin 4 =>
              if k = 0 then Set.Icc (-ε) ε else Set.Icc (-1 : ℝ) 1)) =
          16 * ε := by
      rw [MeasureTheory.measureReal_def, hpi_vol, ENNReal.toReal_ofReal (by linarith)]
    exact hvol_le.trans hpi.le
  have hmeas3 :
      measure 3 B₀E = 4 * sphereScale 3 * MeasureTheory.volume.real (Set.Ioo (0 : ℝ) 1 • B₀E) :=
    measure_three_eq_four_sphereScale_mul_ballCone hB₀_sub hB₀E_meas
  have hmeas_toSphere :
      measure 3 B₀E = sphereScale 3 * MeasureTheory.volume.toSphere.real B₀ := by
    have hraw := hausdorffMeasure_real_eq_scale_mul_toSphere (d := 3) (by omega) hB₀_sub hB₀E_meas
    norm_num at hraw
    rw [measure, hraw, Set.preimage_image_eq _ Subtype.val_injective]
  have hss_pos : 0 < sphereScale 3 := sphereScale_pos (by decide)
  nlinarith

/-- Rotation by angle `α` in the `(0, 1)` plane of `E4`. -/
def rot4_01 (α : ℝ) : OGroup 4 := by
  refine ⟨!![Real.cos α, -Real.sin α, 0, 0;
             Real.sin α,  Real.cos α, 0, 0;
             0,           0,          1, 0;
             0,           0,          0, 1], ?_⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four] <;>
    nlinarith [Real.sin_sq_add_cos_sq α]

lemma rot4_01_apply (α : ℝ) (x : E4) :
    mulVecE (rot4_01 α : OGroup 4) x =
      WithLp.toLp 2 ![Real.cos α * x.ofLp 0 - Real.sin α * x.ofLp 1,
        Real.sin α * x.ofLp 0 + Real.cos α * x.ofLp 1, x.ofLp 2, x.ofLp 3] := by
  ext i
  fin_cases i <;>
    simp [rot4_01, mulVecE_apply, Fin.sum_univ_four] <;> ring

/-- Closed 4D spherical sector of angle `θ` around the `(0, 1)` plane. -/
def sectorClosed4 (θ : ℝ) : Set ↑(Metric.sphere (0 : E4) 1) :=
  {y | ∃ φ ∈ Set.Icc 0 θ, ∃ r : ℝ, 0 ≤ r ∧
    (y : E4).ofLp 0 = r * Real.cos φ ∧ (y : E4).ofLp 1 = r * Real.sin φ}

lemma sectorClosed4_mono {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    sectorClosed4 θ₁ ⊆ sectorClosed4 θ₂ := by
  intro y ⟨φ, hφ, r, hr, h0, h1⟩
  exact ⟨φ, ⟨hφ.1, hφ.2.trans h⟩, r, hr, h0, h1⟩

lemma isClosed_sectorClosed4 (θ : ℝ) : IsClosed (sectorClosed4 θ) := by
  let K : Set (ℝ × ℝ × ↑(Metric.sphere (0 : E4) 1)) :=
    (Set.Icc 0 θ ×ˢ Set.Icc 0 2 ×ˢ Set.univ) ∩
      {p | (p.2.2 : E4).ofLp 0 = p.2.1 * Real.cos p.1 ∧
           (p.2.2 : E4).ofLp 1 = p.2.1 * Real.sin p.1}
  have hprod_comp : IsCompact (Set.Icc 0 θ ×ˢ Set.Icc (0 : ℝ) 2 ×ˢ
      (Set.univ : Set ↑(Metric.sphere (0 : E4) 1))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_univ)
  have hK_closed : IsClosed {p : ℝ × ℝ × ↑(Metric.sphere (0 : E4) 1) |
      (p.2.2 : E4).ofLp 0 = p.2.1 * Real.cos p.1 ∧
      (p.2.2 : E4).ofLp 1 = p.2.1 * Real.sin p.1} := by
    refine IsClosed.inter (isClosed_eq ?_ ?_) (isClosed_eq ?_ ?_)
    · exact ((EuclideanSpace.proj (0 : Fin 4)).continuous.comp continuous_subtype_val).comp
        (continuous_snd.comp continuous_snd)
    · exact (continuous_fst.comp continuous_snd).mul (Real.continuous_cos.comp continuous_fst)
    · exact ((EuclideanSpace.proj (1 : Fin 4)).continuous.comp continuous_subtype_val).comp
        (continuous_snd.comp continuous_snd)
    · exact (continuous_fst.comp continuous_snd).mul (Real.continuous_sin.comp continuous_fst)
  have hK_comp : IsCompact K := hprod_comp.inter_right hK_closed
  have himg : (fun p : ℝ × ℝ × ↑(Metric.sphere (0 : E4) 1) => p.2.2) '' K = sectorClosed4 θ := by
    ext y
    constructor
    · rintro ⟨⟨φ, r, z⟩, ⟨⟨hφ, hr, _⟩, h0, h1⟩, rfl⟩
      exact ⟨φ, hφ, r, hr.1, h0, h1⟩
    · rintro ⟨φ, hφ, r, hr0, h0, h1⟩
      have hr2 : r ≤ 2 := by
        have hy1 : ‖(y : E4)‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
        have hn0 : |(y : E4).ofLp 0| ≤ 1 := by simpa [hy1] using PiLp.norm_apply_le (y : E4) 0
        have hn1 : |(y : E4).ofLp 1| ≤ 1 := by simpa [hy1] using PiLp.norm_apply_le (y : E4) 1
        have hsq : r ^ 2 = (y : E4).ofLp 0 ^ 2 + (y : E4).ofLp 1 ^ 2 := by
          rw [h0, h1]
          nlinarith [Real.sin_sq_add_cos_sq φ]
        have h0_sq : (y : E4).ofLp 0 ^ 2 ≤ 1 := by nlinarith [abs_le.mp hn0]
        have h1_sq : (y : E4).ofLp 1 ^ 2 ≤ 1 := by nlinarith [abs_le.mp hn1]
        by_contra hr_gt
        push Not at hr_gt
        nlinarith
      exact ⟨(φ, r, y), ⟨⟨hφ, ⟨hr0, hr2⟩, Set.mem_univ _⟩, h0, h1⟩, rfl⟩
  rw [← himg]
  exact (hK_comp.image (continuous_snd.comp continuous_snd)).isClosed

lemma sectorClosed4_measurableSet (θ : ℝ) : MeasurableSet (sectorClosed4 θ) :=
  (isClosed_sectorClosed4 θ).measurableSet

lemma sectorClosed4_two_pi : sectorClosed4 (2 * Real.pi) = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  by_cases hzero : (y : E4).ofLp 0 = 0 ∧ (y : E4).ofLp 1 = 0
  · refine ⟨0, ⟨le_rfl, by positivity⟩, 0, le_rfl, ?_, ?_⟩ <;> simp [hzero.1, hzero.2]
  · let z : ℂ := ((y : E4).ofLp 0 : ℂ) + ((y : E4).ofLp 1 : ℂ) * Complex.I
    have hz : z ≠ 0 := by
      intro h
      apply hzero
      exact ⟨by simpa [z] using congrArg Complex.re h, by simpa [z] using congrArg Complex.im h⟩
    have hre : (y : E4).ofLp 0 = ‖z‖ * Real.cos z.arg := by
      rw [Complex.cos_arg hz, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
      simp [z]
    have him : (y : E4).ofLp 1 = ‖z‖ * Real.sin z.arg := by
      rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
      simp [z]
    by_cases hnonneg : 0 ≤ z.arg
    · exact ⟨z.arg, ⟨hnonneg, (Complex.arg_le_pi z).trans (by linarith [Real.pi_pos])⟩,
        ‖z‖, norm_nonneg z, hre, him⟩
    · have hgt : -Real.pi < z.arg := Complex.neg_pi_lt_arg z
      refine ⟨z.arg + 2 * Real.pi, ⟨by linarith, by linarith⟩, ‖z‖, norm_nonneg z, ?_, ?_⟩
      · simpa [Real.cos_add_two_pi] using hre
      · simpa [Real.sin_add_two_pi] using him

lemma rot4_01_image_sectorClosed4 (α θ : ℝ) :
    ⇑(orthoSphereAct (rot4_01 α)) '' sectorClosed4 θ =
      {y : ↑(Metric.sphere (0 : E4) 1) | ∃ φ ∈ Set.Icc α (α + θ), ∃ r : ℝ, 0 ≤ r ∧
        (y : E4).ofLp 0 = r * Real.cos φ ∧ (y : E4).ofLp 1 = r * Real.sin φ} := by
  ext y
  constructor
  · rintro ⟨x, ⟨φ, hφ, r, hr, hx0, hx1⟩, rfl⟩
    refine ⟨α + φ, ⟨by linarith [hφ.1], by linarith [hφ.2]⟩, r, hr, ?_, ?_⟩
    · simp only [orthoSphereAct_val, orthoEquiv_apply, rot4_01_apply, Matrix.cons_val_zero,
        hx0, hx1, Real.cos_add]; ring
    · simp only [orthoSphereAct_val, orthoEquiv_apply, rot4_01_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, hx0, hx1, Real.sin_add]; ring
  · rintro ⟨φ, hφ, r, hr, hy0, hy1⟩
    refine ⟨orthoSphereAct (rot4_01 (-α)) y, ?_, ?_⟩
    · refine ⟨φ - α, ⟨by linarith [hφ.1], by linarith [hφ.2]⟩, r, hr, ?_, ?_⟩
      · simp only [orthoSphereAct_val, orthoEquiv_apply, rot4_01_apply, Matrix.cons_val_zero,
          hy0, hy1, Real.cos_neg, Real.sin_neg, Real.cos_sub]; ring
      · simp only [orthoSphereAct_val, orthoEquiv_apply, rot4_01_apply, Matrix.cons_val_one,
          Matrix.cons_val_zero, hy0, hy1, Real.cos_neg, Real.sin_neg, Real.sin_sub]; ring
    · apply Subtype.ext
      simp only [orthoSphereAct_val, orthoEquiv_apply, ← ortho_mulVecE_mul]
      have hmul : rot4_01 α * rot4_01 (-α) = 1 := by
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [rot4_01, Real.cos_neg, Real.sin_neg] <;>
          try nlinarith [Real.sin_sq_add_cos_sq α]
      rw [hmul, ortho_mulVecE_one]

lemma toSphere_sectorClosed4_ray_eq_zero (φ : ℝ) :
    MeasureTheory.volume.toSphere
        {y : ↑(Metric.sphere (0 : E4) 1) |
          ∃ r : ℝ, 0 ≤ r ∧ (y : E4).ofLp 0 = r * Real.cos φ ∧ (y : E4).ofLp 1 = r * Real.sin φ} =
      0 := by
  let w : E4 := WithLp.toLp 2 ![Real.sin φ, -Real.cos φ, 0, 0]
  have hw : w ≠ 0 := by
    intro h
    have h0 : w.ofLp 0 = 0 := by rw [h]; rfl
    have h1 : w.ofLp 1 = 0 := by rw [h]; rfl
    simp [w] at h0 h1
    nlinarith [Real.sin_sq_add_cos_sq φ]
  refine measure_mono_null ?_ (volume_toSphere_hyperplane_eq_zero hw)
  rintro y ⟨r, _, hy0, hy1⟩
  simp only [Set.mem_ofPred_eq, PiLp.inner_apply, Fin.sum_univ_four, w]
  rw [hy0, hy1]
  simp; ring

lemma toSphere_sectorClosed4_union {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂)
    (h12 : θ₁ + θ₂ ≤ 2 * Real.pi) :
    MeasureTheory.volume.toSphere.real (sectorClosed4 (θ₁ + θ₂)) =
      MeasureTheory.volume.toSphere.real (sectorClosed4 θ₁) +
        MeasureTheory.volume.toSphere.real (sectorClosed4 θ₂) := by
  have hS2_pre :
      ⇑(orthoSphereAct (rot4_01 θ₁)) '' sectorClosed4 θ₂ =
        ⇑(orthoSphereAct (rot4_01 θ₁)⁻¹) ⁻¹' sectorClosed4 θ₂ := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      convert hx using 1
      apply Subtype.ext
      simp only [orthoSphereAct_val, orthoEquiv_apply, ← ortho_mulVecE_mul, inv_mul_cancel,
        ortho_mulVecE_one]
    · intro hy
      refine ⟨orthoSphereAct (rot4_01 θ₁)⁻¹ y, hy, ?_⟩
      apply Subtype.ext
      simp only [orthoSphereAct_val, orthoEquiv_apply, ← ortho_mulVecE_mul, mul_inv_cancel,
        ortho_mulVecE_one]
  have hS2_rot :
      MeasureTheory.volume.toSphere.real (⇑(orthoSphereAct (rot4_01 θ₁)) '' sectorClosed4 θ₂) =
        MeasureTheory.volume.toSphere.real (sectorClosed4 θ₂) := by
    rw [hS2_pre]
    exact measureReal_toSphere_preimage_oGroup (rot4_01 θ₁)⁻¹ (sectorClosed4_measurableSet θ₂)
  rw [← hS2_rot]
  have hunion :
      sectorClosed4 (θ₁ + θ₂) =
        sectorClosed4 θ₁ ∪ (⇑(orthoSphereAct (rot4_01 θ₁)) '' sectorClosed4 θ₂) := by
    ext y
    rw [Set.mem_union, rot4_01_image_sectorClosed4]
    constructor
    · rintro ⟨φ, hφ, r, hr, hy0, hy1⟩
      by_cases hle : φ ≤ θ₁
      · exact Or.inl ⟨φ, ⟨hφ.1, hle⟩, r, hr, hy0, hy1⟩
      · exact Or.inr ⟨φ, ⟨le_of_lt (lt_of_not_ge hle), hφ.2⟩, r, hr, hy0, hy1⟩
    · rintro (⟨φ, hφ, r, hr, hy0, hy1⟩ | ⟨φ, hφ, r, hr, hy0, hy1⟩)
      · exact ⟨φ, ⟨hφ.1, hφ.2.trans (by linarith)⟩, r, hr, hy0, hy1⟩
      · exact ⟨φ, ⟨h1.trans hφ.1, hφ.2⟩, r, hr, hy0, hy1⟩
  have hinter :
      MeasureTheory.volume.toSphere
          (sectorClosed4 θ₁ ∩ (⇑(orthoSphereAct (rot4_01 θ₁)) '' sectorClosed4 θ₂)) = 0 := by
    refine measure_mono_null ?_ (measure_union_null (toSphere_sectorClosed4_ray_eq_zero θ₁)
      (toSphere_sectorClosed4_ray_eq_zero 0))
    intro y ⟨hy1, hy2⟩
    rw [rot4_01_image_sectorClosed4] at hy2
    rcases hy1 with ⟨φ₁, hφ₁, r₁, hr₁, hy0, hy1'⟩
    rcases hy2 with ⟨φ₂, hφ₂, r₂, hr₂, hy0', hy1''⟩
    by_cases hr0 : r₁ = 0
    · left
      exact ⟨0, le_rfl, by simpa [hr0] using hy0, by simpa [hr0] using hy1'⟩
    · have hr1_pos : 0 < r₁ := lt_of_le_of_ne hr₁ (Ne.symm hr0)
      have hsq : r₁ ^ 2 = r₂ ^ 2 := by
        have hsum : (y : E4).ofLp 0 ^ 2 + (y : E4).ofLp 1 ^ 2 = r₁ ^ 2 := by
          rw [hy0, hy1']; nlinarith [Real.sin_sq_add_cos_sq φ₁]
        have hsum' : (y : E4).ofLp 0 ^ 2 + (y : E4).ofLp 1 ^ 2 = r₂ ^ 2 := by
          rw [hy0', hy1'']; nlinarith [Real.sin_sq_add_cos_sq φ₂]
        linarith
      have hr_eq : r₁ = r₂ := by nlinarith [sq_nonneg (r₁ - r₂)]
      subst hr_eq
      have hcos : Real.cos φ₁ = Real.cos φ₂ := mul_left_cancel₀ hr1_pos.ne' (hy0.symm.trans hy0')
      have hsin : Real.sin φ₁ = Real.sin φ₂ := mul_left_cancel₀ hr1_pos.ne' (hy1'.symm.trans hy1'')
      have hdiff_sub : Real.cos (φ₂ - φ₁) = 1 := by
        rw [Real.cos_sub, ← hcos, ← hsin]
        nlinarith [Real.cos_sq_add_sin_sq φ₁]
      have hdiff0 : 0 ≤ φ₂ - φ₁ := by linarith [hφ₁.2, hφ₂.1]
      have hdiff_le : φ₂ - φ₁ ≤ 2 * Real.pi := by linarith [hφ₁.1, hφ₂.2, h12]
      rcases eq_or_lt_of_le hdiff0 with hzero | _
      · have heq : φ₁ = θ₁ := by linarith [hφ₁.2, hφ₂.1]
        left
        exact ⟨r₁, hr₁, by simpa [heq] using hy0, by simpa [heq] using hy1'⟩
      · have hpi2 : φ₂ - φ₁ = 2 * Real.pi := by
          rcases lt_or_eq_of_le hdiff_le with hlt | heq
          · have hhalf_pos : 0 < (φ₂ - φ₁) / 2 := by linarith
            have hhalf_lt : (φ₂ - φ₁) / 2 < Real.pi := by linarith
            have hsin_pos : 0 < Real.sin ((φ₂ - φ₁) / 2) := Real.sin_pos_of_pos_of_lt_pi hhalf_pos hhalf_lt
            have hsin_sq : 2 * Real.sin ((φ₂ - φ₁) / 2) ^ 2 = 1 - Real.cos (φ₂ - φ₁) := by
              have hcos2 := Real.cos_two_mul' ((φ₂ - φ₁) / 2)
              have hh : 2 * ((φ₂ - φ₁) / 2) = φ₂ - φ₁ := by ring
              rw [hh] at hcos2
              nlinarith [Real.cos_sq_add_sin_sq ((φ₂ - φ₁) / 2)]
            rw [hdiff_sub] at hsin_sq
            nlinarith
          · exact heq
        have h0 : φ₁ = 0 := by linarith [hφ₁.1, hφ₂.2, h12, hpi2]
        right
        exact ⟨r₁, hr₁, by simpa [h0] using hy0, by simpa [h0] using hy1'⟩
  have hS2_meas : MeasurableSet (⇑(orthoSphereAct (rot4_01 θ₁)) '' sectorClosed4 θ₂) := by
    rw [hS2_pre]
    exact (sectorClosed4_measurableSet θ₂).preimage (orthoSphereAct _).continuous.measurable
  rw [hunion]
  exact measureReal_union_inter_null MeasureTheory.volume.toSphere
    (sectorClosed4_measurableSet θ₁) hS2_meas hinter

lemma toSphere_sectorClosed4_mul_nat {θ : ℝ} (hθ : 0 ≤ θ) :
    ∀ n : ℕ, (n : ℝ) * θ ≤ 2 * Real.pi →
      MeasureTheory.volume.toSphere.real (sectorClosed4 (n * θ)) =
        n * MeasureTheory.volume.toSphere.real (sectorClosed4 θ) := by
  intro n hn
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    rw [MeasureTheory.measureReal_def]
    have hsub : sectorClosed4 0 ⊆ {y : ↑(Metric.sphere (0 : E4) 1) |
        ∃ r : ℝ, 0 ≤ r ∧ (y : E4).ofLp 0 = r * Real.cos 0 ∧ (y : E4).ofLp 1 = r * Real.sin 0} := by
      rintro y ⟨φ, hφ, r, hr, h0, h1⟩
      have hφ0 : φ = 0 := le_antisymm hφ.2 hφ.1
      subst hφ0
      exact ⟨r, hr, h0, h1⟩
    rw [measure_mono_null hsub (toSphere_sectorClosed4_ray_eq_zero 0)]
    simp
  | succ k ih =>
    have hk_le : (k : ℝ) * θ ≤ 2 * Real.pi := by
      have : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
      nlinarith
    have hsucc_eq : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by push_cast; ring
    rw [hsucc_eq, toSphere_sectorClosed4_union (mul_nonneg (Nat.cast_nonneg k) hθ) hθ
      (hsucc_eq ▸ hn), ih hk_le]
    push_cast; ring

lemma toSphere_sectorClosed4_eq {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ 2 * Real.pi) :
    MeasureTheory.volume.toSphere.real (sectorClosed4 θ) =
      θ / (2 * Real.pi) *
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) := by
  set M := MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1))
  have hM_nonneg : 0 ≤ M := MeasureTheory.measureReal_nonneg
  have hfull : MeasureTheory.volume.toSphere.real (sectorClosed4 (2 * Real.pi)) = M := by
    rw [sectorClosed4_two_pi]
  have hbound : ∀ (n : ℕ), 0 < n →
      |MeasureTheory.volume.toSphere.real (sectorClosed4 θ) - θ / (2 * Real.pi) * M| ≤ M / n := by
    intro n hn
    let δ : ℝ := (2 * Real.pi) / n
    have hδ : 0 < δ := div_pos (by positivity) (Nat.cast_pos.mpr hn)
    have hnδ : (n : ℝ) * δ = 2 * Real.pi := mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')
    have hδ_val : MeasureTheory.volume.toSphere.real (sectorClosed4 δ) = M / n := by
      have hmul := toSphere_sectorClosed4_mul_nat hδ.le n hnδ.le
      rw [hnδ, hfull] at hmul
      exact eq_div_of_mul_eq (Nat.cast_ne_zero.mpr hn.ne') (by rw [mul_comm, ← hmul])
    let k : ℕ := Nat.floor (θ / δ)
    have hk_le : (k : ℝ) * δ ≤ θ := by
      have := Nat.floor_le (div_nonneg h0 hδ.le)
      exact (le_div_iff₀ hδ).mp this
    have hlt_k : θ < ((k + 1 : ℕ) : ℝ) * δ := by
      have := Nat.lt_floor_add_one (θ / δ)
      push_cast at this ⊢
      exact (div_lt_iff₀ hδ).mp this
    have hk_le_n : k ≤ n := by
      have hkn : (k : ℝ) * δ ≤ (n : ℝ) * δ := hk_le.trans (hpi.trans hnδ.ge)
      exact_mod_cast le_of_mul_le_mul_right hkn hδ
    have hk_val : MeasureTheory.volume.toSphere.real (sectorClosed4 (k * δ)) = k * (M / n) := by
      rw [toSphere_sectorClosed4_mul_nat hδ.le k
        ((mul_le_mul_of_nonneg_right (by exact_mod_cast hk_le_n) hδ.le).trans hnδ.le), hδ_val]
    have hsucc_val :
        MeasureTheory.volume.toSphere.real (sectorClosed4 (min ((k + 1 : ℕ) * δ) (2 * Real.pi))) ≤
          (k + 1 : ℕ) * (M / n) := by
      by_cases hkn1 : k + 1 ≤ n
      · have hle2 : ((k + 1 : ℕ) : ℝ) * δ ≤ 2 * Real.pi := by
          calc ((k + 1 : ℕ) : ℝ) * δ ≤ (n : ℝ) * δ :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hkn1) hδ.le
          _ = 2 * Real.pi := hnδ
        rw [min_eq_left hle2, toSphere_sectorClosed4_mul_nat hδ.le (k + 1) hle2, hδ_val]
      · have hkne : k = n := by omega
        have hmin_r : 2 * Real.pi ≤ ((k + 1 : ℕ) : ℝ) * δ := by
          push_cast; rw [hkne]; nlinarith [hnδ, hδ]
        rw [min_eq_right hmin_r]
        rw [hfull]
        have : (n : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ k + 1)
        have hdiv : M = (n : ℝ) * (M / n) := by
          field_simp [Nat.cast_ne_zero.mpr hn.ne']
        nlinarith [div_nonneg hM_nonneg (Nat.cast_nonneg n)]
    have hμ_low : (k : ℝ) * (M / n) ≤ MeasureTheory.volume.toSphere.real (sectorClosed4 θ) := by
      rw [← hk_val]
      exact MeasureTheory.measureReal_mono (sectorClosed4_mono hk_le) (measure_ne_top _ _)
    have hμ_high : MeasureTheory.volume.toSphere.real (sectorClosed4 θ) ≤ (k + 1 : ℕ) * (M / n) := by
      calc MeasureTheory.volume.toSphere.real (sectorClosed4 θ)
          ≤ MeasureTheory.volume.toSphere.real (sectorClosed4 (min ((k + 1 : ℕ) * δ) (2 * Real.pi))) :=
            MeasureTheory.measureReal_mono (sectorClosed4_mono (le_min hlt_k.le hpi))
              (measure_ne_top _ _)
      _ ≤ (k + 1 : ℕ) * (M / n) := hsucc_val
    have hθ_low : (k : ℝ) * (M / n) ≤ θ / (2 * Real.pi) * M := by
      have hk_div : (k : ℝ) / n ≤ θ / (2 * Real.pi) := by
        rw [← hnδ]
        have : (k : ℝ) * δ / ((n : ℝ) * δ) ≤ θ / ((n : ℝ) * δ) :=
          div_le_div_of_nonneg_right hk_le (mul_nonneg (Nat.cast_nonneg n) hδ.le)
        rwa [mul_div_mul_right _ _ hδ.ne'] at this
      calc (k : ℝ) * (M / n) = ((k : ℝ) / n) * M := by ring
      _ ≤ (θ / (2 * Real.pi)) * M := mul_le_mul_of_nonneg_right hk_div hM_nonneg
    have hθ_high : θ / (2 * Real.pi) * M ≤ ((k + 1 : ℕ) : ℝ) * (M / n) := by
      have hk_div : θ / (2 * Real.pi) ≤ ((k + 1 : ℕ) : ℝ) / n := by
        rw [← hnδ]
        have : θ / ((n : ℝ) * δ) ≤ ((k + 1 : ℕ) : ℝ) * δ / ((n : ℝ) * δ) :=
          div_le_div_of_nonneg_right hlt_k.le (mul_nonneg (Nat.cast_nonneg n) hδ.le)
        rwa [mul_div_mul_right _ _ hδ.ne'] at this
      calc θ / (2 * Real.pi) * M ≤ (((k + 1 : ℕ) : ℝ) / n) * M :=
            mul_le_mul_of_nonneg_right hk_div hM_nonneg
      _ = ((k + 1 : ℕ) : ℝ) * (M / n) := by ring
    rw [abs_le]
    push_cast at hμ_high hθ_high ⊢
    constructor <;> linarith
  by_contra hne
  set err := |MeasureTheory.volume.toSphere.real (sectorClosed4 θ) - θ / (2 * Real.pi) * M|
  have herr : 0 < err := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos herr (by linarith : 0 < M + 1))
  have hn_pos : 0 < n + 1 := Nat.succ_pos n
  have hle := hbound (n + 1) hn_pos
  have hlt : M / (n + 1 : ℕ) < err := by
    have h1 : 1 / ((n : ℝ) + 1) < err / (M + 1) := by simpa using hn
    have h2 : M / ((n : ℝ) + 1) = M * (1 / ((n : ℝ) + 1)) := by ring
    push_cast
    rw [h2]
    calc M * (1 / ((n : ℝ) + 1)) ≤ M * (err / (M + 1)) :=
          mul_le_mul_of_nonneg_left h1.le hM_nonneg
    _ < (M + 1) * (err / (M + 1)) := by nlinarith [div_pos herr (by linarith : 0 < M + 1)]
    _ = err := by field_simp [(by linarith : M + 1 ≠ 0)]
  linarith

/-- Standard 4D lune of two unit vectors in `S³`. -/
def lune4 (u v : ↑(Metric.sphere (0 : E4) 1)) : Set ↑(Metric.sphere (0 : E4) 1) :=
  {y | 0 ≤ inner ℝ (u : E4) (y : E4) ∧ 0 ≤ inner ℝ (v : E4) (y : E4)}

lemma lune4_measurableSet (u v : ↑(Metric.sphere (0 : E4) 1)) : MeasurableSet (lune4 u v) := by
  have hcont : ∀ w : E4,
      Continuous (fun y : ↑(Metric.sphere (0 : E4) 1) => inner ℝ w (y : E4)) :=
    fun _ => continuous_const.inner continuous_subtype_val
  have hcl : IsClosed (lune4 u v) := by
    change IsClosed {y : ↑(Metric.sphere (0 : E4) 1) |
      0 ≤ inner ℝ (u : E4) (y : E4) ∧ 0 ≤ inner ℝ (v : E4) (y : E4)}
    exact IsClosed.inter
      (isClosed_le continuous_const (hcont (u : E4)))
      (isClosed_le continuous_const (hcont (v : E4)))
  exact hcl.measurableSet

/-- On `S³ ⊂ E4`, the spherical volume of a lune equals `(luneAngle u v / (2π)) * μ(S³)`. -/
lemma toSphere_real_lune4 (u v : ↑(Metric.sphere (0 : E4) 1)) :
    MeasureTheory.volume.toSphere.real (lune4 u v) =
      Real.arccos (-inner ℝ (u : E4) (v : E4)) / (2 * Real.pi) *
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) := by
  let θ := Real.arccos (-inner ℝ (u : E4) (v : E4))
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθpi : θ ≤ Real.pi := Real.arccos_le_pi _
  have hu1 : ‖(u : E4)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hv1 : ‖(v : E4)‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hinner_bnd : -1 ≤ -inner ℝ (u : E4) (v : E4) ∧ -inner ℝ (u : E4) (v : E4) ≤ 1 := by
    rw [← abs_le, abs_neg]
    simpa [hu1, hv1] using abs_real_inner_le_norm (u : E4) (v : E4)
  have hcosθ : Real.cos θ = -inner ℝ (u : E4) (v : E4) := Real.cos_arccos hinner_bnd.1 hinner_bnd.2
  by_cases hθZero : θ = 0
  · have hvu : (v : E4) = -(u : E4) := by
      have hcos1 : -inner ℝ (u : E4) (v : E4) = 1 := by
        simpa [hθZero] using hcosθ.symm
      have hsq : ‖(u : E4) + (v : E4)‖ ^ 2 = 0 := by
        rw [norm_add_sq_real, hu1, hv1]
        have : inner ℝ (u : E4) (v : E4) = -1 := by linarith
        rw [this]; ring
      exact add_eq_zero_iff_eq_neg'.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    have hsub : lune4 u v ⊆ {y : ↑(Metric.sphere (0 : E4) 1) | inner ℝ (u : E4) (y : E4) = 0} := by
      intro y ⟨huy, hvy⟩
      rw [hvu, inner_neg_left] at hvy
      exact le_antisymm (neg_nonneg.mp hvy) huy
    have hu_ne : (u : E4) ≠ 0 := by intro h; rw [h, norm_zero] at hu1; norm_num at hu1
    rw [MeasureTheory.measureReal_def, measure_mono_null hsub (volume_toSphere_hyperplane_eq_zero hu_ne)]
    rw [show Real.arccos (-inner ℝ (u : E4) (v : E4)) = θ from rfl, hθZero]
    simp
  · by_cases hθPi : θ = Real.pi
    · have hvu : (v : E4) = (u : E4) := by
        have hcos1 : -inner ℝ (u : E4) (v : E4) = -1 := by
          simpa [hθPi] using hcosθ.symm
        have hsq : ‖(u : E4) - (v : E4)‖ ^ 2 = 0 := by
          rw [norm_sub_sq_real, hu1, hv1]
          have : inner ℝ (u : E4) (v : E4) = 1 := by linarith
          rw [this]; ring
        exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))).symm
      let e₁ : E4 := WithLp.toLp 2 (Pi.single (1 : Fin 4) (1 : ℝ))
      have he₁ : ‖e₁‖ = 1 := by rw [EuclideanSpace.norm_eq]; simp [e₁, Pi.single_apply]
      obtain ⟨g, hg⟩ := oGroup_transitive_sphere u ⟨e₁, mem_sphere_zero_iff_norm.mpr he₁⟩
      have hsec : sectorClosed4 Real.pi =
          {y : ↑(Metric.sphere (0 : E4) 1) | 0 ≤ (y : E4).ofLp 1} := by
        ext y
        simp only [sectorClosed4, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨φ, hφ, r, hr, _, h1⟩
          rw [h1]
          exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2)
        · intro hy1
          by_cases hzero : (y : E4).ofLp 0 = 0 ∧ (y : E4).ofLp 1 = 0
          · refine ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, 0, le_rfl, ?_, ?_⟩ <;> simp [hzero.1, hzero.2]
          · let z : ℂ := ((y : E4).ofLp 0 : ℂ) + ((y : E4).ofLp 1 : ℂ) * Complex.I
            have hz : z ≠ 0 := by
              intro h
              apply hzero
              exact ⟨by simpa [z] using congrArg Complex.re h, by simpa [z] using congrArg Complex.im h⟩
            have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by simpa [z] using hy1)
            refine ⟨z.arg, ⟨harg0, Complex.arg_le_pi z⟩, ‖z‖, norm_nonneg z, ?_, ?_⟩
            · rw [Complex.cos_arg hz, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]; simp [z]
            · rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]; simp [z]
      have hpre : lune4 u v = ⇑(orthoSphereAct g) ⁻¹' sectorClosed4 Real.pi := by
        ext y
        rw [Set.mem_preimage, hsec]
        simp only [lune4, Set.mem_ofPred_eq, hvu, and_self]
        have hinn : inner ℝ (u : E4) (y : E4) =
            inner ℝ (orthoEquiv g (u : E4)) (orthoEquiv g (y : E4)) := by
          simp [orthoEquiv_apply, ortho_mulVecE_inner]
        have hge₁ : orthoEquiv g (u : E4) = e₁ := by
          simpa [orthoSphereAct_val] using congrArg Subtype.val hg
        rw [hinn, hge₁]
        have hdot : inner ℝ e₁ (orthoEquiv g (y : E4)) = ((orthoSphereAct g y : E4).ofLp 1) := by
          simp [e₁, PiLp.inner_apply, orthoSphereAct_val]
        rw [hdot]
      rw [hpre, MeasureTheory.measureReal_def]
      have hmap := toSphere_oGroup_invariant 4 g
      have hm := Measure.map_apply (μ := MeasureTheory.volume.toSphere)
        (orthoSphereAct g).continuous.measurable (sectorClosed4_measurableSet Real.pi)
      rw [hmap] at hm
      rw [← hm]
      change MeasureTheory.volume.toSphere.real (sectorClosed4 Real.pi) = _
      rw [show Real.arccos (-inner ℝ (u : E4) (v : E4)) = θ from rfl, hθPi]
      exact toSphere_sectorClosed4_eq Real.pi_pos.le (by linarith [Real.pi_pos])
    · have hθ_pos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθZero)
      have hθ_lt : θ < Real.pi := lt_of_le_of_ne hθpi hθPi
      have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt
      have hsin_sq : Real.sin θ ^ 2 = 1 - inner ℝ (u : E4) (v : E4) ^ 2 := by
        have := Real.sin_sq_add_cos_sq θ
        rw [hcosθ] at this
        linarith
      let r_vec : E4 := (v : E4) - inner ℝ (u : E4) (v : E4) • (u : E4)
      have hr_norm_sq : ‖r_vec‖ ^ 2 = Real.sin θ ^ 2 := by
        rw [norm_sub_sq_real, hv1]
        have h2 : inner ℝ (v : E4) (inner ℝ (u : E4) (v : E4) • (u : E4)) =
            inner ℝ (u : E4) (v : E4) ^ 2 := by
          rw [inner_smul_right, real_inner_comm]; ring
        have h3 : ‖inner ℝ (u : E4) (v : E4) • (u : E4)‖ ^ 2 = inner ℝ (u : E4) (v : E4) ^ 2 := by
          rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, sq_abs]
        rw [h2, h3, hsin_sq]; ring
      have hr_norm : ‖r_vec‖ = Real.sin θ := by nlinarith [norm_nonneg r_vec]
      let w : E4 := (Real.sin θ)⁻¹ • r_vec
      have hw_norm : ‖w‖ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsin_pos.le), hr_norm,
          inv_mul_cancel₀ hsin_pos.ne']
      have hw_orth : inner ℝ w (u : E4) = 0 := by
        simp only [w, r_vec, inner_smul_left, inner_sub_left, real_inner_comm (u : E4) (v : E4)]
        rw [real_inner_self_eq_norm_sq, hu1]
        simp
      have hv_decomp : (v : E4) = Real.sin θ • w - Real.cos θ • (u : E4) := by
        ext i
        simp [w, r_vec, hcosθ, smul_smul, mul_inv_cancel₀ hsin_pos.ne']
      obtain ⟨b, hb, hb0, hb1⟩ := exists_orthonormal_extension_pair hw_norm hu1 hw_orth
      let g : OGroup 4 := (orthoOfOrthonormal hb)⁻¹
      have hgu : orthoEquiv g (u : E4) = WithLp.toLp 2 (Pi.single 1 1) := by
        rw [← hb1]; exact mulVecE_orthoOfOrthonormal_inv hb 1
      have hgw : orthoEquiv g w = WithLp.toLp 2 (Pi.single 0 1) := by
        rw [← hb0]; exact mulVecE_orthoOfOrthonormal_inv hb 0
      have hgv : orthoEquiv g (v : E4) =
          Real.sin θ • WithLp.toLp 2 (Pi.single 0 1) -
            Real.cos θ • WithLp.toLp 2 (Pi.single 1 1) := by
        have hm1 : orthoEquiv g (Real.sin θ • w) = Real.sin θ • orthoEquiv g w := map_smul _ _ _
        have hm2 : orthoEquiv g (Real.cos θ • (u : E4)) = Real.cos θ • orthoEquiv g (u : E4) :=
          map_smul _ _ _
        calc orthoEquiv g (v : E4)
            = orthoEquiv g (Real.sin θ • w - Real.cos θ • (u : E4)) := by rw [hv_decomp]
          _ = orthoEquiv g (Real.sin θ • w) - orthoEquiv g (Real.cos θ • (u : E4)) := map_sub _ _ _
          _ = Real.sin θ • orthoEquiv g w - Real.cos θ • orthoEquiv g (u : E4) := by rw [hm1, hm2]
          _ = Real.sin θ • WithLp.toLp 2 (Pi.single 0 1) -
                Real.cos θ • WithLp.toLp 2 (Pi.single 1 1) := by rw [hgw, hgu]
      have hsec_eq : sectorClosed4 θ =
          {y : ↑(Metric.sphere (0 : E4) 1) |
            0 ≤ (y : E4).ofLp 1 ∧ 0 ≤ (y : E4).ofLp 0 * Real.sin θ - (y : E4).ofLp 1 * Real.cos θ} := by
        ext y
        simp only [sectorClosed4, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨φ, hφ, r, hr, hy0, hy1⟩
          constructor
          · rw [hy1]
            exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (hφ.2.trans hθpi))
          · have : (y : E4).ofLp 0 * Real.sin θ - (y : E4).ofLp 1 * Real.cos θ =
                r * Real.sin (θ - φ) := by
              rw [hy0, hy1, Real.sin_sub]; ring
            rw [this]
            exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.2])
              (by linarith [hφ.1, hθpi]))
        · rintro ⟨hy1, hyw⟩
          by_cases hzero : (y : E4).ofLp 0 = 0 ∧ (y : E4).ofLp 1 = 0
          · refine ⟨0, ⟨le_rfl, hθ0⟩, 0, le_rfl, ?_, ?_⟩ <;> simp [hzero.1, hzero.2]
          · let z : ℂ := ((y : E4).ofLp 0 : ℂ) + ((y : E4).ofLp 1 : ℂ) * Complex.I
            have hz : z ≠ 0 := by
              intro h
              apply hzero
              exact ⟨by simpa [z] using congrArg Complex.re h, by simpa [z] using congrArg Complex.im h⟩
            have harg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by simpa [z] using hy1)
            have hre : (y : E4).ofLp 0 = ‖z‖ * Real.cos z.arg := by
              rw [Complex.cos_arg hz, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]; simp [z]
            have him : (y : E4).ofLp 1 = ‖z‖ * Real.sin z.arg := by
              rw [Complex.sin_arg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hz)]; simp [z]
            have hsin_sub : 0 ≤ Real.sin (θ - z.arg) := by
              have heq : (y : E4).ofLp 0 * Real.sin θ - (y : E4).ofLp 1 * Real.cos θ =
                  ‖z‖ * Real.sin (θ - z.arg) := by
                rw [hre, him, Real.sin_sub]; ring
              rw [heq] at hyw
              exact nonneg_of_mul_nonneg_right hyw (norm_pos_iff.mpr hz)
            have hle_θ : z.arg ≤ θ := by
              by_contra hgt
              have hlt0 : θ < z.arg := lt_of_not_ge hgt
              have hneg_pos : 0 < z.arg - θ := by linarith
              have hneg_lt : z.arg - θ < Real.pi := by linarith [Complex.arg_le_pi z]
              have hsin_neg : Real.sin (θ - z.arg) < 0 := by
                have hpos := Real.sin_pos_of_pos_of_lt_pi hneg_pos hneg_lt
                have hneg : Real.sin (θ - z.arg) = -Real.sin (z.arg - θ) := by
                  rw [← Real.sin_neg (z.arg - θ), neg_sub]
                linarith
              linarith
            exact ⟨z.arg, ⟨harg0, hle_θ⟩, ‖z‖, norm_nonneg z, hre, him⟩
      have hpre : lune4 u v = ⇑(orthoSphereAct g) ⁻¹' sectorClosed4 θ := by
        ext y
        rw [Set.mem_preimage, hsec_eq]
        simp only [lune4, Set.mem_ofPred_eq]
        have hu_inn : inner ℝ (u : E4) (y : E4) =
            inner ℝ (orthoEquiv g (u : E4)) (orthoEquiv g (y : E4)) := by
          simp [orthoEquiv_apply, ortho_mulVecE_inner]
        have hv_inn : inner ℝ (v : E4) (y : E4) =
            inner ℝ (orthoEquiv g (v : E4)) (orthoEquiv g (y : E4)) := by
          simp [orthoEquiv_apply, ortho_mulVecE_inner]
        rw [hu_inn, hv_inn, hgu, hgv]
        simp [orthoSphereAct_val, PiLp.inner_apply, Fin.sum_univ_four,
          inner_sub_left, inner_smul_left]
        intro _
        constructor <;> intro h <;> linarith
      rw [hpre, MeasureTheory.measureReal_def]
      have hmap := toSphere_oGroup_invariant 4 g
      have hm := Measure.map_apply (μ := MeasureTheory.volume.toSphere)
        (orthoSphereAct g).continuous.measurable (sectorClosed4_measurableSet θ)
      rw [hmap] at hm
      rw [← hm]
      change MeasureTheory.volume.toSphere.real (sectorClosed4 θ) = _
      exact toSphere_sectorClosed4_eq hθ0 (hθpi.trans (by linarith [Real.pi_pos]))

/-- Standard 4D suspension of a spherical triangle cut by 3 half-spaces in `S³`. -/
def triSusp4 (w : Fin 3 → ↑(Metric.sphere (0 : E4) 1)) : Set ↑(Metric.sphere (0 : E4) 1) :=
  {y | ∀ k : Fin 3, 0 ≤ inner ℝ (w k : E4) (y : E4)}

lemma triSusp4_measurableSet (w : Fin 3 → ↑(Metric.sphere (0 : E4) 1)) :
    MeasurableSet (triSusp4 w) := by
  have heq : triSusp4 w = ⋂ k : Fin 3, {y : ↑(Metric.sphere (0 : E4) 1) | 0 ≤ inner ℝ (w k : E4) (y : E4)} := by
    ext y; simp [triSusp4]
  rw [heq]
  exact MeasurableSet.iInter fun k =>
    (isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)).measurableSet

/-- Volume on `S³` of a 3-hyperplane sector `triSusp4 w` via Girard's lune count. -/
lemma toSphere_real_triSusp4 (w : Fin 3 → ↑(Metric.sphere (0 : E4) 1)) :
    MeasureTheory.volume.toSphere.real (triSusp4 w) =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
          (4 * Real.pi) *
        (Real.arccos (-inner ℝ (w 0 : E4) (w 1 : E4)) +
         Real.arccos (-inner ℝ (w 1 : E4) (w 2 : E4)) +
         Real.arccos (-inner ℝ (w 2 : E4) (w 0 : E4)) - Real.pi) := by
  let S := triSusp4 w
  let sgn := fun (a b c : Bool) =>
    {y : ↑(Metric.sphere (0 : E4) 1) |
      (if a then 0 ≤ inner ℝ (w 0 : E4) (y : E4) else 0 ≤ -inner ℝ (w 0 : E4) (y : E4)) ∧
      (if b then 0 ≤ inner ℝ (w 1 : E4) (y : E4) else 0 ≤ -inner ℝ (w 1 : E4) (y : E4)) ∧
      (if c then 0 ≤ inner ℝ (w 2 : E4) (y : E4) else 0 ≤ -inner ℝ (w 2 : E4) (y : E4))}
  have hsgn_meas : ∀ a b c, MeasurableSet (sgn a b c) := by
    have hcont : ∀ k : Fin 3,
        Continuous (fun y : ↑(Metric.sphere (0 : E4) 1) => inner ℝ (w k : E4) (y : E4)) :=
      fun _ => continuous_const.inner continuous_subtype_val
    have hm_pos : ∀ k : Fin 3,
        MeasurableSet {y : ↑(Metric.sphere (0 : E4) 1) | 0 ≤ inner ℝ (w k : E4) (y : E4)} :=
      fun k => (isClosed_le continuous_const (hcont k)).measurableSet
    have hm_neg : ∀ k : Fin 3,
        MeasurableSet {y : ↑(Metric.sphere (0 : E4) 1) | 0 ≤ -inner ℝ (w k : E4) (y : E4)} :=
      fun k => (isClosed_le continuous_const (hcont k).neg).measurableSet
    intro a b c
    cases a <;> cases b <;> cases c <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte]
    all_goals
      refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
      · first | exact hm_pos 0 | exact hm_neg 0
      · first | exact hm_pos 1 | exact hm_neg 1
      · first | exact hm_pos 2 | exact hm_neg 2
  have hnull_k : ∀ k : Fin 3,
      MeasureTheory.volume.toSphere {y : ↑(Metric.sphere (0 : E4) 1) | inner ℝ (w k : E4) (y : E4) = 0} = 0 := by
    intro k
    refine volume_toSphere_hyperplane_eq_zero ?_
    have hk := mem_sphere_zero_iff_norm.mp (w k).2
    intro h; rw [h, norm_zero] at hk; norm_num at hk
  have hnull_all : MeasureTheory.volume.toSphere
      (⋃ k : Fin 3, {y : ↑(Metric.sphere (0 : E4) 1) | inner ℝ (w k : E4) (y : E4) = 0}) = 0 :=
    measure_iUnion_null hnull_k
  have hneg_inv : ∀ a b c,
      MeasureTheory.volume.toSphere.real (sgn a b c) =
        MeasureTheory.volume.toSphere.real (sgn (!a) (!b) (!c)) := by
    intro a b c
    let negO : OGroup 4 := ⟨-1, by rw [Matrix.mem_orthogonalGroup_iff]; simp⟩
    have hpre : sgn a b c = ⇑(orthoSphereAct negO) ⁻¹' sgn (!a) (!b) (!c) := by
      ext y
      have hact : (orthoSphereAct negO y : E4) = -(y : E4) := by
        ext i
        fin_cases i <;>
          simp [orthoSphereAct_val, orthoEquiv_apply, negO, mulVecE_apply, Fin.sum_univ_four]
      simp only [sgn, Set.mem_preimage, Set.mem_ofPred_eq, hact, inner_neg_right]
      cases a <;> cases b <;> cases c <;> simp
    rw [hpre, MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    have hmap := toSphere_oGroup_invariant 4 negO
    have hm := Measure.map_apply (μ := MeasureTheory.volume.toSphere)
      (orthoSphereAct negO).continuous.measurable (hsgn_meas (!a) (!b) (!c))
    rw [hmap] at hm
    rw [← hm]
  have hsgn_inter : ∀ a₁ b₁ c₁ a₂ b₂ c₂,
      (a₁, b₁, c₁) ≠ (a₂, b₂, c₂) →
      MeasureTheory.volume.toSphere (sgn a₁ b₁ c₁ ∩ sgn a₂ b₂ c₂) = 0 := by
    intro a₁ b₁ c₁ a₂ b₂ c₂ hne
    refine measure_mono_null ?_ hnull_all
    intro y ⟨hy1, hy2⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra hzero
    push Not at hzero
    have hz0 := hzero 0
    have hz1 := hzero 1
    have hz2 := hzero 2
    rcases hy1 with ⟨h10, h11, h12⟩
    rcases hy2 with ⟨h20, h21, h22⟩
    have ha : a₁ = a₂ := by
      cases a₁ <;> cases a₂ <;> simp at h10 h20 ⊢
      · exact absurd (le_antisymm h10 h20) hz0
      · exact absurd (le_antisymm h20 h10) hz0
    have hb : b₁ = b₂ := by
      cases b₁ <;> cases b₂ <;> simp at h11 h21 ⊢
      · exact absurd (le_antisymm h11 h21) hz1
      · exact absurd (le_antisymm h21 h11) hz1
    have hc : c₁ = c₂ := by
      cases c₁ <;> cases c₂ <;> simp at h12 h22 ⊢
      · exact absurd (le_antisymm h12 h22) hz2
      · exact absurd (le_antisymm h22 h12) hz2
    exact hne (by simp [ha, hb, hc])
  have hS_eq : S = sgn true true true := by
    ext y
    simp only [S, triSusp4, sgn, Set.mem_ofPred_eq, ↓reduceIte]
    exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ k => by fin_cases k <;> assumption⟩
  have hlune01 : lune4 (w 0) (w 1) = sgn true true true ∪ sgn true true false := by
    ext y
    simp only [lune4, sgn, Set.mem_union, Set.mem_ofPred_eq, ↓reduceIte]
    constructor
    · rintro ⟨h0, h1⟩
      rcases le_total 0 (inner ℝ (w 2 : E4) (y : E4)) with h2 | h2
      · exact Or.inl ⟨h0, h1, h2⟩
      · exact Or.inr ⟨h0, h1, neg_nonneg.mpr h2⟩
    · rintro (⟨h0, h1, _⟩ | ⟨h0, h1, _⟩) <;> exact ⟨h0, h1⟩
  have hlune12 : lune4 (w 1) (w 2) = sgn true true true ∪ sgn false true true := by
    ext y
    simp only [lune4, sgn, Set.mem_union, Set.mem_ofPred_eq, ↓reduceIte]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_total 0 (inner ℝ (w 0 : E4) (y : E4)) with h0 | h0
      · exact Or.inl ⟨h0, h1, h2⟩
      · exact Or.inr ⟨neg_nonneg.mpr h0, h1, h2⟩
    · rintro (⟨_, h1, h2⟩ | ⟨_, h1, h2⟩) <;> exact ⟨h1, h2⟩
  have hlune20 : lune4 (w 2) (w 0) = sgn true true true ∪ sgn true false true := by
    ext y
    simp only [lune4, sgn, Set.mem_union, Set.mem_ofPred_eq, ↓reduceIte]
    constructor
    · rintro ⟨h2, h0⟩
      rcases le_total 0 (inner ℝ (w 1 : E4) (y : E4)) with h1 | h1
      · exact Or.inl ⟨h0, h1, h2⟩
      · exact Or.inr ⟨h0, neg_nonneg.mpr h1, h2⟩
    · rintro (⟨h0, _, h2⟩ | ⟨h0, _, h2⟩) <;> exact ⟨h2, h0⟩
  have hm01 : MeasureTheory.volume.toSphere.real (lune4 (w 0) (w 1)) =
      MeasureTheory.volume.toSphere.real (sgn true true true) +
        MeasureTheory.volume.toSphere.real (sgn true true false) := by
    rw [hlune01]
    exact measureReal_union_inter_null MeasureTheory.volume.toSphere
      (hsgn_meas true true true) (hsgn_meas true true false)
      (hsgn_inter true true true true true false (by decide))
  have hm12 : MeasureTheory.volume.toSphere.real (lune4 (w 1) (w 2)) =
      MeasureTheory.volume.toSphere.real (sgn true true true) +
        MeasureTheory.volume.toSphere.real (sgn false true true) := by
    rw [hlune12]
    exact measureReal_union_inter_null MeasureTheory.volume.toSphere
      (hsgn_meas true true true) (hsgn_meas false true true)
      (hsgn_inter true true true false true true (by decide))
  have hm20 : MeasureTheory.volume.toSphere.real (lune4 (w 2) (w 0)) =
      MeasureTheory.volume.toSphere.real (sgn true true true) +
        MeasureTheory.volume.toSphere.real (sgn true false true) := by
    rw [hlune20]
    exact measureReal_union_inter_null MeasureTheory.volume.toSphere
      (hsgn_meas true true true) (hsgn_meas true false true)
      (hsgn_inter true true true true false true (by decide))
  have huniv :
      (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) =
        (sgn true true true ∪ sgn false false false) ∪
        ((sgn true true false ∪ sgn false false true) ∪
         (sgn false true true ∪ sgn true false false) ∪
         (sgn true false true ∪ sgn false true false)) := by
    ext y
    simp only [Set.mem_univ, Set.mem_union, true_iff, sgn, Set.mem_ofPred_eq, ↓reduceIte]
    rcases le_total 0 (inner ℝ (w 0 : E4) (y : E4)) with h0 | h0 <;>
    rcases le_total 0 (inner ℝ (w 1 : E4) (y : E4)) with h1 | h1 <;>
    rcases le_total 0 (inner ℝ (w 2 : E4) (y : E4)) with h2 | h2
    · exact Or.inl (Or.inl ⟨h0, h1, h2⟩)
    · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨h0, h1, neg_nonneg.mpr h2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h0, neg_nonneg.mpr h1, h2⟩))
    · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨h0, neg_nonneg.mpr h1, neg_nonneg.mpr h2⟩)))
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨neg_nonneg.mpr h0, h1, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr ⟨neg_nonneg.mpr h0, h1, neg_nonneg.mpr h2⟩))
    · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨neg_nonneg.mpr h0, neg_nonneg.mpr h1, h2⟩)))
    · exact Or.inl (Or.inr ⟨neg_nonneg.mpr h0, neg_nonneg.mpr h1, neg_nonneg.mpr h2⟩)
  have add_pair : ∀ a b c,
      MeasureTheory.volume.toSphere.real (sgn a b c ∪ sgn (!a) (!b) (!c)) =
        2 * MeasureTheory.volume.toSphere.real (sgn a b c) := by
    intro a b c
    rw [measureReal_union_inter_null MeasureTheory.volume.toSphere
      (hsgn_meas a b c) (hsgn_meas (!a) (!b) (!c))
      (hsgn_inter a b c (!a) (!b) (!c) (by cases a <;> cases b <;> cases c <;> decide))]
    rw [← hneg_inv a b c]
    ring
  have hsum_univ :
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) =
        2 * (MeasureTheory.volume.toSphere.real (sgn true true true) +
             MeasureTheory.volume.toSphere.real (sgn true true false) +
             MeasureTheory.volume.toSphere.real (sgn false true true) +
             MeasureTheory.volume.toSphere.real (sgn true false true)) := by
    have huniv_eq := congrArg MeasureTheory.volume.toSphere.real huniv
    have hp_null : ∀ a₁ b₁ c₁ a₂ b₂ c₂,
        (a₁, b₁, c₁) ≠ (a₂, b₂, c₂) → (a₁, b₁, c₁) ≠ (!a₂, !b₂, !c₂) →
        MeasureTheory.volume.toSphere
          ((sgn a₁ b₁ c₁ ∪ sgn (!a₁) (!b₁) (!c₁)) ∩ (sgn a₂ b₂ c₂ ∪ sgn (!a₂) (!b₂) (!c₂))) = 0 := by
      intro a₁ b₁ c₁ a₂ b₂ c₂ hne1 hne2
      rw [Set.union_inter_distrib_right, Set.inter_union_distrib_left, Set.inter_union_distrib_left]
      exact measure_union_null
        (measure_union_null (hsgn_inter _ _ _ _ _ _ hne1) (hsgn_inter _ _ _ _ _ _ hne2))
        (measure_union_null
          (hsgn_inter _ _ _ _ _ _ (by
            intro h; revert h hne1 hne2
            cases a₁ <;> cases b₁ <;> cases c₁ <;> cases a₂ <;> cases b₂ <;> cases c₂ <;> decide))
          (hsgn_inter _ _ _ _ _ _ (by
            intro h; revert h hne1 hne2
            cases a₁ <;> cases b₁ <;> cases c₁ <;> cases a₂ <;> cases b₂ <;> cases c₂ <;> decide)))
    have h01 := hp_null true true true true true false (by decide) (by decide)
    have h02 := hp_null true true true false true true (by decide) (by decide)
    have h03 := hp_null true true true true false true (by decide) (by decide)
    have h12 := hp_null true true false false true true (by decide) (by decide)
    have h13 := hp_null true true false true false true (by decide) (by decide)
    have h23 := hp_null false true true true false true (by decide) (by decide)
    have hp0 := add_pair true true true
    have hp1 := add_pair true true false
    have hp2 := add_pair false true true
    have hp3 := add_pair true false true
    simp only [Bool.not_true, Bool.not_false] at h01 h02 h03 h12 h13 h23 hp0 hp1 hp2 hp3
    have h12_3 :
        MeasureTheory.volume.toSphere
          (((sgn true true false ∪ sgn false false true) ∪
            (sgn false true true ∪ sgn true false false)) ∩
            (sgn true false true ∪ sgn false true false)) = 0 := by
      rw [Set.union_inter_distrib_right]
      exact measure_union_null h13 h23
    have h0_123 :
        MeasureTheory.volume.toSphere
          ((sgn true true true ∪ sgn false false false) ∩
            (((sgn true true false ∪ sgn false false true) ∪
              (sgn false true true ∪ sgn true false false)) ∪
              (sgn true false true ∪ sgn false true false))) = 0 := by
      rw [Set.inter_union_distrib_left, Set.inter_union_distrib_left]
      exact measure_union_null (measure_union_null h01 h02) h03
    rw [measureReal_union_inter_null MeasureTheory.volume.toSphere
      ((hsgn_meas true true true).union (hsgn_meas false false false))
      ((((hsgn_meas true true false).union (hsgn_meas false false true)).union
        ((hsgn_meas false true true).union (hsgn_meas true false false))).union
        ((hsgn_meas true false true).union (hsgn_meas false true false))) h0_123] at huniv_eq
    rw [measureReal_union_inter_null MeasureTheory.volume.toSphere
      (((hsgn_meas true true false).union (hsgn_meas false false true)).union
        ((hsgn_meas false true true).union (hsgn_meas true false false)))
      ((hsgn_meas true false true).union (hsgn_meas false true false)) h12_3] at huniv_eq
    rw [measureReal_union_inter_null MeasureTheory.volume.toSphere
      ((hsgn_meas true true false).union (hsgn_meas false false true))
      ((hsgn_meas false true true).union (hsgn_meas true false false)) h12] at huniv_eq
    rw [hp0, hp1, hp2, hp3] at huniv_eq
    linarith
  let M4 := MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1))
  have hcount :
      2 * (M4 * Real.arccos (-inner ℝ (w 0 : E4) (w 1 : E4)) / (2 * Real.pi) +
           M4 * Real.arccos (-inner ℝ (w 1 : E4) (w 2 : E4)) / (2 * Real.pi) +
           M4 * Real.arccos (-inner ℝ (w 2 : E4) (w 0 : E4)) / (2 * Real.pi)) =
        M4 + 4 * MeasureTheory.volume.toSphere.real S := by
    have h01 := toSphere_real_lune4 (w 0) (w 1)
    have h12 := toSphere_real_lune4 (w 1) (w 2)
    have h20 := toSphere_real_lune4 (w 2) (w 0)
    have e01 : M4 * Real.arccos (-inner ℝ (w 0 : E4) (w 1 : E4)) / (2 * Real.pi) =
        MeasureTheory.volume.toSphere.real (sgn true true true) +
          MeasureTheory.volume.toSphere.real (sgn true true false) := by
      rw [← hm01, h01]; dsimp [M4]; ring
    have e12 : M4 * Real.arccos (-inner ℝ (w 1 : E4) (w 2 : E4)) / (2 * Real.pi) =
        MeasureTheory.volume.toSphere.real (sgn true true true) +
          MeasureTheory.volume.toSphere.real (sgn false true true) := by
      rw [← hm12, h12]; dsimp [M4]; ring
    have e20 : M4 * Real.arccos (-inner ℝ (w 2 : E4) (w 0 : E4)) / (2 * Real.pi) =
        MeasureTheory.volume.toSphere.real (sgn true true true) +
          MeasureTheory.volume.toSphere.real (sgn true false true) := by
      rw [← hm20, h20]; dsimp [M4]; ring
    rw [e01, e12, e20, hS_eq]
    change _ = M4 + _
    rw [show M4 = MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) from rfl,
      hsum_univ]
    ring
  exact Sphere3.girard_algebra_of_lune_count
    M4 (MeasureTheory.volume.toSphere.real S)
    (Real.arccos (-inner ℝ (w 0 : E4) (w 1 : E4)))
    (Real.arccos (-inner ℝ (w 1 : E4) (w 2 : E4)))
    (Real.arccos (-inner ℝ (w 2 : E4) (w 0 : E4))) hcount

/-- The 2-Hausdorff measure of a suspended great-circle arc on `S² ⊂ u⊥` equals
`2 * faceScale * arccos (-⟪n₀, n₁⟫)`. -/
lemma measure_two_suspension_arc {u n₀ n₁ : E4} (hu : ‖u‖ = 1) (hn0 : ‖n₀‖ = 1) (hn1 : ‖n₁‖ = 1)
    (hu0 : inner ℝ u n₀ = 0) (hu1 : inner ℝ u n₁ = 0) :
    measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ u x = 0 ∧ 0 ≤ inner ℝ n₀ x ∧ 0 ≤ inner ℝ n₁ x} =
      2 * faceScale * Real.arccos (-inner ℝ n₀ n₁) := by
  have hS1 : Module.finrank ℝ (Submodule.span ℝ {u}) < 4 := by
    have hle : Module.finrank ℝ (Submodule.span ℝ ({u} : Set E4)) ≤
        ({u} : Finset E4).card := by
      simpa using finrank_span_le_card ({u} : Set E4)
    have hc : ({u} : Finset E4).card ≤ 1 := by simp
    omega
  obtain ⟨v₀, hv0norm, hv0orth⟩ := exists_unit_orthogonal_of_finrank_lt hS1
  have hu_v0 : inner ℝ u v₀ = 0 := hv0orth u (Submodule.subset_span (by simp))
  obtain ⟨b, hb, hb0, hb1⟩ := exists_orthonormal_extension_pair hu hv0norm hu_v0
  let b_rot : Fin 4 → E4 := ![b 1, b 2, b 3, b 0]
  have hb_rot : Orthonormal ℝ b_rot := by
    let idx : Fin 4 → Fin 4 := ![1, 2, 3, 0]
    have hidx_inj : Function.Injective idx := by
      intro i j h; fin_cases i <;> fin_cases j <;> simp_all [idx]
    have hb_rot_eq : ∀ i, b_rot i = b (idx i) := fun i => by fin_cases i <;> rfl
    rw [orthonormal_iff_ite]
    intro i j
    rw [hb_rot_eq i, hb_rot_eq j, orthonormal_iff_ite.mp hb (idx i) (idx j)]
    simp [hidx_inj.eq_iff]
  let g : OGroup 4 := orthoOfOrthonormal hb_rot
  let emb : E3 →ₗᵢ[ℝ] E4 :=
    { toFun := fun z => WithLp.toLp 2 ![z.ofLp 0, z.ofLp 1, z.ofLp 2, 0]
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_three, Fin.sum_univ_four] }
  let f : E3 →ₗᵢ[ℝ] E4 := (orthoEquiv g).toLinearIsometry.comp emb
  have hf_img :
      f '' (Set.univ : Set E3) = {x : E4 | inner ℝ u x = 0} := by
    ext x
    constructor
    · rintro ⟨z, _, rfl⟩
      simp only [f, LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
        Function.comp_apply, Set.mem_ofPred_eq]
      have hu_b3 : u = (orthoEquiv g) (WithLp.toLp 2 (Pi.single 3 1)) := by
        rw [orthoEquiv_apply, mulVecE_orthoOfOrthonormal_basis hb_rot 3]
        exact hb0.symm
      rw [hu_b3, LinearIsometryEquiv.inner_map_map]
      simp [emb, PiLp.inner_apply]
    · intro hx
      let y : E4 := (orthoEquiv g).symm x
      have hy3 : y.ofLp 3 = 0 := by
        have h1 : inner ℝ (WithLp.toLp 2 (Pi.single (3 : Fin 4) (1 : ℝ))) y = 0 := by
          have hu_eq : u = (orthoEquiv g) (WithLp.toLp 2 (Pi.single 3 1)) := by
            rw [orthoEquiv_apply, mulVecE_orthoOfOrthonormal_basis hb_rot 3]
            exact hb0.symm
          have hsymm : (orthoEquiv g).symm u = WithLp.toLp 2 (Pi.single 3 1) := by
            rw [hu_eq, LinearIsometryEquiv.symm_apply_apply]
          rw [← hsymm, LinearIsometryEquiv.inner_map_map]
          exact hx
        simpa [PiLp.inner_apply, Pi.single_apply, Fin.sum_univ_four] using h1
      let z : E3 := WithLp.toLp 2 ![y.ofLp 0, y.ofLp 1, y.ofLp 2]
      refine ⟨z, Set.mem_univ _, ?_⟩
      have hemb : emb z = y := by
        ext i; fin_cases i <;> simp [emb, z, hy3]
      simp [f, hemb, y]
  obtain ⟨n₀', hn₀'⟩ : ∃ n₀' : E3, f n₀' = n₀ := by
    have : n₀ ∈ f '' (Set.univ : Set E3) := by rw [hf_img]; exact hu0
    rcases this with ⟨n₀', _, h⟩; exact ⟨n₀', h⟩
  obtain ⟨n₁', hn₁'⟩ : ∃ n₁' : E3, f n₁' = n₁ := by
    have : n₁ ∈ f '' (Set.univ : Set E3) := by rw [hf_img]; exact hu1
    rcases this with ⟨n₁', _, h⟩; exact ⟨n₁', h⟩
  let u₀' : ↑(Metric.sphere (0 : E3) 1) :=
    ⟨n₀', mem_sphere_zero_iff_norm.mpr (by rw [← f.norm_map n₀', hn₀', hn0])⟩
  let u₁' : ↑(Metric.sphere (0 : E3) 1) :=
    ⟨n₁', mem_sphere_zero_iff_norm.mpr (by rw [← f.norm_map n₁', hn₁', hn1])⟩
  let L' : Set E3 := Subtype.val '' (lune u₀' u₁')
  have himgL :
      f '' L' = {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ u x = 0 ∧ 0 ≤ inner ℝ n₀ x ∧ 0 ≤ inner ℝ n₁ x} := by
    ext x
    constructor
    · rintro ⟨z, ⟨w, ⟨hw0, hw1⟩, rfl⟩, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, f.norm_map]
        exact mem_sphere_zero_iff_norm.mp w.2
      · have : f (w : E3) ∈ f '' Set.univ := ⟨w, Set.mem_univ _, rfl⟩
        rwa [hf_img] at this
      · rw [← hn₀', f.inner_map_map]; exact hw0
      · rw [← hn₁', f.inner_map_map]; exact hw1
    · rintro ⟨hxS, hxu, hx0, hx1⟩
      have hx_mem : x ∈ f '' (Set.univ : Set E3) := by rw [hf_img]; exact hxu
      rcases hx_mem with ⟨z, _, rfl⟩
      have hzS : z ∈ Metric.sphere (0 : E3) 1 := by
        rw [mem_sphere_zero_iff_norm, ← f.norm_map]
        exact mem_sphere_zero_iff_norm.mp hxS
      let zw : ↑(Metric.sphere (0 : E3) 1) := ⟨z, hzS⟩
      refine ⟨z, ⟨zw, ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · rw [← hn₀', f.inner_map_map] at hx0; exact hx0
      · rw [← hn₁', f.inner_map_map] at hx1; exact hx1
  rw [← himgL, measure, f.isometry.hausdorffMeasure_image (Or.inl (by norm_num))]
  have hL'_sub : L' ⊆ Metric.sphere (0 : E3) 1 := by
    rintro z ⟨w, _, rfl⟩; exact w.2
  have hL'_meas : MeasurableSet L' := by
    have hcl : IsClosed (lune u₀' u₁') := by
      have hcont : ∀ w : E3,
          Continuous (fun y : ↑(Metric.sphere (0 : E3) 1) => inner ℝ w (y : E3)) :=
        fun _ => continuous_const.inner continuous_subtype_val
      rw [lune]
      exact IsClosed.inter
        (isClosed_le continuous_const (hcont (u₀' : E3)))
        (isClosed_le continuous_const (hcont (u₁' : E3)))
    have hcomp : IsCompact (lune u₀' u₁') :=
      IsCompact.of_isClosed_subset isCompact_univ hcl (Set.subset_univ _)
    exact (hcomp.image continuous_subtype_val).measurableSet
  have h2 := @hausdorffMeasure_real_eq_scale_mul_toSphere 2 (by decide) L' hL'_sub hL'_meas
  norm_num at h2
  rw [h2, Set.preimage_image_eq _ Subtype.val_injective, toSphere_real_lune u₀' u₁']
  have hinner_eq : inner ℝ (u₀' : E3) (u₁' : E3) = inner ℝ n₀ n₁ := by
    change inner ℝ n₀' n₁' = inner ℝ n₀ n₁
    rw [← hn₀', ← hn₁', f.inner_map_map]
  simp only [luneAngle, hinner_eq, faceScale]
  ring

/-! ### Part 2: Euler/L'Huilier Triangle Excess and 2D `≤ 4`-gon Isoperimetry -/

/-- Standard 3D cross product on `E3`. -/
def cross3 (x y : E3) : E3 :=
  WithLp.toLp 2
    ![x.ofLp 1 * y.ofLp 2 - x.ofLp 2 * y.ofLp 1,
      x.ofLp 2 * y.ofLp 0 - x.ofLp 0 * y.ofLp 2,
      x.ofLp 0 * y.ofLp 1 - x.ofLp 1 * y.ofLp 0]

/-- Signed triple determinant `⟪a, b × c⟫` on `E3`. -/
def det3 (a b c : E3) : ℝ := inner ℝ a (cross3 b c)

lemma inner_left_cross3 (x y : E3) : inner ℝ x (cross3 x y) = 0 := by
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma inner_right_cross3 (x y : E3) : inner ℝ y (cross3 x y) = 0 := by
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma inner_cross3_left (x y : E3) : inner ℝ (cross3 x y) x = 0 := by
  rw [real_inner_comm]; exact inner_left_cross3 x y

lemma inner_cross3_right (x y : E3) : inner ℝ (cross3 x y) y = 0 := by
  rw [real_inner_comm]; exact inner_right_cross3 x y

lemma norm_sq_cross3 (x y : E3) : ‖cross3 x y‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 - inner ℝ x y ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, cross3,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  dsimp
  ring

lemma inner_cross3_cross3 (a b c d : E3) :
    inner ℝ (cross3 a b) (cross3 c d) = inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c := by
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma det3_cyclic (a b c : E3) : det3 a b c = det3 b c a := by
  simp [det3, cross3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma det3_swap_23 (a b c : E3) : det3 a c b = -det3 a b c := by
  simp [det3, cross3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma det3_neg_right (a b c : E3) : det3 a b (-c) = -det3 a b c := by
  simp [det3, cross3, PiLp.inner_apply, PiLp.neg_apply, Fin.sum_univ_three]
  ring

lemma det3_decomp (a b c y : E3) :
    det3 a b c • y = det3 y b c • a + det3 a y c • b + det3 a b y • c := by
  ext i
  fin_cases i <;>
    simp [det3, cross3, PiLp.inner_apply, PiLp.smul_apply, PiLp.add_apply, Fin.sum_univ_three] <;>
    ring

lemma cross3_ne_zero_of_abs_inner_lt {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : |inner ℝ u v| < 1) : cross3 u v ≠ 0 := by
  intro hz
  have h0 : ‖cross3 u v‖ ^ 2 = 0 := by rw [hz, norm_zero]; norm_num
  rw [norm_sq_cross3, hu, hv, one_pow, mul_one] at h0
  have hsq : inner ℝ u v ^ 2 < 1 := by
    have := sq_lt_sq' (abs_lt.mp h).1 (abs_lt.mp h).2
    simpa using this
  linarith

lemma tan_sq_half_eq_one_sub_cos_div_one_add_cos (x : ℝ) (hcos : 1 + Real.cos (2 * x) ≠ 0) :
    Real.tan x ^ 2 = (1 - Real.cos (2 * x)) / (1 + Real.cos (2 * x)) := by
  have hc0 : Real.cos x ≠ 0 := by
    intro h
    apply hcos
    rw [Real.cos_two_mul, h]
    ring
  rw [Real.tan_eq_sin_div_cos, div_pow, Real.cos_two_mul]
  have h1 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by linarith [Real.sin_sq_add_cos_sq x]
  rw [h1]
  field_simp [hc0]
  ring

private lemma lhuilier_trig_cos_part (x y z : ℝ) :
    let s := x + y + z
    (Real.sin s - Real.sin (s - 2 * z)) * Real.sin (s - 2 * x) * Real.sin (s - 2 * y) +
        (Real.sin (s - 2 * y) + Real.sin (s - 2 * x)) * Real.sin s * Real.sin (s - 2 * z) =
      2 * Real.sin x * Real.sin y * Real.sin z *
        (1 + Real.cos (2 * x) + Real.cos (2 * y) + Real.cos (2 * z)) := by
  intro s
  have hdiff1 : Real.sin s - Real.sin (s - 2 * z) = 2 * Real.cos (x + y) * Real.sin z := by
    change Real.sin ((x + y) + z) - Real.sin ((x + y) + z - 2 * z) = _
    rw [show (x + y) + z - 2 * z = (x + y) - z by ring]
    simp only [Real.sin_add, Real.sin_sub]
    ring
  have hsum2 : Real.sin (s - 2 * y) + Real.sin (s - 2 * x) = 2 * Real.sin z * Real.cos (x - y) := by
    rw [show s - 2 * y = z + (x - y) by dsimp [s]; ring,
      show s - 2 * x = z - (x - y) by dsimp [s]; ring]
    simp only [Real.sin_add, Real.sin_sub]
    ring
  have hp1 : 2 * Real.sin (s - 2 * x) * Real.sin (s - 2 * y) =
      Real.cos (2 * (x - y)) - Real.cos (2 * z) := by
    rw [Real.cos_sub_cos, show (2 * (x - y) + 2 * z) / 2 = s - 2 * y by dsimp [s]; ring,
      show (2 * (x - y) - 2 * z) / 2 = -(s - 2 * x) by dsimp [s]; ring, Real.sin_neg]
    ring
  have hp2 : 2 * Real.sin s * Real.sin (s - 2 * z) =
      Real.cos (2 * z) - Real.cos (2 * (x + y)) := by
    rw [Real.cos_sub_cos, show (2 * z + 2 * (x + y)) / 2 = s by dsimp [s]; ring,
      show (2 * z - 2 * (x + y)) / 2 = -(s - 2 * z) by dsimp [s]; ring, Real.sin_neg]
    ring
  have hcos2 : ∀ θ : ℝ, Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := fun θ => Real.cos_two_mul θ
  have hdiffc : Real.cos (x - y) - Real.cos (x + y) = 2 * Real.sin x * Real.sin y := by
    rw [Real.cos_sub, Real.cos_add]; ring
  have hsumc : Real.cos (2 * x) + Real.cos (2 * y) = 2 * Real.cos (x + y) * Real.cos (x - y) := by
    rw [Real.cos_add_cos, show (2 * x + 2 * y) / 2 = x + y by ring,
      show (2 * x - 2 * y) / 2 = x - y by ring]
  calc (Real.sin s - Real.sin (s - 2 * z)) * Real.sin (s - 2 * x) * Real.sin (s - 2 * y) +
        (Real.sin (s - 2 * y) + Real.sin (s - 2 * x)) * Real.sin s * Real.sin (s - 2 * z)
      = Real.cos (x + y) * Real.sin z * (2 * Real.sin (s - 2 * x) * Real.sin (s - 2 * y)) +
          Real.sin z * Real.cos (x - y) * (2 * Real.sin s * Real.sin (s - 2 * z)) := by
          rw [hdiff1, hsum2]; ring
    _ = Real.sin z * (Real.cos (x + y) * (Real.cos (2 * (x - y)) - Real.cos (2 * z)) +
          Real.cos (x - y) * (Real.cos (2 * z) - Real.cos (2 * (x + y)))) := by
          rw [hp1, hp2]; ring
    _ = Real.sin z * (Real.cos (x - y) - Real.cos (x + y)) *
          (1 + 2 * Real.cos (x + y) * Real.cos (x - y) + Real.cos (2 * z)) := by
          rw [hcos2 (x - y), hcos2 (x + y)]; ring
    _ = 2 * Real.sin x * Real.sin y * Real.sin z *
          (1 + Real.cos (2 * x) + Real.cos (2 * y) + Real.cos (2 * z)) := by
          rw [hdiffc, ← hsumc]; ring

private lemma lhuilier_trig_sin_part (x y z : ℝ) :
    let s := x + y + z
    Real.sin (s - 2 * y) + Real.sin (s - 2 * x) - Real.sin s + Real.sin (s - 2 * z) =
      4 * Real.sin x * Real.sin y * Real.sin z := by
  intro s
  have hs : s = x + y + z := rfl
  have hsx : s - 2 * x = y + z - x := by rw [hs]; ring
  have hsy : s - 2 * y = x + z - y := by rw [hs]; ring
  have hsz : s - 2 * z = x + y - z := by rw [hs]; ring
  rw [hs, hsx, hsy, hsz]
  simp only [Real.sin_add, Real.sin_sub, Real.cos_add]
  ring

private lemma lhuilier_trig_plus (u v w : ℝ) :
    1 + Real.cos (4 * u) + Real.cos (4 * v) + Real.cos (4 * w) +
        4 * Real.cos (2 * u) * Real.cos (2 * v) * Real.cos (2 * w) =
      8 * Real.cos (u + v + w) * Real.cos (v + w - u) *
        Real.cos (u - v + w) * Real.cos (u + v - w) := by
  have hc1 : 2 * Real.cos (u + v + w) * Real.cos (u + v - w) =
      Real.cos (2 * u + 2 * v) + Real.cos (2 * w) := by
    rw [Real.cos_add_cos, show (2 * u + 2 * v + 2 * w) / 2 = u + v + w by ring,
      show (2 * u + 2 * v - 2 * w) / 2 = u + v - w by ring]
  have hc2 : 2 * Real.cos (v + w - u) * Real.cos (u - v + w) =
      Real.cos (2 * w) + Real.cos (2 * u - 2 * v) := by
    rw [Real.cos_add_cos, show (2 * w + (2 * u - 2 * v)) / 2 = u - v + w by ring,
      show (2 * w - (2 * u - 2 * v)) / 2 = v + w - u by ring]; ring
  have h1 : Real.cos (2 * u + 2 * v) + Real.cos (2 * u - 2 * v) =
      2 * Real.cos (2 * u) * Real.cos (2 * v) := by
    rw [Real.cos_add_cos, show (2 * u + 2 * v + (2 * u - 2 * v)) / 2 = 2 * u by ring,
      show (2 * u + 2 * v - (2 * u - 2 * v)) / 2 = 2 * v by ring]
  have h2 : 2 * Real.cos (2 * u + 2 * v) * Real.cos (2 * u - 2 * v) =
      Real.cos (4 * u) + Real.cos (4 * v) := by
    rw [Real.cos_add_cos, show (4 * u + 4 * v) / 2 = 2 * u + 2 * v by ring,
      show (4 * u - 4 * v) / 2 = 2 * u - 2 * v by ring]
  have h3 : 2 * Real.cos (2 * w) ^ 2 = 1 + Real.cos (4 * w) := by
    conv_rhs => rw [show 4 * w = 2 * (2 * w) by ring, Real.cos_two_mul]
    ring
  symm
  calc 8 * Real.cos (u + v + w) * Real.cos (v + w - u) *
          Real.cos (u - v + w) * Real.cos (u + v - w)
      = 2 * (2 * Real.cos (u + v + w) * Real.cos (u + v - w)) *
          (2 * Real.cos (v + w - u) * Real.cos (u - v + w)) := by ring
    _ = 2 * Real.cos (2 * w) ^ 2 +
          2 * Real.cos (2 * w) * (Real.cos (2 * u + 2 * v) + Real.cos (2 * u - 2 * v)) +
          2 * Real.cos (2 * u + 2 * v) * Real.cos (2 * u - 2 * v) := by rw [hc1, hc2]; ring
    _ = 1 + Real.cos (4 * u) + Real.cos (4 * v) + Real.cos (4 * w) +
          4 * Real.cos (2 * u) * Real.cos (2 * v) * Real.cos (2 * w) := by
          rw [h1, h2, h3]; ring

private lemma lhuilier_trig_minus (u v w : ℝ) :
    4 * Real.cos (2 * u) * Real.cos (2 * v) * Real.cos (2 * w) -
        (1 + Real.cos (4 * u) + Real.cos (4 * v) + Real.cos (4 * w)) =
      8 * Real.sin (u + v + w) * Real.sin (v + w - u) *
        Real.sin (u - v + w) * Real.sin (u + v - w) := by
  have hs1 : 2 * Real.sin (u + v + w) * Real.sin (u + v - w) =
      Real.cos (2 * w) - Real.cos (2 * u + 2 * v) := by
    rw [Real.cos_sub_cos, show (2 * w + (2 * u + 2 * v)) / 2 = u + v + w by ring,
      show (2 * w - (2 * u + 2 * v)) / 2 = -(u + v - w) by ring, Real.sin_neg]; ring
  have hs2 : 2 * Real.sin (v + w - u) * Real.sin (u - v + w) =
      Real.cos (2 * u - 2 * v) - Real.cos (2 * w) := by
    rw [Real.cos_sub_cos, show ((2 * u - 2 * v) + 2 * w) / 2 = u - v + w by ring,
      show ((2 * u - 2 * v) - 2 * w) / 2 = -(v + w - u) by ring, Real.sin_neg]; ring
  have h1 : Real.cos (2 * u + 2 * v) + Real.cos (2 * u - 2 * v) =
      2 * Real.cos (2 * u) * Real.cos (2 * v) := by
    rw [Real.cos_add_cos, show (2 * u + 2 * v + (2 * u - 2 * v)) / 2 = 2 * u by ring,
      show (2 * u + 2 * v - (2 * u - 2 * v)) / 2 = 2 * v by ring]
  have h2 : 2 * Real.cos (2 * u + 2 * v) * Real.cos (2 * u - 2 * v) =
      Real.cos (4 * u) + Real.cos (4 * v) := by
    rw [Real.cos_add_cos, show (4 * u + 4 * v) / 2 = 2 * u + 2 * v by ring,
      show (4 * u - 4 * v) / 2 = 2 * u - 2 * v by ring]
  have h3 : 2 * Real.cos (2 * w) ^ 2 = 1 + Real.cos (4 * w) := by
    conv_rhs => rw [show 4 * w = 2 * (2 * w) by ring, Real.cos_two_mul]
    ring
  symm
  calc 8 * Real.sin (u + v + w) * Real.sin (v + w - u) *
          Real.sin (u - v + w) * Real.sin (u + v - w)
      = 2 * (2 * Real.sin (u + v + w) * Real.sin (u + v - w)) *
          (2 * Real.sin (v + w - u) * Real.sin (u - v + w)) := by ring
    _ = - (2 * Real.cos (2 * w) ^ 2) +
          2 * Real.cos (2 * w) * (Real.cos (2 * u + 2 * v) + Real.cos (2 * u - 2 * v)) -
          2 * Real.cos (2 * u + 2 * v) * Real.cos (2 * u - 2 * v) := by rw [hs1, hs2]; ring
    _ = 4 * Real.cos (2 * u) * Real.cos (2 * v) * Real.cos (2 * w) -
          (1 + Real.cos (4 * u) + Real.cos (4 * v) + Real.cos (4 * w)) := by
          rw [h1, h2, h3]; ring

/-- Spherical law of cosines expression `cos α = (cos a - cos b cos c) / (sin b sin c)`. -/
def sphCosAngle (a b c : ℝ) : ℝ :=
  (Real.cos a - Real.cos b * Real.cos c) / (Real.sin b * Real.sin c)

/-- Dihedral / vertex angle `arccos (sphCosAngle a b c)`. -/
def sphAngle (a b c : ℝ) : ℝ := Real.arccos (sphCosAngle a b c)

/-- Spherical excess `α + β + γ - π` as a function of side lengths `(a, b, c)`. -/
def sphExcess (a b c : ℝ) : ℝ :=
  sphAngle a b c + sphAngle b c a + sphAngle c a b - Real.pi

lemma sphCosAngle_swap (a b c : ℝ) : sphCosAngle a c b = sphCosAngle a b c := by
  simp only [sphCosAngle, mul_comm]

lemma sphAngle_swap (a b c : ℝ) : sphAngle a c b = sphAngle a b c := by
  simp only [sphAngle, sphCosAngle_swap]

lemma sphExcess_perm_12 (a b c : ℝ) : sphExcess b a c = sphExcess a b c := by
  simp only [sphExcess, sphAngle_swap]; ring

lemma sphExcess_perm_cyc (a b c : ℝ) : sphExcess b c a = sphExcess a b c := by
  simp only [sphExcess]; ring

lemma one_add_sphCosAngle {a b c : ℝ} (hsb : Real.sin b ≠ 0) (hsc : Real.sin c ≠ 0) :
    1 + sphCosAngle a b c =
      2 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b + c) / 2 - a) / (Real.sin b * Real.sin c) := by
  set s := (a + b + c) / 2
  have h1 : Real.cos a - Real.cos (b + c) = 2 * Real.sin s * Real.sin (s - a) := by
    rw [Real.cos_sub_cos]
    have h1 : (a + (b + c)) / 2 = s := by dsimp [s]; ring
    have h2 : (a - (b + c)) / 2 = -(s - a) := by dsimp [s]; ring
    rw [h1, h2, Real.sin_neg]
    ring
  rw [sphCosAngle, one_add_div (mul_ne_zero hsb hsc)]
  rw [show Real.sin b * Real.sin c + (Real.cos a - Real.cos b * Real.cos c) =
      Real.cos a - Real.cos (b + c) by rw [Real.cos_add]; ring, h1]

lemma one_sub_sphCosAngle {a b c : ℝ} (hsb : Real.sin b ≠ 0) (hsc : Real.sin c ≠ 0) :
    1 - sphCosAngle a b c =
      2 * Real.sin ((a + b + c) / 2 - b) * Real.sin ((a + b + c) / 2 - c) / (Real.sin b * Real.sin c) := by
  set s := (a + b + c) / 2
  have h1 : Real.cos (b - c) - Real.cos a = 2 * Real.sin (s - b) * Real.sin (s - c) := by
    rw [Real.cos_sub_cos]
    have h1 : (b - c + a) / 2 = s - c := by dsimp [s]; ring
    have h2 : (b - c - a) / 2 = -(s - b) := by dsimp [s]; ring
    rw [h1, h2, Real.sin_neg]
    ring
  rw [sphCosAngle, one_sub_div (mul_ne_zero hsb hsc)]
  rw [show Real.sin b * Real.sin c - (Real.cos a - Real.cos b * Real.cos c) =
      Real.cos (b - c) - Real.cos a by rw [Real.cos_sub]; ring, h1]

/-- L'Huilier's theorem and strict bounds `0 < sphExcess a b c < 2 * π` for any valid spherical triangle. -/
theorem sphExcess_lhuilier {a b c : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc0 : 0 < c) (hcpi : c < Real.pi)
    (habc : a < b + c) (hbca : b < c + a) (hcab : c < a + b)
    (hper : a + b + c < 2 * Real.pi) :
    0 < sphExcess a b c ∧ sphExcess a b c < 2 * Real.pi ∧
      Real.tan (sphExcess a b c / 4) ^ 2 =
        let s := (a + b + c) / 2
        Real.tan (s / 2) * Real.tan ((s - a) / 2) *
          Real.tan ((s - b) / 2) * Real.tan ((s - c) / 2) := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (a + b + c) / 2 := ⟨_, rfl⟩
  have hs0 : 0 < s := by linarith only [hs_def, ha0, hb0, hc0]
  have hspi : s < Real.pi := by linarith only [hs_def, hper]
  have hsa0 : 0 < s - a := by linarith only [hs_def, habc]
  have hsapi : s - a < Real.pi := by linarith only [hs_def, ha0, hper]
  have hsb0 : 0 < s - b := by linarith only [hs_def, hbca]
  have hsbpi : s - b < Real.pi := by linarith only [hs_def, hb0, hper]
  have hsc0 : 0 < s - c := by linarith only [hs_def, hcab]
  have hscpi : s - c < Real.pi := by linarith only [hs_def, hc0, hper]
  have hsab : (a + b + c) / 2 = s := hs_def.symm
  have hsbc : (b + c + a) / 2 = s := by linarith only [hs_def]
  have hsca : (c + a + b) / 2 = s := by linarith only [hs_def]
  have hsin_a : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsin_b : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbpi
  have hsin_c : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc0 hcpi
  have hsin_s : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 hspi
  have hsin_sa : 0 < Real.sin (s - a) := Real.sin_pos_of_pos_of_lt_pi hsa0 hsapi
  have hsin_sb : 0 < Real.sin (s - b) := Real.sin_pos_of_pos_of_lt_pi hsb0 hsbpi
  have hsin_sc : 0 < Real.sin (s - c) := Real.sin_pos_of_pos_of_lt_pi hsc0 hscpi
  have hangle_bnd : ∀ {x y z : ℝ},
      0 < Real.sin y → 0 < Real.sin z →
      0 < 1 + sphCosAngle x y z → 0 < 1 - sphCosAngle x y z →
      -1 < sphCosAngle x y z ∧ sphCosAngle x y z < 1 ∧ 0 < sphAngle x y z ∧ sphAngle x y z < Real.pi := by
    intro x y z _ _ h1p h1m
    have hlo : -1 < sphCosAngle x y z := by linarith only [h1p]
    have hhi : sphCosAngle x y z < 1 := by linarith only [h1m]
    refine ⟨hlo, hhi, Real.arccos_pos.mpr hhi, Real.arccos_lt_pi.mpr hlo⟩
  have ha1p : 0 < 1 + sphCosAngle a b c := by
    rw [one_add_sphCosAngle hsin_b.ne' hsin_c.ne', hsab]
    exact div_pos (by positivity) (by positivity)
  have ha1m : 0 < 1 - sphCosAngle a b c := by
    rw [one_sub_sphCosAngle hsin_b.ne' hsin_c.ne', hsab]
    exact div_pos (by positivity) (by positivity)
  have hb1p : 0 < 1 + sphCosAngle b c a := by
    rw [one_add_sphCosAngle hsin_c.ne' hsin_a.ne', hsbc]
    exact div_pos (by positivity) (by positivity)
  have hb1m : 0 < 1 - sphCosAngle b c a := by
    rw [one_sub_sphCosAngle hsin_c.ne' hsin_a.ne', hsbc]
    exact div_pos (by positivity) (by positivity)
  have hc1p : 0 < 1 + sphCosAngle c a b := by
    rw [one_add_sphCosAngle hsin_a.ne' hsin_b.ne', hsca]
    exact div_pos (by positivity) (by positivity)
  have hc1m : 0 < 1 - sphCosAngle c a b := by
    rw [one_sub_sphCosAngle hsin_a.ne' hsin_b.ne', hsca]
    exact div_pos (by positivity) (by positivity)
  obtain ⟨ha_lo, ha_hi, hα0, hαpi⟩ := hangle_bnd hsin_b hsin_c ha1p ha1m
  obtain ⟨hb_lo, hb_hi, hβ0, hβpi⟩ := hangle_bnd hsin_c hsin_a hb1p hb1m
  obtain ⟨hc_lo, hc_hi, hγ0, hγpi⟩ := hangle_bnd hsin_a hsin_b hc1p hc1m
  obtain ⟨α, hα_def⟩ : ∃ α : ℝ, α = sphAngle a b c := ⟨_, rfl⟩
  obtain ⟨β, hβ_def⟩ : ∃ β : ℝ, β = sphAngle b c a := ⟨_, rfl⟩
  obtain ⟨γ, hγ_def⟩ : ∃ γ : ℝ, γ = sphAngle c a b := ⟨_, rfl⟩
  rw [← hα_def] at hα0 hαpi
  rw [← hβ_def] at hβ0 hβpi
  rw [← hγ_def] at hγ0 hγpi
  have hcosα : Real.cos α = sphCosAngle a b c := by
    rw [hα_def]; exact Real.cos_arccos ha_lo.le ha_hi.le
  have hcosβ : Real.cos β = sphCosAngle b c a := by
    rw [hβ_def]; exact Real.cos_arccos hb_lo.le hb_hi.le
  have hcosγ : Real.cos γ = sphCosAngle c a b := by
    rw [hγ_def]; exact Real.cos_arccos hc_lo.le hc_hi.le
  obtain ⟨P₀, hP0_def⟩ : ∃ P₀ : ℝ, P₀ = √(Real.sin s) := ⟨_, rfl⟩
  obtain ⟨P₁, hP1_def⟩ : ∃ P₁ : ℝ, P₁ = √(Real.sin (s - a)) := ⟨_, rfl⟩
  obtain ⟨P₂, hP2_def⟩ : ∃ P₂ : ℝ, P₂ = √(Real.sin (s - b)) := ⟨_, rfl⟩
  obtain ⟨P₃, hP3_def⟩ : ∃ P₃ : ℝ, P₃ = √(Real.sin (s - c)) := ⟨_, rfl⟩
  obtain ⟨Qa, hQa_def⟩ : ∃ Qa : ℝ, Qa = √(Real.sin a) := ⟨_, rfl⟩
  obtain ⟨Qb, hQb_def⟩ : ∃ Qb : ℝ, Qb = √(Real.sin b) := ⟨_, rfl⟩
  obtain ⟨Qc, hQc_def⟩ : ∃ Qc : ℝ, Qc = √(Real.sin c) := ⟨_, rfl⟩
  have hP0_pos : 0 < P₀ := hP0_def ▸ Real.sqrt_pos.mpr hsin_s
  have hP1_pos : 0 < P₁ := hP1_def ▸ Real.sqrt_pos.mpr hsin_sa
  have hP2_pos : 0 < P₂ := hP2_def ▸ Real.sqrt_pos.mpr hsin_sb
  have hP3_pos : 0 < P₃ := hP3_def ▸ Real.sqrt_pos.mpr hsin_sc
  have hQa_pos : 0 < Qa := hQa_def ▸ Real.sqrt_pos.mpr hsin_a
  have hQb_pos : 0 < Qb := hQb_def ▸ Real.sqrt_pos.mpr hsin_b
  have hQc_pos : 0 < Qc := hQc_def ▸ Real.sqrt_pos.mpr hsin_c
  have hP0_sq : P₀ ^ 2 = Real.sin s := hP0_def ▸ Real.sq_sqrt hsin_s.le
  have hP1_sq : P₁ ^ 2 = Real.sin (s - a) := hP1_def ▸ Real.sq_sqrt hsin_sa.le
  have hP2_sq : P₂ ^ 2 = Real.sin (s - b) := hP2_def ▸ Real.sq_sqrt hsin_sb.le
  have hP3_sq : P₃ ^ 2 = Real.sin (s - c) := hP3_def ▸ Real.sq_sqrt hsin_sc.le
  have hQa_sq : Qa ^ 2 = Real.sin a := hQa_def ▸ Real.sq_sqrt hsin_a.le
  have hQb_sq : Qb ^ 2 = Real.sin b := hQb_def ▸ Real.sq_sqrt hsin_b.le
  have hQc_sq : Qc ^ 2 = Real.sin c := hQc_def ▸ Real.sq_sqrt hsin_c.le
  have hcos_half : ∀ {θ N D : ℝ}, 0 < θ → θ < Real.pi → 0 ≤ N → 0 < D →
      (1 + Real.cos θ) / 2 = N ^ 2 / D ^ 2 → Real.cos (θ / 2) = N / D := by
    intro θ N D h0 hpi hN hD heq
    have hcos_pos : 0 < Real.cos (θ / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith only [h0, Real.pi_pos], by linarith only [hpi]⟩
    have hsq : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
      conv_rhs => rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
      ring
    rw [heq, ← div_pow] at hsq
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hcos_pos.le, Real.sqrt_sq (div_nonneg hN hD.le)] at this
  have hsin_half : ∀ {θ N D : ℝ}, 0 < θ → θ < Real.pi → 0 ≤ N → 0 < D →
      (1 - Real.cos θ) / 2 = N ^ 2 / D ^ 2 → Real.sin (θ / 2) = N / D := by
    intro θ N D h0 hpi hN hD heq
    have hsin_pos : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith only [h0]) (by linarith only [hpi, Real.pi_pos])
    have hsq : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
      conv_rhs => rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
      linarith only [Real.sin_sq_add_cos_sq (θ / 2)]
    rw [heq, ← div_pow] at hsq
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hsin_pos.le, Real.sqrt_sq (div_nonneg hN hD.le)] at this
  have hca : Real.cos (α / 2) = (P₀ * P₁) / (Qb * Qc) := by
    refine hcos_half hα0 hαpi (mul_pos hP0_pos hP1_pos).le (mul_pos hQb_pos hQc_pos) ?_
    rw [hcosα, one_add_sphCosAngle hsin_b.ne' hsin_c.ne', hsab]
    rw [mul_pow, mul_pow, hP0_sq, hP1_sq, hQb_sq, hQc_sq]; ring
  have hsa : Real.sin (α / 2) = (P₂ * P₃) / (Qb * Qc) := by
    refine hsin_half hα0 hαpi (mul_pos hP2_pos hP3_pos).le (mul_pos hQb_pos hQc_pos) ?_
    rw [hcosα, one_sub_sphCosAngle hsin_b.ne' hsin_c.ne', hsab]
    rw [mul_pow, mul_pow, hP2_sq, hP3_sq, hQb_sq, hQc_sq]; ring
  have hcb : Real.cos (β / 2) = (P₀ * P₂) / (Qc * Qa) := by
    refine hcos_half hβ0 hβpi (mul_pos hP0_pos hP2_pos).le (mul_pos hQc_pos hQa_pos) ?_
    rw [hcosβ, one_add_sphCosAngle hsin_c.ne' hsin_a.ne', hsbc]
    rw [mul_pow, mul_pow, hP0_sq, hP2_sq, hQc_sq, hQa_sq]; ring
  have hsb : Real.sin (β / 2) = (P₁ * P₃) / (Qc * Qa) := by
    refine hsin_half hβ0 hβpi (mul_pos hP1_pos hP3_pos).le (mul_pos hQc_pos hQa_pos) ?_
    rw [hcosβ, one_sub_sphCosAngle hsin_c.ne' hsin_a.ne', hsbc]
    rw [mul_pow, mul_pow, hP1_sq, hP3_sq, hQc_sq, hQa_sq]; ring
  have hcc : Real.cos (γ / 2) = (P₀ * P₃) / (Qa * Qb) := by
    refine hcos_half hγ0 hγpi (mul_pos hP0_pos hP3_pos).le (mul_pos hQa_pos hQb_pos) ?_
    rw [hcosγ, one_add_sphCosAngle hsin_a.ne' hsin_b.ne', hsca]
    rw [mul_pow, mul_pow, hP0_sq, hP3_sq, hQa_sq, hQb_sq]; ring
  have hsc : Real.sin (γ / 2) = (P₁ * P₂) / (Qa * Qb) := by
    refine hsin_half hγ0 hγpi (mul_pos hP1_pos hP2_pos).le (mul_pos hQa_pos hQb_pos) ?_
    rw [hcosγ, one_sub_sphCosAngle hsin_a.ne' hsin_b.ne', hsca]
    rw [mul_pow, mul_pow, hP1_sq, hP2_sq, hQa_sq, hQb_sq]; ring
  obtain ⟨E, hE_def⟩ : ∃ E : ℝ, E = sphExcess a b c := ⟨_, rfl⟩
  have hE_eq : E = α + β + γ - Real.pi := by
    rw [hE_def, hα_def, hβ_def, hγ_def]; rfl
  have hE_half : E / 2 = ((α + β) / 2 + γ / 2) - Real.pi / 2 := by linarith only [hE_eq]
  have hsin_E2_trig : Real.sin (E / 2) =
      Real.sin ((α + β) / 2) * Real.sin (γ / 2) -
        Real.cos ((α + β) / 2) * Real.cos (γ / 2) := by
    rw [hE_half, Real.sin_sub_pi_div_two, Real.cos_add]; ring
  have hcos_E2_trig : Real.cos (E / 2) =
      Real.cos ((α + β) / 2) * Real.sin (γ / 2) +
        Real.sin ((α + β) / 2) * Real.cos (γ / 2) := by
    rw [hE_half, Real.cos_sub_pi_div_two, Real.sin_add]; ring
  have hsin_ab : Real.sin ((α + β) / 2) =
      (Real.sin (s - b) + Real.sin (s - a)) * P₀ * P₃ / (Qa * Qb * Qc ^ 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.sin_add, hsa, hsb, hca, hcb]
    rw [← hP1_sq, ← hP2_sq]
    field_simp [hQa_pos.ne', hQb_pos.ne', hQc_pos.ne'] <;> ring
  have hcos_ab : Real.cos ((α + β) / 2) =
      (Real.sin s - Real.sin (s - c)) * P₁ * P₂ / (Qa * Qb * Qc ^ 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.cos_add, hsa, hsb, hca, hcb]
    rw [← hP0_sq, ← hP3_sq]
    field_simp [hQa_pos.ne', hQb_pos.ne', hQc_pos.ne'] <;> ring
  have hsin_abc_pos : 0 < Real.sin a * Real.sin b * Real.sin c := by positivity
  have hsin_E2 : Real.sin (E / 2) =
      4 * Real.sin (a / 2) * Real.sin (b / 2) * Real.sin (c / 2) * (P₀ * P₁ * P₂ * P₃) /
        (Real.sin a * Real.sin b * Real.sin c) := by
    rw [hsin_E2_trig, hsin_ab, hcos_ab, hsc, hcc]
    have hden : (Qa * Qb * Qc ^ 2) * (Qa * Qb) = Real.sin a * Real.sin b * Real.sin c := by
      rw [← hQa_sq, ← hQb_sq, ← hQc_sq]; ring
    have hnum_eq := lhuilier_trig_sin_part (a / 2) (b / 2) (c / 2)
    have hs_eq : a / 2 + b / 2 + c / 2 = s := by linarith only [hs_def]
    dsimp only at hnum_eq
    rw [hs_eq] at hnum_eq
    rw [show s - 2 * (a / 2) = s - a by ring, show s - 2 * (b / 2) = s - b by ring,
      show s - 2 * (c / 2) = s - c by ring] at hnum_eq
    calc
      (Real.sin (s - b) + Real.sin (s - a)) * P₀ * P₃ / (Qa * Qb * Qc ^ 2) * (P₁ * P₂ / (Qa * Qb)) -
          (Real.sin s - Real.sin (s - c)) * P₁ * P₂ / (Qa * Qb * Qc ^ 2) * (P₀ * P₃ / (Qa * Qb))
          = (Real.sin (s - b) + Real.sin (s - a) - Real.sin s + Real.sin (s - c)) *
              (P₀ * P₁ * P₂ * P₃) / ((Qa * Qb * Qc ^ 2) * (Qa * Qb)) := by ring
      _ = 4 * Real.sin (a / 2) * Real.sin (b / 2) * Real.sin (c / 2) * (P₀ * P₁ * P₂ * P₃) /
            (Real.sin a * Real.sin b * Real.sin c) := by rw [hnum_eq, hden]
  have hsa2 : 0 < Real.sin (a / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [ha0]) (by linarith only [hapi, Real.pi_pos])
  have hsb2 : 0 < Real.sin (b / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hb0]) (by linarith only [hbpi, Real.pi_pos])
  have hsc2 : 0 < Real.sin (c / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hc0]) (by linarith only [hcpi, Real.pi_pos])
  have hca2 : 0 < Real.cos (a / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [ha0, Real.pi_pos], by linarith only [hapi]⟩
  have hcb2 : 0 < Real.cos (b / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hb0, Real.pi_pos], by linarith only [hbpi]⟩
  have hcc2 : 0 < Real.cos (c / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hc0, Real.pi_pos], by linarith only [hcpi]⟩
  have hcos_E2 : Real.cos (E / 2) =
      (1 + Real.cos a + Real.cos b + Real.cos c) /
        (4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2)) := by
    have ha_s : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
      conv_lhs => rw [show a = 2 * (a / 2) by ring, Real.sin_two_mul]
    have hb_s : Real.sin b = 2 * Real.sin (b / 2) * Real.cos (b / 2) := by
      conv_lhs => rw [show b = 2 * (b / 2) by ring, Real.sin_two_mul]
    have hc_s : Real.sin c = 2 * Real.sin (c / 2) * Real.cos (c / 2) := by
      conv_lhs => rw [show c = 2 * (c / 2) by ring, Real.sin_two_mul]
    have hnum_eq := lhuilier_trig_cos_part (a / 2) (b / 2) (c / 2)
    have hs_eq : a / 2 + b / 2 + c / 2 = s := by linarith only [hs_def]
    dsimp only at hnum_eq
    rw [hs_eq] at hnum_eq
    rw [show s - 2 * (a / 2) = s - a by ring, show s - 2 * (b / 2) = s - b by ring,
      show s - 2 * (c / 2) = s - c by ring,
      show 2 * (a / 2) = a by ring, show 2 * (b / 2) = b by ring,
      show 2 * (c / 2) = c by ring] at hnum_eq
    rw [hcos_E2_trig, hcos_ab, hsin_ab, hsc, hcc]
    have hden : (Qa * Qb * Qc ^ 2) * (Qa * Qb) = Real.sin a * Real.sin b * Real.sin c := by
      rw [← hQa_sq, ← hQb_sq, ← hQc_sq]; ring
    calc
      (Real.sin s - Real.sin (s - c)) * P₁ * P₂ / (Qa * Qb * Qc ^ 2) * (P₁ * P₂ / (Qa * Qb)) +
          (Real.sin (s - b) + Real.sin (s - a)) * P₀ * P₃ / (Qa * Qb * Qc ^ 2) * (P₀ * P₃ / (Qa * Qb))
          = ((Real.sin s - Real.sin (s - c)) * P₁ ^ 2 * P₂ ^ 2 +
              (Real.sin (s - b) + Real.sin (s - a)) * P₀ ^ 2 * P₃ ^ 2) /
              ((Qa * Qb * Qc ^ 2) * (Qa * Qb)) := by ring
      _ = ((Real.sin s - Real.sin (s - c)) * Real.sin (s - a) * Real.sin (s - b) +
              (Real.sin (s - b) + Real.sin (s - a)) * Real.sin s * Real.sin (s - c)) /
            (Real.sin a * Real.sin b * Real.sin c) := by
          rw [hP0_sq, hP1_sq, hP2_sq, hP3_sq, hden]
      _ = (2 * Real.sin (a / 2) * Real.sin (b / 2) * Real.sin (c / 2) *
              (1 + Real.cos a + Real.cos b + Real.cos c)) /
            ((2 * Real.sin (a / 2) * Real.cos (a / 2)) *
              (2 * Real.sin (b / 2) * Real.cos (b / 2)) *
              (2 * Real.sin (c / 2) * Real.cos (c / 2))) := by
          rw [hnum_eq, ha_s, hb_s, hc_s]
      _ = (1 + Real.cos a + Real.cos b + Real.cos c) /
            (4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2)) := by
          field_simp [hsa2.ne', hsb2.ne', hsc2.ne', hca2.ne', hcb2.ne', hcc2.ne'] <;> ring
  have hsin_E2_pos : 0 < Real.sin (E / 2) := by
    rw [hsin_E2]
    exact div_pos (by positivity) hsin_abc_pos
  have hE_lt : E < 2 * Real.pi := by linarith only [hE_eq, hαpi, hβpi, hγpi]
  have hE_pos : 0 < E := by
    by_contra hle
    push Not at hle
    have hlo : -Real.pi ≤ E / 2 := by linarith only [hE_eq, hα0, hβ0, hγ0, Real.pi_pos]
    have hnonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith only [hle]) hlo
    linarith only [hsin_E2_pos, hnonpos]
  rw [← hE_def]
  refine ⟨hE_pos, hE_lt, ?_⟩
  dsimp only
  rw [← hs_def]
  have hdenom_pos : 0 < 4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) := by positivity
  have hplus_eq := lhuilier_trig_plus (a / 4) (b / 4) (c / 4)
  have hminus_eq := lhuilier_trig_minus (a / 4) (b / 4) (c / 4)
  simp only [show 4 * (a / 4) = a by ring, show 4 * (b / 4) = b by ring,
    show 4 * (c / 4) = c by ring, show 2 * (a / 4) = a / 2 by ring,
    show 2 * (b / 4) = b / 2 by ring, show 2 * (c / 4) = c / 2 by ring] at hplus_eq hminus_eq
  have h1s : a / 4 + b / 4 + c / 4 = s / 2 := by linarith only [hs_def]
  have h2s : b / 4 + c / 4 - a / 4 = (s - a) / 2 := by linarith only [hs_def]
  have h3s : a / 4 - b / 4 + c / 4 = (s - b) / 2 := by linarith only [hs_def]
  have h4s : a / 4 + b / 4 - c / 4 = (s - c) / 2 := by linarith only [hs_def]
  rw [h1s, h2s, h3s, h4s] at hplus_eq hminus_eq
  have hcs2 : 0 < Real.cos (s / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hs0, Real.pi_pos], by linarith only [hspi]⟩
  have hcsa2 : 0 < Real.cos ((s - a) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hsa0, Real.pi_pos], by linarith only [hsapi]⟩
  have hcsb2 : 0 < Real.cos ((s - b) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hsb0, Real.pi_pos], by linarith only [hsbpi]⟩
  have hcsc2 : 0 < Real.cos ((s - c) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hsc0, Real.pi_pos], by linarith only [hscpi]⟩
  have hEcos_ne : 1 + Real.cos (2 * (E / 4)) ≠ 0 := by
    rw [show 2 * (E / 4) = E / 2 by ring, hcos_E2]
    have hnum_pos : 0 < 4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) +
        (1 + Real.cos a + Real.cos b + Real.cos c) := by
      have : 4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) +
          (1 + Real.cos a + Real.cos b + Real.cos c) =
          1 + Real.cos a + Real.cos b + Real.cos c +
            4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) := by ring
      rw [this, hplus_eq]; positivity
    rw [one_add_div hdenom_pos.ne']
    exact div_ne_zero hnum_pos.ne' hdenom_pos.ne'
  rw [tan_sq_half_eq_one_sub_cos_div_one_add_cos (E / 4) hEcos_ne,
    show 2 * (E / 4) = E / 2 by ring, hcos_E2]
  rw [one_sub_div hdenom_pos.ne', one_add_div hdenom_pos.ne', div_div_div_cancel_right₀ hdenom_pos.ne']
  rw [show 4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) -
      (1 + Real.cos a + Real.cos b + Real.cos c) =
      8 * Real.sin (s / 2) * Real.sin ((s - a) / 2) *
        Real.sin ((s - b) / 2) * Real.sin ((s - c) / 2) by linarith only [hminus_eq]]
  rw [show 4 * Real.cos (a / 2) * Real.cos (b / 2) * Real.cos (c / 2) +
      (1 + Real.cos a + Real.cos b + Real.cos c) =
      8 * Real.cos (s / 2) * Real.cos ((s - a) / 2) *
        Real.cos ((s - b) / 2) * Real.cos ((s - c) / 2) by linarith only [hplus_eq]]
  simp only [Real.tan_eq_sin_div_cos]
  field_simp [hcs2.ne', hcsa2.ne', hcsb2.ne', hcsc2.ne'] <;> ring

private lemma tan_add_of_cos_ne_zero {x y : ℝ}
    (hx : Real.cos x ≠ 0) (hy : Real.cos y ≠ 0) (hxy : Real.cos (x + y) ≠ 0) :
    Real.tan (x + y) = (Real.tan x + Real.tan y) / (1 - Real.tan x * Real.tan y) := by
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
    Real.sin_add, Real.cos_add]
  have hden : 1 - (Real.sin x / Real.cos x) * (Real.sin y / Real.cos y) ≠ 0 := by
    intro h; apply hxy; rw [Real.cos_add]
    have hmul := congrArg (· * (Real.cos x * Real.cos y)) h
    field_simp [hx, hy] at hmul
    linarith
  field_simp [hx, hy, hden]

private lemma tan_sub_of_cos_ne_zero {x y : ℝ}
    (hx : Real.cos x ≠ 0) (hy : Real.cos y ≠ 0) (hxy : Real.cos (x - y) ≠ 0) :
    Real.tan (x - y) = (Real.tan x - Real.tan y) / (1 + Real.tan x * Real.tan y) := by
  have := tan_add_of_cos_ne_zero (x := x) (y := -y) hx
    (by simpa [Real.cos_neg] using hy) (by simpa [sub_eq_add_neg] using hxy)
  simpa [sub_eq_add_neg, Real.tan_neg, mul_neg] using this

lemma tan_sub_mul_tan_add_le_tan_sq {u δ : ℝ}
    (hu0 : 0 ≤ u) (hδ_abs : |δ| ≤ u) (hupi : u < Real.pi / 4) :
    Real.tan (u - δ) * Real.tan (u + δ) ≤ Real.tan u ^ 2 := by
  have h1 : -(Real.pi / 2) < u - δ ∧ u - δ < Real.pi / 2 := by
    have := abs_le.mp hδ_abs; constructor <;> linarith
  have h2 : -(Real.pi / 2) < u + δ ∧ u + δ < Real.pi / 2 := by
    have := abs_le.mp hδ_abs; constructor <;> linarith
  have hup : -(Real.pi / 2) < u ∧ u < Real.pi / 2 := ⟨by linarith, by linarith⟩
  have hc1 : 0 < Real.cos (u - δ) := Real.cos_pos_of_mem_Ioo h1
  have hc2 : 0 < Real.cos (u + δ) := Real.cos_pos_of_mem_Ioo h2
  have hcu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo hup
  have hc2u : 0 ≤ Real.cos (2 * u) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h2δ_le : Real.cos (2 * δ) ≤ 1 := Real.cos_le_one _
  have hprod_sin : Real.sin (u - δ) * Real.sin (u + δ) =
      (Real.cos (2 * δ) - Real.cos (2 * u)) / 2 := by
    have hsub := Real.cos_sub (u + δ) (u - δ)
    have hadd := Real.cos_add (u + δ) (u - δ)
    rw [show (u + δ) - (u - δ) = 2 * δ by ring] at hsub
    rw [show (u + δ) + (u - δ) = 2 * u by ring] at hadd
    linarith
  have hprod_cos : Real.cos (u - δ) * Real.cos (u + δ) =
      (Real.cos (2 * δ) + Real.cos (2 * u)) / 2 := by
    have hsub := Real.cos_sub (u + δ) (u - δ)
    have hadd := Real.cos_add (u + δ) (u - δ)
    rw [show (u + δ) - (u - δ) = 2 * δ by ring] at hsub
    rw [show (u + δ) + (u - δ) = 2 * u by ring] at hadd
    linarith
  have htan_sq_u : Real.tan u ^ 2 = (1 - Real.cos (2 * u)) / (1 + Real.cos (2 * u)) :=
    tan_sq_half_eq_one_sub_cos_div_one_add_cos u (by linarith)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, div_mul_div_comm,
    hprod_sin, hprod_cos, htan_sq_u]
  have hden1 : 0 < (Real.cos (2 * δ) + Real.cos (2 * u)) / 2 := by
    rw [← hprod_cos]; positivity
  have hden2 : 0 < 1 + Real.cos (2 * u) := by linarith
  rw [div_le_div_iff₀ (by positivity) hden2]
  nlinarith [h2δ_le, hc2u]

/-- Symmetrizing two sides `(a, b) ↦ (m, m)` (`m = (a+b)/2`) holding base `d` fixed increases spherical excess. -/
theorem sphExcess_le_isosceles {a b d : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hd0 : 0 < d) (hdpi : d < Real.pi)
    (habd : d < a + b) (hbad : a < b + d) (habc : b < d + a)
    (hper : a + b + d < 2 * Real.pi) :
    let m := (a + b) / 2
    sphExcess a b d ≤ sphExcess m m d := by
  intro m
  have hm0 : 0 < m := by dsimp [m]; linarith
  have hmpi : m < Real.pi := by dsimp [m]; linarith
  have hdm : d < m + m := by dsimp [m]; linarith
  have hmd1 : m < m + d := by linarith
  have hmd2 : m < d + m := by linarith
  have hmper : m + m + d < 2 * Real.pi := by dsimp [m]; linarith
  obtain ⟨hE1_pos, hE1_lt, hL1⟩ := sphExcess_lhuilier ha0 hapi hb0 hbpi hd0 hdpi hbad habc habd hper
  obtain ⟨hE2_pos, hE2_lt, hL2⟩ := sphExcess_lhuilier hm0 hmpi hm0 hmpi hd0 hdpi hmd1 hmd2 hdm hmper
  dsimp only at hL1 hL2
  have htan_sq_le : Real.tan (sphExcess a b d / 4) ^ 2 ≤ Real.tan (sphExcess m m d / 4) ^ 2 := by
    rw [hL1, hL2]
    set s := (a + b + d) / 2
    have hs_eq : (m + m + d) / 2 = s := by dsimp [m, s]; ring
    rw [hs_eq]
    have ht0 : 0 < Real.tan (s / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by dsimp [s]; linarith) (by dsimp [s]; linarith)
    have ht1 : 0 < Real.tan ((s - d) / 2) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by dsimp [s]; linarith) (by dsimp [s]; linarith)
    have hmul := tan_sub_mul_tan_add_le_tan_sq (u := d / 4) (δ := (a - b) / 4)
      (by linarith) (by rw [abs_le]; constructor <;> linarith) (by linarith [hdpi])
    have h1 : (s - a) / 2 = d / 4 - (a - b) / 4 := by dsimp [s]; ring
    have h2 : (s - b) / 2 = d / 4 + (a - b) / 4 := by dsimp [s]; ring
    have h3 : (s - m) / 2 = d / 4 := by dsimp [s, m]; ring
    rw [h1, h2, h3]
    calc Real.tan (s / 2) * Real.tan (d / 4 - (a - b) / 4) *
            Real.tan (d / 4 + (a - b) / 4) * Real.tan ((s - d) / 2)
        = Real.tan (s / 2) * Real.tan ((s - d) / 2) *
            (Real.tan (d / 4 - (a - b) / 4) * Real.tan (d / 4 + (a - b) / 4)) := by ring
      _ ≤ Real.tan (s / 2) * Real.tan ((s - d) / 2) * Real.tan (d / 4) ^ 2 := by
          gcongr
      _ = Real.tan (s / 2) * Real.tan (d / 4) * Real.tan (d / 4) * Real.tan ((s - d) / 2) := by ring
  have hpos1 : 0 ≤ Real.tan (sphExcess a b d / 4) :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)).le
  have hpos2 : 0 ≤ Real.tan (sphExcess m m d / 4) :=
    (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)).le
  have htan_le : Real.tan (sphExcess a b d / 4) ≤ Real.tan (sphExcess m m d / 4) := by
    nlinarith [htan_sq_le, hpos1, hpos2]
  have hmono := Real.strictMonoOn_tan.le_iff_le
    (⟨by linarith, by linarith⟩ : sphExcess a b d / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (⟨by linarith, by linarith⟩ : sphExcess m m d / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
  linarith [hmono.mp htan_le]

/-- Rhombus triangle bound: for equal legs `m ∈ (0, π / 2)` and base `d ∈ (0, 2 m)`, twice the
excess is bounded by the spherical square excess `4 * arccos (-tan(m / 2)^2) - 2 * π`. -/
theorem sphExcess_isosceles_le_square {m d : ℝ} (hm0 : 0 < m) (hmpi : m < Real.pi / 2)
    (hd0 : 0 < d) (hd2m : d < 2 * m) :
    2 * sphExcess m m d ≤ 4 * Real.arccos (-Real.tan (m / 2) ^ 2) - 2 * Real.pi := by
  have hmpi' : m < Real.pi := by linarith only [hmpi, Real.pi_pos]
  have hdpi : d < Real.pi := by linarith only [hd2m, hmpi, Real.pi_pos]
  have hmper : m + m + d < 2 * Real.pi := by linarith only [hd2m, hmpi, Real.pi_pos]
  obtain ⟨hE0, hElt, hL⟩ := sphExcess_lhuilier hm0 hmpi' hm0 hmpi' hd0 hdpi
    (by linarith only [hd0]) (by linarith only [hd0]) (by linarith only [hd2m]) hmper
  dsimp only at hL
  obtain ⟨k, hk_def⟩ : ∃ k : ℝ, k = Real.tan (m / 2) := ⟨_, rfl⟩
  obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = Real.tan (d / 4) := ⟨_, rfl⟩
  have hk0 : 0 < k :=
    hk_def ▸ Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith only [hm0]) (by linarith only [hmpi, Real.pi_pos])
  have hk1 : k < 1 := by
    have : Real.tan (m / 2) < Real.tan (Real.pi / 4) :=
      Real.strictMonoOn_tan ⟨by linarith only [hm0, Real.pi_pos], by linarith only [hmpi, Real.pi_pos]⟩
        ⟨by linarith only [Real.pi_pos], by linarith only [Real.pi_pos]⟩ (by linarith only [hmpi])
    rw [Real.tan_pi_div_four, ← hk_def] at this; exact this
  have hx0 : 0 < x :=
    hx_def ▸ Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith only [hd0]) (by linarith only [hd2m, hmpi, Real.pi_pos])
  have hxk : x < k := by
    rw [hk_def, hx_def]
    exact Real.strictMonoOn_tan ⟨by linarith only [hd0, Real.pi_pos], by linarith only [hd2m, hmpi, Real.pi_pos]⟩
      ⟨by linarith only [hm0, Real.pi_pos], by linarith only [hmpi, Real.pi_pos]⟩ (by linarith only [hd2m])
  have hk_sq1 : k ^ 2 < 1 := by nlinarith only [hk0, hk1]
  have hkx_lt1 : k * x < 1 := by nlinarith only [hk0, hk1, hx0, hxk]
  have hkx_ne : 1 - k * x ≠ 0 := by linarith only [hkx_lt1]
  have hkx_p_ne : 1 + k * x ≠ 0 := by nlinarith only [hk0, hx0]
  have hkx_sq1 : (k * x) ^ 2 < 1 := by nlinarith only [hkx_lt1, mul_pos hk0 hx0]
  have hden_pos : 0 < 1 - k ^ 2 * x ^ 2 := by
    linarith only [show (k * x) ^ 2 = k ^ 2 * x ^ 2 by ring, hkx_sq1]
  have hcm : Real.cos (m / 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith only [hm0, Real.pi_pos], by linarith only [hmpi, Real.pi_pos]⟩).ne'
  have hcd : Real.cos (d / 4) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith only [hd0, Real.pi_pos], by linarith only [hd2m, hmpi, Real.pi_pos]⟩).ne'
  have hcadd : Real.cos (m / 2 + d / 4) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith only [hm0, hd0, Real.pi_pos], by linarith only [hd2m, hmpi, Real.pi_pos]⟩).ne'
  have hcsub : Real.cos (m / 2 - d / 4) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith only [hd2m, hmpi, Real.pi_pos], by linarith only [hm0, hmpi, hd0, Real.pi_pos]⟩).ne'
  have htan_add : Real.tan ((m + d / 2) / 2) = (k + x) / (1 - k * x) := by
    rw [show (m + d / 2) / 2 = m / 2 + d / 4 by ring, hk_def, hx_def]
    exact tan_add_of_cos_ne_zero hcm hcd hcadd
  have htan_sub : Real.tan ((m - d / 2) / 2) = (k - x) / (1 + k * x) := by
    rw [show (m - d / 2) / 2 = m / 2 - d / 4 by ring, hk_def, hx_def]
    exact tan_sub_of_cos_ne_zero hcm hcd hcsub
  have hE_tan_sq : Real.tan (sphExcess m m d / 4) ^ 2 = x ^ 2 * (k ^ 2 - x ^ 2) / (1 - k ^ 2 * x ^ 2) := by
    rw [hL]
    have hs1 : (m + m + d) / 2 / 2 = (m + d / 2) / 2 := by ring
    have hs2 : ((m + m + d) / 2 - m) / 2 = d / 4 := by ring
    have hs3 : ((m + m + d) / 2 - d) / 2 = (m - d / 2) / 2 := by ring
    rw [hs1, hs2, hs3, htan_add, htan_sub, ← hx_def]
    field_simp [hkx_ne, hkx_p_ne, hden_pos.ne'] <;> ring
  have hk4 : k ^ 4 < 1 := by
    have hk4_eq : k ^ 4 = k ^ 2 * k ^ 2 := by ring
    rw [hk4_eq]; nlinarith only [sq_nonneg k, hk_sq1]
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = √(1 - k ^ 4) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr_def ▸ Real.sqrt_pos.mpr (by linarith only [hk4])
  have hr_sq : r ^ 2 = 1 - k ^ 4 := hr_def ▸ Real.sq_sqrt (by linarith only [hk4])
  have hr1 : r < 1 := by
    have hk4_pos : 0 < k ^ 4 := pow_pos hk0 4
    nlinarith only [hr_sq, hk4_pos, hr0]
  obtain ⟨x₀, hx₀_def⟩ : ∃ x₀ : ℝ, x₀ = (1 - r) / k ^ 2 := ⟨_, rfl⟩
  have hx₀_pos : 0 < x₀ := hx₀_def ▸ div_pos (by linarith only [hr1]) (sq_pos_of_pos hk0)
  have hquad : k ^ 2 * x₀ ^ 2 - 2 * x₀ + k ^ 2 = 0 := by
    have hkx₀ : k ^ 2 * x₀ = 1 - r := by rw [hx₀_def]; exact mul_div_cancel₀ _ (sq_pos_of_pos hk0).ne'
    have h1 : (k ^ 2 * x₀ - 1) ^ 2 = r ^ 2 := by rw [hkx₀]; ring
    rw [hr_sq] at h1
    have h2 : k ^ 2 * (k ^ 2 * x₀ ^ 2 - 2 * x₀ + k ^ 2) = 0 := by linarith only [h1]
    exact (mul_eq_zero.mp h2).resolve_left (sq_pos_of_pos hk0).ne'
  have htan_le_x₀ : Real.tan (sphExcess m m d / 4) ≤ x₀ := by
    have hsq : Real.tan (sphExcess m m d / 4) ^ 2 ≤ x₀ ^ 2 := by
      rw [hE_tan_sq, div_le_iff₀ hden_pos]
      have hid : (1 - k ^ 2 * x ^ 2) * x₀ ^ 2 - x ^ 2 * (k ^ 2 - x ^ 2) = (x ^ 2 - x₀) ^ 2 := by
        linear_combination (-x ^ 2) * hquad
      nlinarith only [hid, sq_nonneg (x ^ 2 - x₀)]
    have hpos_e : 0 ≤ Real.tan (sphExcess m m d / 4) :=
      (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith only [hE0]) (by linarith only [hElt])).le
    nlinarith only [hsq, hpos_e, hx₀_pos]
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : ℝ, ψ = Real.arccos (-k ^ 2) - Real.pi / 2 := ⟨_, rfl⟩
  have hk2_bnd : -1 < -k ^ 2 ∧ -k ^ 2 < 0 := ⟨by linarith only [hk_sq1], by nlinarith only [hk0]⟩
  have hψ0 : 0 < ψ := by
    have : Real.pi / 2 < Real.arccos (-k ^ 2) := by
      rw [← Real.arccos_zero]
      exact Real.strictAntiOn_arccos ⟨by linarith only [hk2_bnd.1], by linarith only [hk2_bnd.2]⟩
        ⟨by norm_num, by norm_num⟩ hk2_bnd.2
    linarith only [hψ_def, this]
  have hψpi : ψ < Real.pi / 2 := by
    have : Real.arccos (-k ^ 2) < Real.pi := Real.arccos_lt_pi.mpr hk2_bnd.1
    linarith only [hψ_def, this]
  have hsinψ : Real.sin ψ = k ^ 2 := by
    rw [hψ_def, Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
    rw [Real.cos_arccos (by linarith only [hk2_bnd.1]) (by linarith only [hk2_bnd.2])]
    ring
  have hcosψ : Real.cos ψ = r := by
    have hcpos : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hψ0, Real.pi_pos], by linarith only [hψpi]⟩
    have hsinψ_sq : Real.sin ψ ^ 2 = k ^ 4 := by rw [hsinψ]; ring
    have hsq : Real.cos ψ ^ 2 = r ^ 2 := by
      rw [hr_sq, ← hsinψ_sq]
      linarith only [Real.sin_sq_add_cos_sq ψ]
    nlinarith only [hsq, hcpos, hr0]
  have htanψ2 : Real.tan (ψ / 2) = x₀ := by
    rw [Real.tan_eq_sin_div_cos]
    have h1 : 2 * Real.sin (ψ / 2) * Real.cos (ψ / 2) = Real.sin ψ := by
      rw [← Real.sin_two_mul]; congr 1; ring
    have h2 : 2 * Real.sin (ψ / 2) ^ 2 = 1 - Real.cos ψ := by
      conv_rhs => rw [show ψ = 2 * (ψ / 2) by ring, Real.cos_two_mul]
      linarith only [Real.sin_sq_add_cos_sq (ψ / 2)]
    have hc2 : Real.cos (ψ / 2) ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith only [hψ0, Real.pi_pos], by linarith only [hψpi, Real.pi_pos]⟩).ne'
    have hs2 : Real.sin (ψ / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith only [hψ0]) (by linarith only [hψpi, Real.pi_pos])).ne'
    calc Real.sin (ψ / 2) / Real.cos (ψ / 2)
        = (2 * Real.sin (ψ / 2) ^ 2) / (2 * Real.sin (ψ / 2) * Real.cos (ψ / 2)) := by
          field_simp [hc2, hs2] <;> ring
      _ = (1 - Real.cos ψ) / Real.sin ψ := by rw [h1, h2]
      _ = x₀ := by rw [hsinψ, hcosψ, hx₀_def]
  rw [← htanψ2] at htan_le_x₀
  have hmono := Real.strictMonoOn_tan.le_iff_le
    (⟨by linarith only [hE0, Real.pi_pos], by linarith only [hElt]⟩ :
      sphExcess m m d / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (⟨by linarith only [hψ0, Real.pi_pos], by linarith only [hψpi, Real.pi_pos]⟩ :
      ψ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
  have hle : sphExcess m m d / 4 ≤ ψ / 2 := hmono.mp htan_le_x₀
  rw [hk_def] at hψ_def
  linarith only [hle, hψ_def]

lemma sphSquare_area_mono {m₁ m₂ : ℝ} (hm1 : 0 ≤ m₁) (hm12 : m₁ ≤ m₂) (hm2 : m₂ < Real.pi / 2) :
    4 * Real.arccos (-Real.tan (m₁ / 2) ^ 2) - 2 * Real.pi ≤
      4 * Real.arccos (-Real.tan (m₂ / 2) ^ 2) - 2 * Real.pi := by
  have ht : Real.tan (m₁ / 2) ≤ Real.tan (m₂ / 2) :=
    (Real.strictMonoOn_tan.le_iff_le
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).mpr (by linarith)
  have ht0 : 0 ≤ Real.tan (m₁ / 2) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  have hsq : Real.tan (m₁ / 2) ^ 2 ≤ Real.tan (m₂ / 2) ^ 2 := by nlinarith
  have harc := Real.arccos_le_arccos (by linarith : -Real.tan (m₂ / 2) ^ 2 ≤ -Real.tan (m₁ / 2) ^ 2)
  linarith

/-! ### Part 2B: Kite Reduction, Spherical Polygon Triangulation, and Boundary Limit Bound -/

section PointwiseBoundary

open scoped Pointwise

lemma toSphere_hyperplane_null {N : ℕ} [NeZero N] (n : EuclideanSpace ℝ (Fin N)) (hn : n ≠ 0) :
    MeasureTheory.volume.toSphere
        {z : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) |
          inner ℝ n (z : EuclideanSpace ℝ (Fin N)) = 0} = 0 := by
  rw [MeasureTheory.Measure.toSphere_apply']
  · have hsub : (Set.Ioo (0 : ℝ) 1 • (Subtype.val ''
        {z : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) |
          inner ℝ n (z : EuclideanSpace ℝ (Fin N)) = 0})) ⊆
        (((Submodule.span ℝ {n})ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
          Set (EuclideanSpace ℝ (Fin N))) := by
      rintro x ⟨r, _, y, ⟨z, hz, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      change inner ℝ n (r • (z : EuclideanSpace ℝ (Fin N))) = 0
      rw [inner_smul_right, hz, mul_zero]
    have hne : (Submodule.span ℝ {n})ᗮ ≠ ⊤ := by
      intro htop
      have hmem : n ∈ (Submodule.span ℝ {n})ᗮ := htop ▸ Submodule.mem_top
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
      exact hn (inner_self_eq_zero.mp hmem)
    rw [MeasureTheory.measure_mono_null hsub
      (MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume _ hne), mul_zero]
  · exact (isClosed_eq (continuous_inner.comp (continuous_const.prodMk continuous_subtype_val))
      continuous_const).measurableSet

end PointwiseBoundary

lemma hausdorffMeasure2_circle_null (u v : E4) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) :
    MeasureTheory.Measure.hausdorffMeasure 2
        {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0 ∧ inner ℝ v x = 0} = 0 := by
  obtain ⟨b, hb, hb0, hb1⟩ := exists_orthonormal_extension_pair hu hv huv
  let B : OrthonormalBasis (Fin 4) ℝ E4 :=
    OrthonormalBasis.mk hb (le_of_eq (hb.linearIndependent.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])).symm)
  have hB : ∀ k, (B k : E4) = b k := fun k => by simp [B]
  let f : (Fin 2 → ℝ) → E4 := fun y => y 0 • b 2 + y 1 • b 3
  have hlip : LipschitzWith ⟨√2, Real.sqrt_nonneg 2⟩ f := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : f y - f z = (y 0 - z 0) • b 2 + (y 1 - z 1) • b 3 := by
      dsimp [f]; rw [sub_smul, sub_smul]; abel
    have hnorm : ‖f y - f z‖ ^ 2 = (y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 := by
      rw [hsub, norm_add_sq_real]
      have ho23 : inner ℝ (b 2) (b 3) = 0 := hb.2 (by decide)
      have hn2 : ‖b 2‖ = 1 := hb.1 2
      have hn3 : ‖b 3‖ = 1 := hb.1 3
      rw [inner_smul_left, inner_smul_right, ho23, mul_zero, mul_zero,
          norm_smul, norm_smul, hn2, hn3, mul_one, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      ring
    have h0 : |y 0 - z 0| ≤ ‖y - z‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - z) 0
    have h1 : |y 1 - z 1| ≤ ‖y - z‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - z) 1
    have hsq : ‖f y - f z‖ ^ 2 ≤ (√2 * ‖y - z‖) ^ 2 := by
      rw [hnorm, mul_pow, Real.sq_sqrt (by norm_num)]
      have s0 : (y 0 - z 0) ^ 2 ≤ ‖y - z‖ ^ 2 := by nlinarith [abs_nonneg (y 0 - z 0), sq_abs (y 0 - z 0)]
      have s1 : (y 1 - z 1) ^ 2 ≤ ‖y - z‖ ^ 2 := by nlinarith [abs_nonneg (y 1 - z 1), sq_abs (y 1 - z 1)]
      linarith
    exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))
  let T : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 = 1}
  have hsub : {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0 ∧ inner ℝ v x = 0} ⊆ f '' T := by
    rintro x ⟨hx, hux, hvx⟩
    refine ⟨![inner ℝ (b 2) x, inner ℝ (b 3) x], ?_, ?_⟩
    · change (inner ℝ (b 2) x) ^ 2 + (inner ℝ (b 3) x) ^ 2 = 1
      have hparse := B.sum_inner_mul_inner x x
      rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp hx, one_pow] at hparse
      simp only [Fin.sum_univ_four, hB] at hparse
      have hi0 : inner ℝ (b 0) x = 0 := by rw [hb0]; exact hux
      have hi1 : inner ℝ (b 1) x = 0 := by rw [hb1]; exact hvx
      have hc0 : inner ℝ x (b 0) = 0 := by rw [real_inner_comm]; exact hi0
      have hc1 : inner ℝ x (b 1) = 0 := by rw [real_inner_comm]; exact hi1
      rw [hi0, hc0, hi1, hc1] at hparse
      have hc2 : inner ℝ x (b 2) = inner ℝ (b 2) x := real_inner_comm (b 2) x
      have hc3 : inner ℝ x (b 3) = inner ℝ (b 3) x := real_inner_comm (b 3) x
      rw [hc2, hc3] at hparse
      linarith
    · simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hrep := B.sum_repr' x
      simp only [Fin.sum_univ_four, hB] at hrep
      have hi0 : inner ℝ (b 0) x = 0 := by rw [hb0]; exact hux
      have hi1 : inner ℝ (b 1) x = 0 := by rw [hb1]; exact hvx
      rw [hi0, hi1, zero_smul, zero_smul, zero_add, zero_add] at hrep
      exact hrep
  have hT0 : MeasureTheory.volume T = 0 := by
    let e := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    have hT_eq : T = e ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_sphere_zero_iff_norm, T]
      have hn : ‖e y‖ = 1 ↔ ‖e y‖ ^ 2 = 1 :=
        ⟨fun h => by rw [h, one_pow], fun h => by nlinarith [norm_nonneg (e y)]⟩
      rw [hn, EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, e]
    rw [hT_eq]
    have hm : MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.Measure.map e MeasureTheory.volume) :=
      ContinuousLinearEquiv.isAddHaarMeasure_map e MeasureTheory.volume
    rw [← MeasureTheory.Measure.map_apply e.continuous.measurable Metric.isClosed_sphere.measurableSet]
    exact MeasureTheory.Measure.addHaar_sphere
      (MeasureTheory.Measure.map e MeasureTheory.volume) 0 1
  have him : MeasureTheory.Measure.hausdorffMeasure 2 (f '' T) = 0 := by
    have hle := hlip.hausdorffMeasure_image_le (d := 2) (by norm_num) T
    rw [show (2 : ℝ) = ((Fintype.card (Fin 2) : ℕ) : ℝ) by norm_num,
        MeasureTheory.hausdorffMeasure_pi_real] at hle
    simpa [hT0] using hle
  exact MeasureTheory.measure_mono_null hsub him

lemma measure_sphere_two_section (u : E4) (hu : ‖u‖ = 1) :
    SphericalTetrahedron.measure 2 {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0} =
      4 * Real.pi * faceScale := by
  have hne_u : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hlt : Module.finrank ℝ (Submodule.span ℝ {u}) < 4 := by
    calc Module.finrank ℝ (Submodule.span ℝ {u}) ≤ 1 := finrank_span_singleton hne_u |>.le
      _ < 4 := by norm_num
  obtain ⟨v, hv, hvu⟩ := exists_unit_orthogonal_of_finrank_lt hlt
  have huv : inner ℝ u v = 0 := by
    simpa using (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hvu)
  let A : Set E4 :=
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0 ∧ 0 ≤ inner ℝ v x ∧ 0 ≤ inner ℝ v x}
  let B : Set E4 :=
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0 ∧ 0 ≤ inner ℝ (-v) x ∧ 0 ≤ inner ℝ (-v) x}
  have hA := measure_two_suspension_arc hu hv hv huv huv
  have hvneg : ‖-v‖ = 1 := by simp [hv]
  have huvneg : inner ℝ u (-v) = 0 := by simp [inner_neg_right, huv]
  have hB := measure_two_suspension_arc hu hvneg hvneg huvneg huvneg
  have hA_val : SphericalTetrahedron.measure 2 A = 2 * Real.pi * faceScale := by
    have hv1 : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
    rw [hA, hv1, Real.arccos_neg_one]; ring
  have hB_val : SphericalTetrahedron.measure 2 B = 2 * Real.pi * faceScale := by
    have hv2 : inner ℝ (-v) (-v) = 1 := by rw [real_inner_self_eq_norm_sq, hvneg, one_pow]
    rw [hB, hv2, Real.arccos_neg_one]; ring
  have hAB : {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0} = A ∪ B := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, A, B, inner_neg_left, neg_nonneg,
      and_self]
    constructor
    · rintro ⟨hx, hux⟩
      rcases le_total 0 (inner ℝ v x) with h | h
      · exact Or.inl ⟨hx, hux, h⟩
      · exact Or.inr ⟨hx, hux, h⟩
    · rintro (⟨hx, hux, _⟩ | ⟨hx, hux, _⟩) <;> exact ⟨hx, hux⟩
  have hI : A ∩ B = {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ u x = 0 ∧ inner ℝ v x = 0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, A, B, inner_neg_left, neg_nonneg,
      and_self]
    constructor
    · rintro ⟨⟨hx, hux, h1⟩, ⟨_, _, h2⟩⟩; exact ⟨hx, hux, le_antisymm h2 h1⟩
    · rintro ⟨hx, hux, hvx⟩; exact ⟨⟨hx, hux, hvx.ge⟩, ⟨hx, hux, hvx.le⟩⟩
  have hB_meas : MeasurableSet B := by
    refine (Metric.isClosed_sphere.inter
      ((isClosed_eq (continuous_inner.comp (continuous_const.prodMk continuous_id))
          (continuous_const : Continuous fun _ : E4 => (0 : ℝ))).inter
       ((isClosed_le (continuous_const : Continuous fun _ : E4 => (0 : ℝ))
          (continuous_inner.comp (continuous_const.prodMk continuous_id))).inter
        (isClosed_le (continuous_const : Continuous fun _ : E4 => (0 : ℝ))
          (continuous_inner.comp (continuous_const.prodMk continuous_id)))))).measurableSet
  have hI0 : MeasureTheory.Measure.hausdorffMeasure 2 (A ∩ B) = 0 := by
    rw [hI]; exact hausdorffMeasure2_circle_null u v hu hv huv
  have hpos : 0 < 2 * Real.pi * faceScale := by positivity [Real.pi_pos, faceScale_pos]
  have hA_fin : MeasureTheory.Measure.hausdorffMeasure 2 A ≠ ⊤ := by
    intro htop
    have : SphericalTetrahedron.measure 2 A = 0 := by simp [SphericalTetrahedron.measure, htop]
    linarith
  have hB_fin : MeasureTheory.Measure.hausdorffMeasure 2 B ≠ ⊤ := by
    intro htop
    have : SphericalTetrahedron.measure 2 B = 0 := by simp [SphericalTetrahedron.measure, htop]
    linarith
  have hunion : MeasureTheory.Measure.hausdorffMeasure 2 (A ∪ B) =
      MeasureTheory.Measure.hausdorffMeasure 2 A + MeasureTheory.Measure.hausdorffMeasure 2 B := by
    have h1 := MeasureTheory.measure_union_add_inter (μ := MeasureTheory.Measure.hausdorffMeasure 2) A hB_meas
    rw [hI0, add_zero] at h1
    exact h1
  rw [hAB, SphericalTetrahedron.measure, hunion, ENNReal.toReal_add hA_fin hB_fin]
  change SphericalTetrahedron.measure 2 A + SphericalTetrahedron.measure 2 B = 4 * Real.pi * faceScale
  linarith [hA_val, hB_val]

lemma exists_orthonormal_pair_ortho_E3 (n : E3) (hn : ‖n‖ = 1) :
    ∃ e₀ e₁ : E3, ‖e₀‖ = 1 ∧ ‖e₁‖ = 1 ∧
      inner ℝ e₀ n = 0 ∧ inner ℝ e₁ n = 0 ∧ inner ℝ e₀ e₁ = 0 := by
  have hne : n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hfin : Module.finrank ℝ (Submodule.span ℝ {n}) < Module.finrank ℝ E3 := by
    rw [finrank_euclideanSpace_fin]
    calc Module.finrank ℝ (Submodule.span ℝ {n}) ≤ 1 := finrank_span_singleton hne |>.le
      _ < 3 := by norm_num
  have hbot : (Submodule.span ℝ {n})ᗮ ≠ ⊥ := by
    intro h0
    have hadd := (Submodule.span ℝ {n}).finrank_add_finrank_orthogonal
    rw [h0, finrank_bot, add_zero] at hadd
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let e₀ : E3 := (1 / ‖v‖) • v
  have he₀ : ‖e₀‖ = 1 := by
    dsimp [e₀]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (norm_pos_iff.mpr hv_ne)),
      one_div_mul_cancel (norm_ne_zero_iff.mpr hv_ne)]
  have he₀n : inner ℝ e₀ n = 0 := by
    dsimp [e₀]
    rw [inner_smul_left, real_inner_comm]
    have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv_mem
    simp [this]
  let e₁ : E3 := cross3 n e₀
  have hne_0n : inner ℝ n e₀ = 0 := by rw [real_inner_comm]; exact he₀n
  have he₁_sq : ‖e₁‖ ^ 2 = 1 := by
    dsimp [e₁]; rw [norm_sq_cross3, hn, he₀, hne_0n]; ring
  have he₁ : ‖e₁‖ = 1 := by nlinarith [norm_nonneg e₁]
  have he₁n : inner ℝ e₁ n = 0 := by
    dsimp [e₁]; rw [real_inner_comm]; exact inner_left_cross3 n e₀
  have he₀₁ : inner ℝ e₀ e₁ = 0 := by
    dsimp [e₁]; exact inner_right_cross3 n e₀
  exact ⟨e₀, e₁, he₀, he₁, he₀n, he₁n, he₀₁⟩

lemma det3_sq_eq (A B C : E3) (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) :
    det3 A B C ^ 2 =
      1 - inner ℝ A B ^ 2 - inner ℝ B C ^ 2 - inner ℝ C A ^ 2 +
        2 * inner ℝ A B * inner ℝ B C * inner ℝ C A := by
  have hA2 : A.ofLp 0 ^ 2 + A.ofLp 1 ^ 2 + A.ofLp 2 ^ 2 = 1 := by
    have := hA ▸ EuclideanSpace.norm_sq_eq A
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using this.symm
  have hB2 : B.ofLp 0 ^ 2 + B.ofLp 1 ^ 2 + B.ofLp 2 ^ 2 = 1 := by
    have := hB ▸ EuclideanSpace.norm_sq_eq B
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using this.symm
  have hC2 : C.ofLp 0 ^ 2 + C.ofLp 1 ^ 2 + C.ofLp 2 ^ 2 = 1 := by
    have := hC ▸ EuclideanSpace.norm_sq_eq C
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using this.symm
  have hab : inner ℝ A B = A.ofLp 0 * B.ofLp 0 + A.ofLp 1 * B.ofLp 1 + A.ofLp 2 * B.ofLp 2 := by
    simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, mul_comm]
  have hbc : inner ℝ B C = B.ofLp 0 * C.ofLp 0 + B.ofLp 1 * C.ofLp 1 + B.ofLp 2 * C.ofLp 2 := by
    simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, mul_comm]
  have hca : inner ℝ C A = C.ofLp 0 * A.ofLp 0 + C.ofLp 1 * A.ofLp 1 + C.ofLp 2 * A.ofLp 2 := by
    simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, mul_comm]
  have hdet : det3 A B C =
      A.ofLp 0 * (B.ofLp 1 * C.ofLp 2 - B.ofLp 2 * C.ofLp 1) -
      A.ofLp 1 * (B.ofLp 0 * C.ofLp 2 - B.ofLp 2 * C.ofLp 0) +
      A.ofLp 2 * (B.ofLp 0 * C.ofLp 1 - B.ofLp 1 * C.ofLp 0) := by
    simp only [det3, cross3, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  rw [hdet, hab, hbc, hca]
  have hpoly :
      (A.ofLp 0 * (B.ofLp 1 * C.ofLp 2 - B.ofLp 2 * C.ofLp 1) -
        A.ofLp 1 * (B.ofLp 0 * C.ofLp 2 - B.ofLp 2 * C.ofLp 0) +
        A.ofLp 2 * (B.ofLp 0 * C.ofLp 1 - B.ofLp 1 * C.ofLp 0)) ^ 2 =
      (A.ofLp 0 ^ 2 + A.ofLp 1 ^ 2 + A.ofLp 2 ^ 2) *
          (B.ofLp 0 ^ 2 + B.ofLp 1 ^ 2 + B.ofLp 2 ^ 2) *
          (C.ofLp 0 ^ 2 + C.ofLp 1 ^ 2 + C.ofLp 2 ^ 2) -
        (C.ofLp 0 ^ 2 + C.ofLp 1 ^ 2 + C.ofLp 2 ^ 2) *
          (A.ofLp 0 * B.ofLp 0 + A.ofLp 1 * B.ofLp 1 + A.ofLp 2 * B.ofLp 2) ^ 2 -
        (A.ofLp 0 ^ 2 + A.ofLp 1 ^ 2 + A.ofLp 2 ^ 2) *
          (B.ofLp 0 * C.ofLp 0 + B.ofLp 1 * C.ofLp 1 + B.ofLp 2 * C.ofLp 2) ^ 2 -
        (B.ofLp 0 ^ 2 + B.ofLp 1 ^ 2 + B.ofLp 2 ^ 2) *
          (C.ofLp 0 * A.ofLp 0 + C.ofLp 1 * A.ofLp 1 + C.ofLp 2 * A.ofLp 2) ^ 2 +
        2 * (A.ofLp 0 * B.ofLp 0 + A.ofLp 1 * B.ofLp 1 + A.ofLp 2 * B.ofLp 2) *
          (B.ofLp 0 * C.ofLp 0 + B.ofLp 1 * C.ofLp 1 + B.ofLp 2 * C.ofLp 2) *
          (C.ofLp 0 * A.ofLp 0 + C.ofLp 1 * A.ofLp 1 + C.ofLp 2 * A.ofLp 2) := by
    ring
  rw [hpoly, hA2, hB2, hC2]
  ring

lemma det3_ne_zero_of_linearIndependent {A B C : E3}
    (h : LinearIndependent ℝ ![A, B, C]) : det3 A B C ≠ 0 := by
  intro h0
  have hspan : Submodule.span ℝ (Set.range ![A, B, C]) = ⊤ :=
    h.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])
  have hcr : cross3 A B ∈ (Submodule.span ℝ (Set.range ![A, B, C]))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have hA : inner ℝ A (cross3 A B) = 0 := inner_left_cross3 A B
    have hB : inner ℝ B (cross3 A B) = 0 := inner_right_cross3 A B
    have hC : inner ℝ C (cross3 A B) = 0 := by
      have hcd : inner ℝ C (cross3 A B) = det3 C A B := rfl
      rw [hcd, det3_cyclic]
      exact h0
    simp [inner_add_left, inner_smul_left, hA, hB, hC]
  rw [hspan] at hcr
  rw [Submodule.mem_orthogonal] at hcr
  have hzero : cross3 A B = 0 := inner_self_eq_zero.mp (hcr (cross3 A B) Submodule.mem_top)
  have hnorm_cr : ‖cross3 A B‖ ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 - inner ℝ A B ^ 2 := norm_sq_cross3 A B
  rw [hzero, norm_zero, zero_pow (by norm_num)] at hnorm_cr
  let w : E3 := (inner ℝ A A) • B - (inner ℝ A B) • A
  have hw0 : ‖w‖ ^ 2 = 0 := by
    dsimp [w]
    rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
        Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    simp only [conj_trivial]
    have hBA : inner ℝ B A = inner ℝ A B := real_inner_comm A B
    have hAA : inner ℝ A A = ‖A‖ ^ 2 := real_inner_self_eq_norm_sq A
    rw [hBA, hAA]
    linear_combination (‖A‖ ^ 2) * (-hnorm_cr)
  have hw : w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w])
  have hdep := Fintype.linearIndependent_iff.mp h ![(-inner ℝ A B), inner ℝ A A, 0]
  have hcomb : ∑ i : Fin 3, (![-inner ℝ A B, inner ℝ A A, 0] i) • ![A, B, C] i = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      zero_smul, add_zero, neg_smul]
    simpa [w, sub_eq_neg_add, add_comm] using hw
  have hi1 := hdep hcomb 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, real_inner_self_eq_norm_sq] at hi1
  have hA0 : A = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg A])
  exact h.ne_zero 0 (by simpa using hA0)

lemma sphTriangleInequalities_of_det3_ne_zero {A B C : E3}
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) (hdet : det3 A B C ≠ 0) :
    let a := Real.arccos (inner ℝ B C)
    let b := Real.arccos (inner ℝ C A)
    let c := Real.arccos (inner ℝ A B)
    0 < a ∧ a < Real.pi ∧ 0 < b ∧ b < Real.pi ∧ 0 < c ∧ c < Real.pi ∧
      a < b + c ∧ b < c + a ∧ c < a + b ∧ a + b + c < 2 * Real.pi := by
  intro a b c
  have hsq : det3 A B C ^ 2 > 0 := sq_pos_of_ne_zero hdet
  rw [det3_sq_eq A B C hA hB hC] at hsq
  have hab_sq : 1 - inner ℝ A B ^ 2 > 0 := by
    have h1 : (inner ℝ C A - inner ℝ A B * inner ℝ B C) ^ 2 ≥ 0 := sq_nonneg _
    have h2 : (1 - inner ℝ A B ^ 2) * (1 - inner ℝ B C ^ 2) =
        (inner ℝ C A - inner ℝ A B * inner ℝ B C) ^ 2 +
          (1 - inner ℝ A B ^ 2 - inner ℝ B C ^ 2 - inner ℝ C A ^ 2 +
            2 * inner ℝ A B * inner ℝ B C * inner ℝ C A) := by ring
    have hbc_le : 0 ≤ 1 - inner ℝ B C ^ 2 := by
      have : |inner ℝ B C| ≤ ‖B‖ * ‖C‖ := abs_real_inner_le_norm B C
      rw [hB, hC, mul_one] at this
      nlinarith [abs_le.mp this]
    nlinarith
  have hbc_sq : 1 - inner ℝ B C ^ 2 > 0 := by
    have h1 : (inner ℝ A B - inner ℝ B C * inner ℝ C A) ^ 2 ≥ 0 := sq_nonneg _
    have h2 : (1 - inner ℝ B C ^ 2) * (1 - inner ℝ C A ^ 2) =
        (inner ℝ A B - inner ℝ B C * inner ℝ C A) ^ 2 +
          (1 - inner ℝ A B ^ 2 - inner ℝ B C ^ 2 - inner ℝ C A ^ 2 +
            2 * inner ℝ A B * inner ℝ B C * inner ℝ C A) := by ring
    have hca_le : 0 ≤ 1 - inner ℝ C A ^ 2 := by
      have : |inner ℝ C A| ≤ ‖C‖ * ‖A‖ := abs_real_inner_le_norm C A
      rw [hC, hA, mul_one] at this
      nlinarith [abs_le.mp this]
    nlinarith
  have hca_sq : 1 - inner ℝ C A ^ 2 > 0 := by
    have h1 : (inner ℝ B C - inner ℝ C A * inner ℝ A B) ^ 2 ≥ 0 := sq_nonneg _
    have h2 : (1 - inner ℝ C A ^ 2) * (1 - inner ℝ A B ^ 2) =
        (inner ℝ B C - inner ℝ C A * inner ℝ A B) ^ 2 +
          (1 - inner ℝ A B ^ 2 - inner ℝ B C ^ 2 - inner ℝ C A ^ 2 +
            2 * inner ℝ A B * inner ℝ B C * inner ℝ C A) := by ring
    nlinarith
  have hab_lt : -1 < inner ℝ A B ∧ inner ℝ A B < 1 := ⟨by nlinarith, by nlinarith⟩
  have hbc_lt : -1 < inner ℝ B C ∧ inner ℝ B C < 1 := ⟨by nlinarith, by nlinarith⟩
  have hca_lt : -1 < inner ℝ C A ∧ inner ℝ C A < 1 := ⟨by nlinarith, by nlinarith⟩
  have ha0 : 0 < a := Real.arccos_pos.mpr hbc_lt.2
  have ha1 : a < Real.pi := Real.arccos_lt_pi.mpr hbc_lt.1
  have hb0 : 0 < b := Real.arccos_pos.mpr hca_lt.2
  have hb1 : b < Real.pi := Real.arccos_lt_pi.mpr hca_lt.1
  have hc0 : 0 < c := Real.arccos_pos.mpr hab_lt.2
  have hc1 : c < Real.pi := Real.arccos_lt_pi.mpr hab_lt.1
  have hcos_lt_to_lt : ∀ {u v : ℝ}, 0 ≤ u → u ≤ Real.pi → 0 ≤ v → v ≤ Real.pi →
      Real.cos v < Real.cos u → u < v := by
    intro u v hu0 hu1 hv0 hv1 hlt
    by_contra hle
    rcases eq_or_lt_of_le (le_of_not_gt hle) with rfl | hlt'
    · linarith
    · exact absurd (Real.strictAntiOn_cos ⟨hv0, hv1⟩ ⟨hu0, hu1⟩ hlt') (not_lt_of_gt hlt)
  have tri : ∀ {x y z : ℝ}, 0 < x → x < Real.pi → 0 < y → y < Real.pi → 0 < z → z < Real.pi →
      (Real.cos z - Real.cos x * Real.cos y) ^ 2 < (1 - Real.cos x ^ 2) * (1 - Real.cos y ^ 2) →
      z < x + y ∧ x + y + z < 2 * Real.pi := by
    intro x y z hx0 hx1 hy0 hy1 hz0 hz1 hdiff
    have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hx1
    have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy0 hy1
    have hprod_sq : (Real.sin x * Real.sin y) ^ 2 = (1 - Real.cos x ^ 2) * (1 - Real.cos y ^ 2) := by
      have := Real.sin_sq x; have := Real.sin_sq y
      nlinarith
    rw [← hprod_sq] at hdiff
    have hcos_add : Real.cos (x + y) < Real.cos z := by
      rw [Real.cos_add]
      have hspos : 0 < Real.sin x * Real.sin y := mul_pos hsx hsy
      nlinarith [sq_nonneg (Real.cos z - Real.cos x * Real.cos y - (-Real.sin x * Real.sin y))]
    have hlt1 : z < x + y := by
      by_cases hle : x + y ≤ Real.pi
      · exact hcos_lt_to_lt hz0.le hz1.le (by linarith) hle hcos_add
      · linarith
    have hlt2 : x + y + z < 2 * Real.pi := by
      by_cases hle : x + y ≤ Real.pi
      · linarith
      · have hpi : Real.pi < x + y := lt_of_not_ge hle
        have hcos_2pi : Real.cos (2 * Real.pi - (x + y)) < Real.cos z := by
          rw [Real.cos_two_pi_sub]; exact hcos_add
        have hlt_sub : z < 2 * Real.pi - (x + y) :=
          hcos_lt_to_lt hz0.le hz1.le (by linarith) (by linarith) hcos_2pi
        linarith
    exact ⟨hlt1, hlt2⟩
  have hcos_a : Real.cos a = inner ℝ B C := Real.cos_arccos hbc_lt.1.le hbc_lt.2.le
  have hcos_b : Real.cos b = inner ℝ C A := Real.cos_arccos hca_lt.1.le hca_lt.2.le
  have hcos_c : Real.cos c = inner ℝ A B := Real.cos_arccos hab_lt.1.le hab_lt.2.le
  have h1 : (Real.cos a - Real.cos b * Real.cos c) ^ 2 < (1 - Real.cos b ^ 2) * (1 - Real.cos c ^ 2) := by
    rw [hcos_a, hcos_b, hcos_c]; linarith
  have h2 : (Real.cos b - Real.cos c * Real.cos a) ^ 2 < (1 - Real.cos c ^ 2) * (1 - Real.cos a ^ 2) := by
    rw [hcos_a, hcos_b, hcos_c]; linarith
  have h3 : (Real.cos c - Real.cos a * Real.cos b) ^ 2 < (1 - Real.cos a ^ 2) * (1 - Real.cos b ^ 2) := by
    rw [hcos_a, hcos_b, hcos_c]; linarith
  obtain ⟨ha_lt, hsum⟩ := tri hb0 hb1 hc0 hc1 ha0 ha1 h1
  obtain ⟨hb_lt, _⟩ := tri hc0 hc1 ha0 ha1 hb0 hb1 h2
  obtain ⟨hc_lt, _⟩ := tri ha0 ha1 hb0 hb1 hc0 hc1 h3
  exact ⟨ha0, ha1, hb0, hb1, hc0, hc1, ha_lt, hb_lt, hc_lt, by linarith⟩

private lemma abs_inner_lt_one_of_orth_pos {u v w : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hwv : inner ℝ w v = 0) (hwu : 0 < inner ℝ w u) :
    -1 < inner ℝ u v ∧ inner ℝ u v < 1 := by
  have hle : |inner ℝ u v| ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rwa [hu, hv, mul_one] at h
  by_contra h
  have hpm : inner ℝ u v = 1 ∨ inner ℝ u v = -1 := by
    rcases not_and_or.mp h with hle1 | hge1
    · right; linarith [(abs_le.mp hle).1]
    · left; linarith [(abs_le.mp hle).2]
  have hdiff : ‖u - inner ℝ u v • v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hu, hv, mul_one, one_pow,
        inner_smul_right, sq_abs]
    rcases hpm with hc | hc
    · rw [hc]; ring
    · rw [hc]; ring
  have hzero : u - inner ℝ u v • v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (u - inner ℝ u v • v)])
  have hu_eq : u = inner ℝ u v • v := sub_eq_zero.mp hzero
  have hz : inner ℝ w u = 0 := by rw [hu_eq, inner_smul_right, hwv, mul_zero]
  linarith

private lemma ortho_unit_angle_neg {a b c s : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hcs : c ^ 2 + s ^ 2 = 1) (hab : a ^ 2 + b ^ 2 = 1) (hdot : a * c + b * s = 0) :
    -b = c := by
  have ha2 : a ^ 2 = s ^ 2 := by
    have hmul : (a * c) ^ 2 = (b * s) ^ 2 := by
      have h : a * c = -(b * s) := by linarith
      rw [h]; ring
    have h1 : a ^ 2 * (1 - s ^ 2) = (a * c) ^ 2 := by
      have : c ^ 2 = 1 - s ^ 2 := by linarith
      rw [mul_pow, this]
    have h2 : (1 - a ^ 2) * s ^ 2 = (b * s) ^ 2 := by
      have : b ^ 2 = 1 - a ^ 2 := by linarith
      rw [mul_pow, this]
    have h3 : a ^ 2 * (1 - s ^ 2) = (1 - a ^ 2) * s ^ 2 := by linarith
    linarith
  have has : a = s := by nlinarith only [hs, ha, ha2]
  have hdot' : s * c + b * s = 0 := by rw [has] at hdot; exact hdot
  have hsum : s * (c + b) = 0 := by linarith
  have hcb : c + b = 0 := (mul_eq_zero.mp hsum).resolve_left hs.ne'
  linarith

private lemma orthonormal_E3_inner {e₀ e₁ e₂ : E3}
    (he0 : ‖e₀‖ = 1) (he1 : ‖e₁‖ = 1) (he2 : ‖e₂‖ = 1)
    (h01 : inner ℝ e₀ e₁ = 0) (h02 : inner ℝ e₀ e₂ = 0) (h12 : inner ℝ e₁ e₂ = 0)
    (x y : E3) :
    inner ℝ x y = inner ℝ x e₀ * inner ℝ e₀ y + inner ℝ x e₁ * inner ℝ e₁ y +
      inner ℝ x e₂ * inner ℝ e₂ y := by
  let b : Fin 3 → E3 := ![e₀, e₁, e₂]
  have hb : Orthonormal ℝ b := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · fin_cases i <;> simp [b, he0, he1, he2]
    · fin_cases i <;> fin_cases j <;> try contradiction
      all_goals simp [b, h01, h02, h12, real_inner_comm]
  let B : OrthonormalBasis (Fin 3) ℝ E3 :=
    OrthonormalBasis.mk hb (le_of_eq (hb.linearIndependent.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])).symm)
  have hB0 : (B 0 : E3) = e₀ := by simp [B, b]
  have hB1 : (B 1 : E3) = e₁ := by simp [B, b]
  have hB2 : (B 2 : E3) = e₂ := by simp [B, b]
  have hs := (B.sum_inner_mul_inner x y).symm
  rw [Fin.sum_univ_three, hB0, hB1, hB2] at hs
  exact hs

lemma sphCosAngle_of_normals {V₀ V₁ V₂ w₀ w₁ : E3}
    (hV0 : ‖V₀‖ = 1) (hV1 : ‖V₁‖ = 1) (hV2 : ‖V₂‖ = 1)
    (hw0 : ‖w₀‖ = 1) (hw1 : ‖w₁‖ = 1)
    (hw00 : inner ℝ w₀ V₀ = 0) (hw01 : inner ℝ w₀ V₁ = 0) (hw02 : 0 < inner ℝ w₀ V₂)
    (hw11 : inner ℝ w₁ V₁ = 0) (hw12 : inner ℝ w₁ V₂ = 0) (hw10 : 0 < inner ℝ w₁ V₀) :
    -inner ℝ w₀ w₁ =
      sphCosAngle (Real.arccos (inner ℝ V₂ V₀))
        (Real.arccos (inner ℝ V₀ V₁))
        (Real.arccos (inner ℝ V₁ V₂)) := by
  obtain ⟨c01, hc01⟩ : ∃ x : ℝ, x = inner ℝ V₀ V₁ := ⟨_, rfl⟩
  obtain ⟨c12, hc12⟩ : ∃ x : ℝ, x = inner ℝ V₁ V₂ := ⟨_, rfl⟩
  obtain ⟨c20, hc20⟩ : ∃ x : ℝ, x = inner ℝ V₂ V₀ := ⟨_, rfl⟩
  have h01_lt : -1 < c01 ∧ c01 < 1 := by
    rw [hc01]; exact abs_inner_lt_one_of_orth_pos hV0 hV1 hw11 hw10
  have h12_lt : -1 < c12 ∧ c12 < 1 := by
    have h21 : -1 < inner ℝ V₂ V₁ ∧ inner ℝ V₂ V₁ < 1 :=
      abs_inner_lt_one_of_orth_pos hV2 hV1 hw01 hw02
    have hc21 : inner ℝ V₂ V₁ = c12 := by rw [real_inner_comm V₁ V₂, ← hc12]
    rwa [hc21] at h21
  have hs01_sq : 0 < 1 - c01 ^ 2 := by nlinarith [h01_lt.1, h01_lt.2]
  have hs12_sq : 0 < 1 - c12 ^ 2 := by nlinarith [h12_lt.1, h12_lt.2]
  obtain ⟨s01, hs01_eq⟩ : ∃ x : ℝ, x = √(1 - c01 ^ 2) := ⟨_, rfl⟩
  obtain ⟨s12, hs12_eq⟩ : ∃ x : ℝ, x = √(1 - c12 ^ 2) := ⟨_, rfl⟩
  have hs01 : 0 < s01 := by rw [hs01_eq]; exact Real.sqrt_pos.mpr hs01_sq
  have hs12 : 0 < s12 := by rw [hs12_eq]; exact Real.sqrt_pos.mpr hs12_sq
  obtain ⟨t₀, ht₀_eq⟩ : ∃ t : E3, t = (1 / s01) • (V₀ - c01 • V₁) := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂_eq⟩ : ∃ t : E3, t = (1 / s12) • (V₂ - c12 • V₁) := ⟨_, rfl⟩
  have ht0_norm : ‖t₀‖ = 1 := by
    have hraw : ‖V₀ - c01 • V₁‖ ^ 2 = s01 ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hV0, hV1, mul_one, one_pow,
          inner_smul_right, sq_abs, hs01_eq, Real.sq_sqrt hs01_sq.le, ← hc01]
      ring
    have ht0_sq : ‖t₀‖ ^ 2 = 1 := by
      rw [ht₀_eq, norm_smul, mul_pow, hraw, Real.norm_eq_abs, sq_abs]
      field_simp [hs01.ne']
    nlinarith [norm_nonneg t₀]
  have ht2_norm : ‖t₂‖ = 1 := by
    have hraw : ‖V₂ - c12 • V₁‖ ^ 2 = s12 ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hV2, hV1, mul_one, one_pow,
          inner_smul_right, sq_abs, hs12_eq, Real.sq_sqrt hs12_sq.le]
      have hc21 : inner ℝ V₂ V₁ = c12 := by rw [real_inner_comm V₁ V₂, ← hc12]
      rw [hc21]; ring
    have ht2_sq : ‖t₂‖ ^ 2 = 1 := by
      rw [ht₂_eq, norm_smul, mul_pow, hraw, Real.norm_eq_abs, sq_abs]
      field_simp [hs12.ne']
    nlinarith [norm_nonneg t₂]
  have hV1_t0 : inner ℝ V₁ t₀ = 0 := by
    have h10 : inner ℝ V₁ V₀ = c01 := by rw [real_inner_comm V₀ V₁, ← hc01]
    rw [ht₀_eq, inner_smul_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        hV1, one_pow, h10]
    ring
  have hw0_t0 : inner ℝ w₀ t₀ = 0 := by
    rw [ht₀_eq, inner_smul_right, inner_sub_right, inner_smul_right, hw00, hw01]; ring
  have hV1_w0 : inner ℝ V₁ w₀ = 0 := by rw [real_inner_comm w₀ V₁, hw01]
  have hV1_t2 : inner ℝ V₁ t₂ = 0 := by
    have h12 : inner ℝ V₁ V₂ = c12 := hc12.symm
    rw [ht₂_eq, inner_smul_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        hV1, one_pow, h12]
    ring
  have hV1_w1 : inner ℝ V₁ w₁ = 0 := by rw [real_inner_comm w₁ V₁, hw11]
  obtain ⟨c, hc_eq'⟩ : ∃ x : ℝ, x = inner ℝ t₀ t₂ := ⟨_, rfl⟩
  obtain ⟨s, hs_eq'⟩ : ∃ x : ℝ, x = inner ℝ w₀ t₂ := ⟨_, rfl⟩
  obtain ⟨a₁, ha₁_eq'⟩ : ∃ x : ℝ, x = inner ℝ t₀ w₁ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁_eq'⟩ : ∃ x : ℝ, x = inner ℝ w₀ w₁ := ⟨_, rfl⟩
  have hs_pos : 0 < s := by
    rw [hs_eq', ht₂_eq, inner_smul_right, inner_sub_right, inner_smul_right, hw01, mul_zero, sub_zero]
    exact mul_pos (one_div_pos.mpr hs12) hw02
  have ha1_pos : 0 < a₁ := by
    rw [ha₁_eq', ht₀_eq, inner_smul_left, inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
    have h0w1 : inner ℝ V₀ w₁ = inner ℝ w₁ V₀ := real_inner_comm w₁ V₀
    rw [h0w1, hV1_w1, mul_zero, sub_zero]
    exact mul_pos (one_div_pos.mpr hs01) hw10
  have ht0_w0 : inner ℝ t₀ w₀ = 0 := by rw [real_inner_comm w₀ t₀, hw0_t0]
  have hcs_sq : c ^ 2 + s ^ 2 = 1 := by
    have hnorm_t2 := orthonormal_E3_inner hV1 ht0_norm hw0 hV1_t0 hV1_w0 ht0_w0 t₂ t₂
    rw [real_inner_self_eq_norm_sq, ht2_norm, one_pow] at hnorm_t2
    have ht2V1 : inner ℝ t₂ V₁ = 0 := by rw [real_inner_comm V₁ t₂, hV1_t2]
    have ht2t0 : inner ℝ t₂ t₀ = c := by rw [real_inner_comm t₀ t₂, ← hc_eq']
    have ht2w0 : inner ℝ t₂ w₀ = s := by rw [real_inner_comm w₀ t₂, ← hs_eq']
    rw [ht2V1, hV1_t2, ht2t0, ht2w0, ← hc_eq', ← hs_eq'] at hnorm_t2
    linear_combination -hnorm_t2
  have hab_sq : a₁ ^ 2 + b₁ ^ 2 = 1 := by
    have hnorm_w1 := orthonormal_E3_inner hV1 ht0_norm hw0 hV1_t0 hV1_w0 ht0_w0 w₁ w₁
    rw [real_inner_self_eq_norm_sq, hw1, one_pow] at hnorm_w1
    have hw1t0 : inner ℝ w₁ t₀ = a₁ := by rw [real_inner_comm t₀ w₁, ← ha₁_eq']
    have hw1w0 : inner ℝ w₁ w₀ = b₁ := by rw [real_inner_comm w₀ w₁, ← hb₁_eq']
    rw [hw11, hV1_w1, hw1t0, hw1w0, ← ha₁_eq', ← hb₁_eq'] at hnorm_w1
    linear_combination -hnorm_w1
  have hdot : a₁ * c + b₁ * s = 0 := by
    have hw1_t2_inner := orthonormal_E3_inner hV1 ht0_norm hw0 hV1_t0 hV1_w0 ht0_w0 w₁ t₂
    have hw1_t2_zero : inner ℝ w₁ t₂ = 0 := by
      rw [ht₂_eq, inner_smul_right, inner_sub_right, inner_smul_right, hw12, hw11]; ring
    rw [hw1_t2_zero] at hw1_t2_inner
    have hw1t0 : inner ℝ w₁ t₀ = a₁ := by rw [real_inner_comm t₀ w₁, ← ha₁_eq']
    have hw1w0 : inner ℝ w₁ w₀ = b₁ := by rw [real_inner_comm w₀ w₁, ← hb₁_eq']
    rw [hw11, hV1_t2, hw1t0, hw1w0, ← hc_eq', ← hs_eq'] at hw1_t2_inner
    linarith only [hw1_t2_inner]
  have hb1_c : -b₁ = c := ortho_unit_angle_neg hs_pos ha1_pos hcs_sq hab_sq hdot
  have hc_eq : c = (c20 - c01 * c12) / (s01 * s12) := by
    rw [hc_eq', ht₀_eq, ht₂_eq, inner_smul_left, inner_smul_right, inner_sub_left,
        inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
        inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hV1, one_pow]
    simp only [conj_trivial]
    have h02 : inner ℝ V₀ V₂ = c20 := by rw [real_inner_comm V₂ V₀, ← hc20]
    have h01' : inner ℝ V₀ V₁ = c01 := hc01.symm
    have h12' : inner ℝ V₁ V₂ = c12 := hc12.symm
    rw [h02, h01', h12']
    field_simp [hs01.ne', hs12.ne']
    ring
  have hd01 : Real.cos (Real.arccos c01) = c01 := Real.cos_arccos h01_lt.1.le h01_lt.2.le
  have hd12 : Real.cos (Real.arccos c12) = c12 := Real.cos_arccos h12_lt.1.le h12_lt.2.le
  have hd20 : Real.cos (Real.arccos c20) = c20 := by
    have hle := abs_real_inner_le_norm V₂ V₀
    rw [hV2, hV0, mul_one, ← hc20] at hle
    exact Real.cos_arccos (abs_le.mp hle).1 (abs_le.mp hle).2
  have hs01_sin : Real.sin (Real.arccos c01) = s01 := by rw [Real.sin_arccos, ← hs01_eq]
  have hs12_sin : Real.sin (Real.arccos c12) = s12 := by rw [Real.sin_arccos, ← hs12_eq]
  dsimp [sphCosAngle]
  rw [← hc20, ← hc01, ← hc12, hd20, hd01, hd12, hs01_sin, hs12_sin, ← hb₁_eq']
  exact hb1_c.trans hc_eq

lemma stdTriArea_eq_sphExcess {V₀ V₁ V₂ w₀ w₁ w₂ : ↑(Metric.sphere (0 : E3) 1)}
    (hw00 : inner ℝ (w₀ : E3) (V₀ : E3) = 0)
    (hw01 : inner ℝ (w₀ : E3) (V₁ : E3) = 0)
    (hw02 : 0 < inner ℝ (w₀ : E3) (V₂ : E3))
    (hw11 : inner ℝ (w₁ : E3) (V₁ : E3) = 0)
    (hw12 : inner ℝ (w₁ : E3) (V₂ : E3) = 0)
    (hw10 : 0 < inner ℝ (w₁ : E3) (V₀ : E3))
    (hw22 : inner ℝ (w₂ : E3) (V₂ : E3) = 0)
    (hw20 : inner ℝ (w₂ : E3) (V₀ : E3) = 0)
    (hw21 : 0 < inner ℝ (w₂ : E3) (V₁ : E3)) :
    LinearIndependent ℝ ![(V₀ : E3), (V₁ : E3), (V₂ : E3)] ∧
      LinearIndependent ℝ ![(w₀ : E3), (w₁ : E3), (w₂ : E3)] ∧
      stdTriArea ![w₀, w₁, w₂] =
        sphExcess (Real.arccos (inner ℝ (V₁ : E3) (V₂ : E3)))
          (Real.arccos (inner ℝ (V₂ : E3) (V₀ : E3)))
          (Real.arccos (inner ℝ (V₀ : E3) (V₁ : E3))) := by
  have hliV : LinearIndependent ℝ ![(V₀ : E3), (V₁ : E3), (V₂ : E3)] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi0 : inner ℝ (w₀ : E3) (∑ j : Fin 3, c j • ![(V₀ : E3), (V₁ : E3), (V₂ : E3)] j) = 0 := by
      rw [hc, inner_zero_right]
    have hi1 : inner ℝ (w₁ : E3) (∑ j : Fin 3, c j • ![(V₀ : E3), (V₁ : E3), (V₂ : E3)] j) = 0 := by
      rw [hc, inner_zero_right]
    have hi2 : inner ℝ (w₂ : E3) (∑ j : Fin 3, c j • ![(V₀ : E3), (V₁ : E3), (V₂ : E3)] j) = 0 := by
      rw [hc, inner_zero_right]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      inner_add_right, inner_smul_right] at hi0 hi1 hi2
    rw [hw00, hw01, mul_zero, mul_zero, zero_add, zero_add] at hi0
    rw [hw11, hw12, mul_zero, mul_zero, add_zero, add_zero] at hi1
    rw [hw20, hw22, mul_zero, mul_zero, zero_add, add_zero] at hi2
    have hc2 : c 2 = 0 := (mul_eq_zero.mp hi0).resolve_right hw02.ne'
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hi1).resolve_right hw10.ne'
    have hc1 : c 1 = 0 := (mul_eq_zero.mp hi2).resolve_right hw21.ne'
    fin_cases i <;> assumption
  have hliw : LinearIndependent ℝ ![(w₀ : E3), (w₁ : E3), (w₂ : E3)] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hi0 : inner ℝ (∑ j : Fin 3, c j • ![(w₀ : E3), (w₁ : E3), (w₂ : E3)] j) (V₂ : E3) = 0 := by
      rw [hc, inner_zero_left]
    have hi1 : inner ℝ (∑ j : Fin 3, c j • ![(w₀ : E3), (w₁ : E3), (w₂ : E3)] j) (V₀ : E3) = 0 := by
      rw [hc, inner_zero_left]
    have hi2 : inner ℝ (∑ j : Fin 3, c j • ![(w₀ : E3), (w₁ : E3), (w₂ : E3)] j) (V₁ : E3) = 0 := by
      rw [hc, inner_zero_left]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      inner_add_left, inner_smul_left] at hi0 hi1 hi2
    rw [hw12, hw22, mul_zero, mul_zero, add_zero, add_zero] at hi0
    rw [hw00, hw20, mul_zero, mul_zero, zero_add, add_zero] at hi1
    rw [hw01, hw11, mul_zero, mul_zero, zero_add, zero_add] at hi2
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hi0).resolve_right hw02.ne'
    have hc1 : c 1 = 0 := (mul_eq_zero.mp hi1).resolve_right hw10.ne'
    have hc2 : c 2 = 0 := (mul_eq_zero.mp hi2).resolve_right hw21.ne'
    fin_cases i <;> assumption
  have hV0 := mem_sphere_zero_iff_norm.mp V₀.2
  have hV1 := mem_sphere_zero_iff_norm.mp V₁.2
  have hV2 := mem_sphere_zero_iff_norm.mp V₂.2
  have hw0n := mem_sphere_zero_iff_norm.mp w₀.2
  have hw1n := mem_sphere_zero_iff_norm.mp w₁.2
  have hw2n := mem_sphere_zero_iff_norm.mp w₂.2
  have hc01 := sphCosAngle_of_normals hV0 hV1 hV2 hw0n hw1n hw00 hw01 hw02 hw11 hw12 hw10
  have hc12 := sphCosAngle_of_normals hV1 hV2 hV0 hw1n hw2n hw11 hw12 hw10 hw22 hw20 hw21
  have hc20 := sphCosAngle_of_normals hV2 hV0 hV1 hw2n hw0n hw22 hw20 hw21 hw00 hw01 hw02
  have harea : stdTriArea ![w₀, w₁, w₂] =
      sphExcess (Real.arccos (inner ℝ (V₁ : E3) (V₂ : E3)))
        (Real.arccos (inner ℝ (V₂ : E3) (V₀ : E3)))
        (Real.arccos (inner ℝ (V₀ : E3) (V₁ : E3))) := by
    simp only [stdTriArea, luneAngle, sphExcess, sphAngle, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    rw [hc01, hc12, hc20]
    ring
  exact ⟨hliV, hliw, harea⟩

private lemma det3_kite_ne_zero {hdm θ₁ θ₂ : ℝ} (hd : 0 < Real.sin hdm)
    (hs : 0 < Real.sin (θ₁ + θ₂)) :
    det3 !₂[0, Real.sin θ₁, Real.cos θ₁] !₂[Real.sin hdm, 0, Real.cos hdm]
      !₂[0, -Real.sin θ₂, Real.cos θ₂] ≠ 0 := by
  have hval :
      det3 !₂[0, Real.sin θ₁, Real.cos θ₁] !₂[Real.sin hdm, 0, Real.cos hdm]
          !₂[0, -Real.sin θ₂, Real.cos θ₂] =
        -(Real.sin hdm * Real.sin (θ₁ + θ₂)) := by
    simp only [det3, cross3, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [Real.sin_add]
    ring
  rw [hval]
  exact neg_ne_zero.mpr (mul_pos hd hs).ne'

private lemma mem_triSet_three (a b c y : ↑(Metric.sphere (0 : E3) 1)) :
    y ∈ triSet ![a, b, c] ↔
      0 ≤ inner ℝ (a : E3) (y : E3) ∧
      0 ≤ inner ℝ (b : E3) (y : E3) ∧
      0 ≤ inner ℝ (c : E3) (y : E3) := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
  · rintro ⟨ha, hb, hc⟩ k
    fin_cases k
    · simpa using ha
    · simpa using hb
    · simpa using hc

private lemma triSet_sphExcess_eq {V₀ V₁ V₂ w₀ w₁ w₂ : ↑(Metric.sphere (0 : E3) 1)}
    (a0 : inner ℝ (w₀ : E3) (V₀ : E3) = 0) (a1 : inner ℝ (w₀ : E3) (V₁ : E3) = 0)
    (a2 : 0 < inner ℝ (w₀ : E3) (V₂ : E3))
    (b1 : inner ℝ (w₁ : E3) (V₁ : E3) = 0) (b2 : inner ℝ (w₁ : E3) (V₂ : E3) = 0)
    (b0 : 0 < inner ℝ (w₁ : E3) (V₀ : E3))
    (c2 : inner ℝ (w₂ : E3) (V₂ : E3) = 0) (c0 : inner ℝ (w₂ : E3) (V₀ : E3) = 0)
    (c1 : 0 < inner ℝ (w₂ : E3) (V₁ : E3)) :
    MeasureTheory.volume.toSphere.real (triSet ![w₀, w₁, w₂]) =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
        sphExcess (Real.arccos (inner ℝ (V₁ : E3) (V₂ : E3)))
          (Real.arccos (inner ℝ (V₂ : E3) (V₀ : E3)))
          (Real.arccos (inner ℝ (V₀ : E3) (V₁ : E3))) := by
  obtain ⟨_, hw_li, harea⟩ := stdTriArea_eq_sphExcess a0 a1 a2 b1 b2 b0 c2 c0 c1
  have hw_li' : LinearIndependent ℝ (fun k : Fin 3 => (![w₀, w₁, w₂] k : E3)) := by
    convert hw_li using 1
    ext k
    fin_cases k <;> rfl
  rw [toSphere_real_triSet ![w₀, w₁, w₂] hw_li', harea]

private lemma sphere3_E3_univ_pos :
    0 < MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.toSphere_apply_univ]
  have hball : 0 < (MeasureTheory.volume (Metric.ball (0 : E3) 1)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos MeasureTheory.volume (0 : E3) one_pos,
      MeasureTheory.measure_ball_lt_top⟩
  have hcard : (0 : ℝ) < Module.finrank ℝ E3 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  rw [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast]
  exact mul_pos hcard hball

private lemma norm_E3_unit_of_sin_cos_half (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    ‖(!₂[x, 0, y] : E3)‖ = 1 := by
  have hsq : ‖(!₂[x, 0, y] : E3)‖ ^ 2 = 1 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    linarith
  nlinarith [norm_nonneg (!₂[x, 0, y] : E3)]

private lemma norm_E3_unit_of_yz (y z : ℝ) (h : y ^ 2 + z ^ 2 = 1) :
    ‖(!₂[0, y, z] : E3)‖ = 1 := by
  have hsq : ‖(!₂[0, y, z] : E3)‖ ^ 2 = 1 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    linarith
  nlinarith [norm_nonneg (!₂[0, y, z] : E3)]

private lemma sphExcess_kite_half_eq_d2 {m₁ m₂ d θ₁ : ℝ}
    (hd0 : 0 < d) (hd1 : d < Real.pi)
    (hm1_lo : d / 2 < m₁) (hm1_hi : m₁ < Real.pi - d / 2)
    (hm2_eq : m₂ = d / 2)
    (hθ1_pos : 0 < θ₁) (hθ1_lt : θ₁ < Real.pi)
    (hcos_θ1 : Real.cos θ₁ = Real.cos m₁ / Real.cos (d / 2)) :
    sphExcess m₁ m₁ d = 2 * sphExcess m₁ m₂ θ₁ := by
  have hd2_pos : 0 < d / 2 := by linarith
  have hd2_lt : d / 2 < Real.pi / 2 := by linarith
  have hcos_d : 0 < Real.cos (d / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd2_lt⟩
  have hsin_d : 0 < Real.sin (d / 2) := Real.sin_pos_of_pos_of_lt_pi hd2_pos (by linarith [Real.pi_pos])
  have hsin_θ1 : 0 < Real.sin θ₁ := Real.sin_pos_of_pos_of_lt_pi hθ1_pos hθ1_lt
  let Bv : E3 := !₂[Real.sin (d / 2), 0, Real.cos (d / 2)]
  let Cv : E3 := !₂[-Real.sin (d / 2), 0, Real.cos (d / 2)]
  let A₁v : E3 := !₂[0, Real.sin θ₁, Real.cos θ₁]
  let A₂v : E3 := !₂[0, 0, 1]
  have hBnorm : ‖Bv‖ = 1 := norm_E3_unit_of_sin_cos_half _ _ (Real.sin_sq_add_cos_sq (d / 2))
  have hCnorm : ‖Cv‖ = 1 := by
    apply norm_E3_unit_of_sin_cos_half
    nlinarith [Real.sin_sq_add_cos_sq (d / 2)]
  have hA1norm : ‖A₁v‖ = 1 := norm_E3_unit_of_yz _ _ (Real.sin_sq_add_cos_sq θ₁)
  have hA2norm : ‖A₂v‖ = 1 := norm_E3_unit_of_yz 0 1 (by norm_num)
  let Bs : ↑(Metric.sphere (0 : E3) 1) := ⟨Bv, mem_sphere_zero_iff_norm.mpr hBnorm⟩
  let Cs : ↑(Metric.sphere (0 : E3) 1) := ⟨Cv, mem_sphere_zero_iff_norm.mpr hCnorm⟩
  let A₁s : ↑(Metric.sphere (0 : E3) 1) := ⟨A₁v, mem_sphere_zero_iff_norm.mpr hA1norm⟩
  let A₂s : ↑(Metric.sphere (0 : E3) 1) := ⟨A₂v, mem_sphere_zero_iff_norm.mpr hA2norm⟩
  have hd_A1B : Real.arccos (inner ℝ A₁v Bv) = m₁ := by
    have hip : inner ℝ A₁v Bv = Real.cos m₁ := by
      simp only [A₁v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hcos_θ1]; field_simp [hcos_d.ne']; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_A1C : Real.arccos (inner ℝ A₁v Cv) = m₁ := by
    have hip : inner ℝ A₁v Cv = Real.cos m₁ := by
      simp only [A₁v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hcos_θ1]; field_simp [hcos_d.ne']; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_A2B : Real.arccos (inner ℝ A₂v Bv) = m₂ := by
    have hip : inner ℝ A₂v Bv = Real.cos m₂ := by
      simp only [A₂v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hm2_eq]; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_A2C : Real.arccos (inner ℝ A₂v Cv) = m₂ := by
    have hip : inner ℝ A₂v Cv = Real.cos m₂ := by
      simp only [A₂v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hm2_eq]; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_BC : Real.arccos (inner ℝ Bv Cv) = d := by
    have hip : inner ℝ Bv Cv = Real.cos d := by
      simp only [Bv, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hc : Real.cos d = Real.cos (d / 2) ^ 2 - Real.sin (d / 2) ^ 2 := by
        have := Real.cos_two_mul (d / 2)
        rw [show 2 * (d / 2) = d by ring] at this
        have := Real.sin_sq_add_cos_sq (d / 2); linarith
      rw [hc]; ring
    rw [hip, Real.arccos_cos hd0.le hd1.le]
  have hd_A1A2 : Real.arccos (inner ℝ A₁v A₂v) = θ₁ := by
    have hip : inner ℝ A₁v A₂v = Real.cos θ₁ := by
      simp only [A₁v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [hip, Real.arccos_cos hθ1_pos.le hθ1_lt.le]
  let n1v : E3 := !₂[-Real.sin θ₁ * Real.cos (d / 2), -Real.cos θ₁ * Real.sin (d / 2), Real.sin θ₁ * Real.sin (d / 2)]
  let n2v : E3 := !₂[Real.sin θ₁ * Real.cos (d / 2), -Real.cos θ₁ * Real.sin (d / 2), Real.sin θ₁ * Real.sin (d / 2)]
  have hn1_sq : ‖n1v‖ ^ 2 = (Real.sin θ₁ * Real.cos (d / 2)) ^ 2 + Real.sin (d / 2) ^ 2 := by
    simp only [n1v, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    nlinarith [Real.sin_sq_add_cos_sq θ₁]
  have hn1_pos : 0 < ‖n1v‖ := by
    have hsq : 0 < ‖n1v‖ ^ 2 := by rw [hn1_sq]; positivity
    exact norm_pos_iff.mpr (fun h => by rw [h, norm_zero, zero_pow (by norm_num)] at hsq; linarith)
  have hn2_norm : ‖n2v‖ = ‖n1v‖ := by
    have hsq : ‖n2v‖ ^ 2 = ‖n1v‖ ^ 2 := by
      simp only [n2v, n1v, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    nlinarith [norm_nonneg n2v, norm_nonneg n1v]
  let e0v : E3 := !₂[1, 0, 0]
  let e1v : E3 := !₂[0, 1, 0]
  have he0n : ‖e0v‖ = 1 := norm_E3_unit_of_sin_cos_half 1 0 (by norm_num)
  have he1n : ‖e1v‖ = 1 := norm_E3_unit_of_yz 1 0 (by norm_num)
  let e0s : ↑(Metric.sphere (0 : E3) 1) := ⟨e0v, mem_sphere_zero_iff_norm.mpr he0n⟩
  let e1s : ↑(Metric.sphere (0 : E3) 1) := ⟨e1v, mem_sphere_zero_iff_norm.mpr he1n⟩
  let ne0s : ↑(Metric.sphere (0 : E3) 1) := ⟨-e0v, mem_sphere_zero_iff_norm.mpr (by simp [he0n])⟩
  let w1v : E3 := (1 / ‖n1v‖) • n1v
  let w2v : E3 := (1 / ‖n2v‖) • n2v
  have hw1n : ‖w1v‖ = 1 := by
    dsimp [w1v]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn1_pos),
      one_div_mul_cancel hn1_pos.ne']
  have hw2n : ‖w2v‖ = 1 := by
    have hn2_pos : 0 < ‖n2v‖ := hn2_norm ▸ hn1_pos
    dsimp [w2v]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn2_pos),
      one_div_mul_cancel hn2_pos.ne']
  let w1s : ↑(Metric.sphere (0 : E3) 1) := ⟨w1v, mem_sphere_zero_iff_norm.mpr hw1n⟩
  let w2s : ↑(Metric.sphere (0 : E3) 1) := ⟨w2v, mem_sphere_zero_iff_norm.mpr hw2n⟩
  have hn1_A1 : inner ℝ n1v A₁v = 0 := by
    simp [n1v, A₁v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn1_B : inner ℝ n1v Bv = 0 := by
    simp [n1v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn1_C : 0 < inner ℝ n1v Cv := by
    have hval : inner ℝ n1v Cv = 2 * Real.sin θ₁ * Real.sin (d / 2) * Real.cos (d / 2) := by
      simp [n1v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn1_A2 : 0 < inner ℝ n1v A₂v := by
    have hval : inner ℝ n1v A₂v = Real.sin (d / 2) * Real.sin θ₁ := by
      simp [n1v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn2_A1 : inner ℝ n2v A₁v = 0 := by
    simp [n2v, A₁v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn2_C : inner ℝ n2v Cv = 0 := by
    simp [n2v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn2_B : 0 < inner ℝ n2v Bv := by
    have hval : inner ℝ n2v Bv = 2 * Real.sin θ₁ * Real.sin (d / 2) * Real.cos (d / 2) := by
      simp [n2v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn2_A2 : 0 < inner ℝ n2v A₂v := by
    have hval : inner ℝ n2v A₂v = Real.sin (d / 2) * Real.sin θ₁ := by
      simp [n2v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hm1_excess :
      MeasureTheory.volume.toSphere.real (triSet ![w1s, e1s, w2s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₁ m₁ d := by
    have htri := triSet_sphExcess_eq (V₀ := A₁s) (V₁ := Bs) (V₂ := Cs) (w₀ := w1s) (w₁ := e1s) (w₂ := w2s)
      (by dsimp [w1s, w1v, A₁s]; rw [inner_smul_left, hn1_A1, mul_zero])
      (by dsimp [w1s, w1v, Bs]; rw [inner_smul_left, hn1_B, mul_zero])
      (by dsimp [w1s, w1v, Cs]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr hn1_pos) hn1_C)
      (by simp [e1s, e1v, Bs, Bv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, Cs, Cv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_θ1)
      (by dsimp [w2s, w2v, Cs]; rw [inner_smul_left, hn2_C, mul_zero])
      (by dsimp [w2s, w2v, A₁s]; rw [inner_smul_left, hn2_A1, mul_zero])
      (by dsimp [w2s, w2v, Bs]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr (hn2_norm ▸ hn1_pos)) hn2_B)
    dsimp [Bs, Cs, A₁s] at htri
    rw [real_inner_comm A₁v Cv, hd_BC, hd_A1C, hd_A1B,
        sphExcess_perm_cyc m₁ d m₁, sphExcess_perm_cyc m₁ m₁ d] at htri
    exact htri
  have hhalf1 :
      MeasureTheory.volume.toSphere.real (triSet ![e0s, w1s, e1s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₁ m₂ θ₁ := by
    have htri := triSet_sphExcess_eq (V₀ := A₂s) (V₁ := A₁s) (V₂ := Bs) (w₀ := e0s) (w₁ := w1s) (w₂ := e1s)
      (by simp [e0s, e0v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e0s, e0v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e0s, e0v, Bs, Bv, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_d)
      (by dsimp [w1s, w1v, A₁s]; rw [inner_smul_left, hn1_A1, mul_zero])
      (by dsimp [w1s, w1v, Bs]; rw [inner_smul_left, hn1_B, mul_zero])
      (by dsimp [w1s, w1v, A₂s]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr hn1_pos) hn1_A2)
      (by simp [e1s, e1v, Bs, Bv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_θ1)
    dsimp [A₁s, Bs, A₂s] at htri
    rw [real_inner_comm A₂v Bv, real_inner_comm A₁v A₂v, hd_A1B, hd_A2B, hd_A1A2] at htri
    exact htri
  have hhalf2 :
      MeasureTheory.volume.toSphere.real (triSet ![ne0s, e1s, w2s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₁ m₂ θ₁ := by
    have htri := triSet_sphExcess_eq (V₀ := A₁s) (V₁ := A₂s) (V₂ := Cs) (w₀ := ne0s) (w₁ := e1s) (w₂ := w2s)
      (by simp [ne0s, e0v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [ne0s, e0v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [ne0s, e0v, Cs, Cv, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_d)
      (by simp [e1s, e1v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, Cs, Cv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_θ1)
      (by dsimp [w2s, w2v, Cs]; rw [inner_smul_left, hn2_C, mul_zero])
      (by dsimp [w2s, w2v, A₁s]; rw [inner_smul_left, hn2_A1, mul_zero])
      (by dsimp [w2s, w2v, A₂s]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr (hn2_norm ▸ hn1_pos)) hn2_A2)
    dsimp [A₁s, Cs, A₂s] at htri
    rw [real_inner_comm A₁v Cv, hd_A2C, hd_A1C, hd_A1A2, sphExcess_perm_12] at htri
    exact htri
  have hunion_eq : triSet ![w1s, e1s, w2s] = triSet ![e0s, w1s, e1s] ∪ triSet ![ne0s, e1s, w2s] := by
    ext y
    simp only [Set.mem_union, mem_triSet_three]
    have hy_diff : inner ℝ (w2s : E3) (y : E3) - inner ℝ (w1s : E3) (y : E3) =
        (2 * Real.sin θ₁ * Real.cos (d / 2) / ‖n1v‖) * inner ℝ e0v (y : E3) := by
      have hw2_eq : (w2s : E3) = (1 / ‖n1v‖) • n2v := by dsimp [w2s, w2v]; rw [hn2_norm]
      rw [hw2_eq]
      change inner ℝ ((1 / ‖n1v‖) • n2v) (y : E3) - inner ℝ ((1 / ‖n1v‖) • n1v) (y : E3) = _
      rw [inner_smul_left, inner_smul_left, ← mul_sub]
      simp only [conj_trivial]
      rw [← inner_sub_left]
      have hsub_n : n2v - n1v = (2 * Real.sin θ₁ * Real.cos (d / 2)) • e0v := by
        ext i; fin_cases i <;> simp [n2v, n1v, e0v] <;> ring
      rw [hsub_n, inner_smul_left]
      simp only [conj_trivial]
      ring
    have hcoef_pos : 0 < 2 * Real.sin θ₁ * Real.cos (d / 2) / ‖n1v‖ := by positivity
    have he0_eq : inner ℝ (e0s : E3) (y : E3) = inner ℝ e0v (y : E3) := rfl
    have hne0 : inner ℝ (ne0s : E3) (y : E3) = -inner ℝ e0v (y : E3) := by
      change inner ℝ (-e0v) (y : E3) = -inner ℝ e0v (y : E3); simp [inner_neg_left]
    rw [he0_eq, hne0]
    constructor
    · rintro ⟨hw1y, he1y, hw2y⟩
      rcases le_total 0 (inner ℝ e0v (y : E3)) with h0 | h0
      · left; exact ⟨h0, hw1y, he1y⟩
      · right; exact ⟨by linarith, he1y, hw2y⟩
    · rintro (⟨h0, hw1y, he1y⟩ | ⟨h0, he1y, hw2y⟩)
      · have hprod : 0 ≤ (2 * Real.sin θ₁ * Real.cos (d / 2) / ‖n1v‖) * inner ℝ e0v (y : E3) :=
          mul_nonneg hcoef_pos.le h0
        exact ⟨hw1y, he1y, by linarith⟩
      · have h0' : inner ℝ e0v (y : E3) ≤ 0 := by linarith
        have hprod : (2 * Real.sin θ₁ * Real.cos (d / 2) / ‖n1v‖) * inner ℝ e0v (y : E3) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hcoef_pos.le h0'
        exact ⟨by linarith, he1y, hw2y⟩
  have hinter_null : MeasureTheory.volume.toSphere
      (triSet ![e0s, w1s, e1s] ∩ triSet ![ne0s, e1s, w2s]) = 0 := by
    have hsub : triSet ![e0s, w1s, e1s] ∩ triSet ![ne0s, e1s, w2s] ⊆
        {z : ↑(Metric.sphere (0 : E3) 1) | inner ℝ e0v (z : E3) = 0} := by
      intro z ⟨hz1, hz2⟩
      have h1 : 0 ≤ inner ℝ e0v (z : E3) := ((mem_triSet_three e0s w1s e1s z).mp hz1).1
      have h2 : 0 ≤ inner ℝ (-e0v) (z : E3) := ((mem_triSet_three ne0s e1s w2s z).mp hz2).1
      rw [inner_neg_left] at h2
      exact le_antisymm (by linarith) h1
    exact MeasureTheory.measure_mono_null hsub
      (toSphere_hyperplane_null e0v (by intro h; rw [h, norm_zero] at he0n; norm_num at he0n))
  have hsum_meas := measureReal_union_inter_null MeasureTheory.volume.toSphere
    (triSet_measurableSet ![e0s, w1s, e1s]) (triSet_measurableSet ![ne0s, e1s, w2s]) hinter_null
  rw [← hunion_eq, hm1_excess, hhalf1, hhalf2] at hsum_meas
  have hM : 0 < MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) :=
    div_pos sphere3_E3_univ_pos (by positivity [Real.pi_pos])
  have hfactor :
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
        sphExcess m₁ m₁ d =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
        (2 * sphExcess m₁ m₂ θ₁) := by linarith only [hsum_meas]
  exact mul_left_cancel₀ hM.ne' hfactor

private lemma kite_quad_partition_measure_eq
    {w1s w2s w3s w4s e0s e1s ne0s ne1s : ↑(Metric.sphere (0 : E3) 1)}
    (hne0 : (ne0s : E3) = -(e0s : E3)) (hne1 : (ne1s : E3) = -(e1s : E3))
    {c1 c2 c3 c4 cr p1 p2 : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (hc4 : 0 < c4)
    (hcr : 0 < cr) (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hdiff1 : ∀ y : ↑(Metric.sphere (0 : E3) 1),
      c3 * inner ℝ (w3s : E3) (y : E3) - c1 * inner ℝ (w1s : E3) (y : E3) =
        cr * inner ℝ (e1s : E3) (y : E3))
    (hdiff2 : ∀ y : ↑(Metric.sphere (0 : E3) 1),
      c4 * inner ℝ (w4s : E3) (y : E3) - c2 * inner ℝ (w2s : E3) (y : E3) =
        cr * inner ℝ (e1s : E3) (y : E3))
    (hd12 : ∀ y : ↑(Metric.sphere (0 : E3) 1),
      inner ℝ (w2s : E3) (y : E3) - inner ℝ (w1s : E3) (y : E3) =
        p1 * inner ℝ (e0s : E3) (y : E3))
    (hd34 : ∀ y : ↑(Metric.sphere (0 : E3) 1),
      inner ℝ (w4s : E3) (y : E3) - inner ℝ (w3s : E3) (y : E3) =
        p2 * inner ℝ (e0s : E3) (y : E3)) :
    MeasureTheory.volume.toSphere.real (triSet ![w1s, e1s, w2s]) +
      MeasureTheory.volume.toSphere.real (triSet ![w3s, ne1s, w4s]) =
    MeasureTheory.volume.toSphere.real (triSet ![e0s, w1s, w3s]) +
      MeasureTheory.volume.toSphere.real (triSet ![ne0s, w4s, w2s]) := by
  let Pkite : Set ↑(Metric.sphere (0 : E3) 1) :=
    {y | 0 ≤ inner ℝ (w1s : E3) (y : E3) ∧ 0 ≤ inner ℝ (w2s : E3) (y : E3) ∧
         0 ≤ inner ℝ (w3s : E3) (y : E3) ∧ 0 ≤ inner ℝ (w4s : E3) (y : E3)}
  have he0_ne : (e0s : E3) ≠ 0 := by
    have hn : ‖(e0s : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp e0s.2
    intro h; rw [h, norm_zero] at hn; norm_num at hn
  have he1_ne : (e1s : E3) ≠ 0 := by
    have hn : ‖(e1s : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp e1s.2
    intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hcut_y1 : Pkite = triSet ![w1s, e1s, w2s] ∪ triSet ![w3s, ne1s, w4s] := by
    ext y
    simp only [Pkite, Set.mem_setOf_eq, Set.mem_union, mem_triSet_three]
    have hd1 := hdiff1 y
    have hd2 := hdiff2 y
    have hne1_ip : inner ℝ (ne1s : E3) (y : E3) = -inner ℝ (e1s : E3) (y : E3) := by
      rw [hne1, inner_neg_left]
    rw [hne1_ip]
    constructor
    · rintro ⟨hw1y, hw2y, hw3y, hw4y⟩
      rcases le_total 0 (inner ℝ (e1s : E3) (y : E3)) with h0 | h0
      · left; exact ⟨hw1y, h0, hw2y⟩
      · right; exact ⟨hw3y, by linarith only [h0], hw4y⟩
    · rintro (⟨hw1y, he1y, hw2y⟩ | ⟨hw3y, he1y, hw4y⟩)
      · have h1p : 0 ≤ c1 * inner ℝ (w1s : E3) (y : E3) := mul_nonneg hc1.le hw1y
        have h2p : 0 ≤ c2 * inner ℝ (w2s : E3) (y : E3) := mul_nonneg hc2.le hw2y
        have hpos_r : 0 ≤ cr * inner ℝ (e1s : E3) (y : E3) := mul_nonneg hcr.le he1y
        have h3p : 0 ≤ c3 * inner ℝ (w3s : E3) (y : E3) := by linarith only [hd1, h1p, hpos_r]
        have h4p : 0 ≤ c4 * inner ℝ (w4s : E3) (y : E3) := by linarith only [hd2, h2p, hpos_r]
        exact ⟨hw1y, hw2y, (mul_nonneg_iff_of_pos_left hc3).mp h3p, (mul_nonneg_iff_of_pos_left hc4).mp h4p⟩
      · have h3p : 0 ≤ c3 * inner ℝ (w3s : E3) (y : E3) := mul_nonneg hc3.le hw3y
        have h4p : 0 ≤ c4 * inner ℝ (w4s : E3) (y : E3) := mul_nonneg hc4.le hw4y
        have hneg : cr * inner ℝ (e1s : E3) (y : E3) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hcr.le (by linarith only [he1y])
        have h1p : 0 ≤ c1 * inner ℝ (w1s : E3) (y : E3) := by linarith only [hd1, h3p, hneg]
        have h2p : 0 ≤ c2 * inner ℝ (w2s : E3) (y : E3) := by linarith only [hd2, h4p, hneg]
        exact ⟨(mul_nonneg_iff_of_pos_left hc1).mp h1p, (mul_nonneg_iff_of_pos_left hc2).mp h2p, hw3y, hw4y⟩
  have hcut_y0 : Pkite = triSet ![e0s, w1s, w3s] ∪ triSet ![ne0s, w4s, w2s] := by
    ext y
    simp only [Pkite, Set.mem_setOf_eq, Set.mem_union, mem_triSet_three]
    have hy12 := hd12 y
    have hy34 := hd34 y
    have hne0_ip : inner ℝ (ne0s : E3) (y : E3) = -inner ℝ (e0s : E3) (y : E3) := by
      rw [hne0, inner_neg_left]
    rw [hne0_ip]
    constructor
    · rintro ⟨hw1y, hw2y, hw3y, hw4y⟩
      rcases le_total 0 (inner ℝ (e0s : E3) (y : E3)) with h0 | h0
      · left; exact ⟨h0, hw1y, hw3y⟩
      · right; exact ⟨by linarith only [h0], hw4y, hw2y⟩
    · rintro (⟨he0y, hw1y, hw3y⟩ | ⟨he0y, hw4y, hw2y⟩)
      · have hpos1 : 0 ≤ p1 * inner ℝ (e0s : E3) (y : E3) := mul_nonneg hp1.le he0y
        have hpos2 : 0 ≤ p2 * inner ℝ (e0s : E3) (y : E3) := mul_nonneg hp2.le he0y
        exact ⟨hw1y, by linarith only [hy12, hw1y, hpos1], hw3y, by linarith only [hy34, hw3y, hpos2]⟩
      · have he0le : inner ℝ (e0s : E3) (y : E3) ≤ 0 := by linarith only [he0y]
        have hneg1 : p1 * inner ℝ (e0s : E3) (y : E3) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp1.le he0le
        have hneg2 : p2 * inner ℝ (e0s : E3) (y : E3) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp2.le he0le
        exact ⟨by linarith only [hy12, hw2y, hneg1], hw2y, by linarith only [hy34, hw4y, hneg2], hw4y⟩
  have hint1 : MeasureTheory.volume.toSphere (triSet ![w1s, e1s, w2s] ∩ triSet ![w3s, ne1s, w4s]) = 0 := by
    have hsub : triSet ![w1s, e1s, w2s] ∩ triSet ![w3s, ne1s, w4s] ⊆
        {z : ↑(Metric.sphere (0 : E3) 1) | inner ℝ (e1s : E3) (z : E3) = 0} := by
      intro z ⟨hz1, hz2⟩
      have h1 : 0 ≤ inner ℝ (e1s : E3) (z : E3) := ((mem_triSet_three w1s e1s w2s z).mp hz1).2.1
      have h2 : 0 ≤ inner ℝ (ne1s : E3) (z : E3) := ((mem_triSet_three w3s ne1s w4s z).mp hz2).2.1
      rw [hne1, inner_neg_left] at h2
      exact le_antisymm (by linarith only [h2]) h1
    exact MeasureTheory.measure_mono_null hsub (toSphere_hyperplane_null (e1s : E3) he1_ne)
  have hint0 : MeasureTheory.volume.toSphere (triSet ![e0s, w1s, w3s] ∩ triSet ![ne0s, w4s, w2s]) = 0 := by
    have hsub : triSet ![e0s, w1s, w3s] ∩ triSet ![ne0s, w4s, w2s] ⊆
        {z : ↑(Metric.sphere (0 : E3) 1) | inner ℝ (e0s : E3) (z : E3) = 0} := by
      intro z ⟨hz1, hz2⟩
      have h1 : 0 ≤ inner ℝ (e0s : E3) (z : E3) := ((mem_triSet_three e0s w1s w3s z).mp hz1).1
      have h2 : 0 ≤ inner ℝ (ne0s : E3) (z : E3) := ((mem_triSet_three ne0s w4s w2s z).mp hz2).1
      rw [hne0, inner_neg_left] at h2
      exact le_antisymm (by linarith only [h2]) h1
    exact MeasureTheory.measure_mono_null hsub (toSphere_hyperplane_null (e0s : E3) he0_ne)
  have hsum1 := measureReal_union_inter_null MeasureTheory.volume.toSphere
    (triSet_measurableSet ![w1s, e1s, w2s]) (triSet_measurableSet ![w3s, ne1s, w4s]) hint1
  have hsum0 := measureReal_union_inter_null MeasureTheory.volume.toSphere
    (triSet_measurableSet ![e0s, w1s, w3s]) (triSet_measurableSet ![ne0s, w4s, w2s]) hint0
  rw [← hcut_y1] at hsum1
  rw [← hcut_y0] at hsum0
  exact hsum1.symm.trans hsum0

private lemma sphExcess_kite_half_gt_d2 {m₁ m₂ d θ₁ θ₂ : ℝ}
    (hd0 : 0 < d) (hd1 : d < Real.pi)
    (hm1_lo : d / 2 < m₁) (hm1_hi : m₁ < Real.pi - d / 2)
    (hm2_gt : d / 2 < m₂) (hm2_hi : m₂ < Real.pi - d / 2)
    (hθ1_pos : 0 < θ₁) (hθ1_lt : θ₁ < Real.pi)
    (hθ2_pos : 0 < θ₂) (hθ2_lt : θ₂ < Real.pi)
    (hd'_lt_pi : θ₁ + θ₂ < Real.pi)
    (hcos_θ1 : Real.cos θ₁ = Real.cos m₁ / Real.cos (d / 2))
    (hcos_θ2 : Real.cos θ₂ = Real.cos m₂ / Real.cos (d / 2)) :
    sphExcess m₁ m₁ d + sphExcess m₂ m₂ d = 2 * sphExcess m₁ m₂ (θ₁ + θ₂) := by
  have hd2_pos : 0 < d / 2 := by linarith
  have hd2_lt : d / 2 < Real.pi / 2 := by linarith
  have hcos_d : 0 < Real.cos (d / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd2_lt⟩
  have hsin_d : 0 < Real.sin (d / 2) := Real.sin_pos_of_pos_of_lt_pi hd2_pos (by linarith [Real.pi_pos])
  have hsin_θ1 : 0 < Real.sin θ₁ := Real.sin_pos_of_pos_of_lt_pi hθ1_pos hθ1_lt
  have hsin_θ2 : 0 < Real.sin θ₂ := Real.sin_pos_of_pos_of_lt_pi hθ2_pos hθ2_lt
  have hd'_pos : 0 < θ₁ + θ₂ := by linarith
  have hsin_sum_pos : 0 < Real.sin (θ₁ + θ₂) := Real.sin_pos_of_pos_of_lt_pi hd'_pos hd'_lt_pi
  let Bv : E3 := !₂[Real.sin (d / 2), 0, Real.cos (d / 2)]
  let Cv : E3 := !₂[-Real.sin (d / 2), 0, Real.cos (d / 2)]
  let A₁v : E3 := !₂[0, Real.sin θ₁, Real.cos θ₁]
  let A₂v : E3 := !₂[0, -Real.sin θ₂, Real.cos θ₂]
  have hBnorm : ‖Bv‖ = 1 := norm_E3_unit_of_sin_cos_half _ _ (Real.sin_sq_add_cos_sq (d / 2))
  have hCnorm : ‖Cv‖ = 1 := norm_E3_unit_of_sin_cos_half _ _ (by nlinarith [Real.sin_sq_add_cos_sq (d / 2)])
  have hA1norm : ‖A₁v‖ = 1 := norm_E3_unit_of_yz _ _ (Real.sin_sq_add_cos_sq θ₁)
  have hA2norm : ‖A₂v‖ = 1 := norm_E3_unit_of_yz _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ₂])
  let Bs : ↑(Metric.sphere (0 : E3) 1) := ⟨Bv, mem_sphere_zero_iff_norm.mpr hBnorm⟩
  let Cs : ↑(Metric.sphere (0 : E3) 1) := ⟨Cv, mem_sphere_zero_iff_norm.mpr hCnorm⟩
  let A₁s : ↑(Metric.sphere (0 : E3) 1) := ⟨A₁v, mem_sphere_zero_iff_norm.mpr hA1norm⟩
  let A₂s : ↑(Metric.sphere (0 : E3) 1) := ⟨A₂v, mem_sphere_zero_iff_norm.mpr hA2norm⟩
  have hd_A1B : Real.arccos (inner ℝ A₁v Bv) = m₁ := by
    have hip : inner ℝ A₁v Bv = Real.cos m₁ := by
      simp only [A₁v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hcos_θ1]; field_simp [hcos_d.ne']; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_A1C : Real.arccos (inner ℝ A₁v Cv) = m₁ := by
    have hip : inner ℝ A₁v Cv = Real.cos m₁ := by
      simp only [A₁v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hcos_θ1]; field_simp [hcos_d.ne']; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_A2B : Real.arccos (inner ℝ A₂v Bv) = m₂ := by
    have hip : inner ℝ A₂v Bv = Real.cos m₂ := by
      simp only [A₂v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hcos_θ2]; field_simp [hcos_d.ne']; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_A2C : Real.arccos (inner ℝ A₂v Cv) = m₂ := by
    have hip : inner ℝ A₂v Cv = Real.cos m₂ := by
      simp only [A₂v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [hcos_θ2]; field_simp [hcos_d.ne']; ring
    rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
  have hd_BC : Real.arccos (inner ℝ Bv Cv) = d := by
    have hip : inner ℝ Bv Cv = Real.cos d := by
      simp only [Bv, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hc : Real.cos d = Real.cos (d / 2) ^ 2 - Real.sin (d / 2) ^ 2 := by
        have := Real.cos_two_mul (d / 2)
        rw [show 2 * (d / 2) = d by ring] at this
        have := Real.sin_sq_add_cos_sq (d / 2); linarith
      rw [hc]; ring
    rw [hip, Real.arccos_cos hd0.le hd1.le]
  have hd_A1A2 : Real.arccos (inner ℝ A₁v A₂v) = θ₁ + θ₂ := by
    have hip : inner ℝ A₁v A₂v = Real.cos (θ₁ + θ₂) := by
      simp only [A₁v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [Real.cos_add]; ring
    rw [hip, Real.arccos_cos hd'_pos.le hd'_lt_pi.le]
  let n1v : E3 := !₂[-Real.sin θ₁ * Real.cos (d / 2), -Real.cos θ₁ * Real.sin (d / 2), Real.sin θ₁ * Real.sin (d / 2)]
  let n2v : E3 := !₂[Real.sin θ₁ * Real.cos (d / 2), -Real.cos θ₁ * Real.sin (d / 2), Real.sin θ₁ * Real.sin (d / 2)]
  let n3v : E3 := !₂[-Real.sin θ₂ * Real.cos (d / 2), Real.cos θ₂ * Real.sin (d / 2), Real.sin θ₂ * Real.sin (d / 2)]
  let n4v : E3 := !₂[Real.sin θ₂ * Real.cos (d / 2), Real.cos θ₂ * Real.sin (d / 2), Real.sin θ₂ * Real.sin (d / 2)]
  have hn1_sq : ‖n1v‖ ^ 2 = (Real.sin θ₁ * Real.cos (d / 2)) ^ 2 + Real.sin (d / 2) ^ 2 := by
    simp only [n1v, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← one_mul (Real.sin (d / 2) ^ 2), ← Real.sin_sq_add_cos_sq θ₁]; ring
  have hn1_pos : 0 < ‖n1v‖ := by
    have hsq : 0 < ‖n1v‖ ^ 2 := by rw [hn1_sq]; positivity
    exact norm_pos_iff.mpr (fun h => by rw [h, norm_zero, zero_pow (by norm_num)] at hsq; linarith)
  have hn2_norm : ‖n2v‖ = ‖n1v‖ := by
    have hsq : ‖n2v‖ ^ 2 = ‖n1v‖ ^ 2 := by
      simp only [n2v, n1v, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    rw [← Real.sqrt_sq (norm_nonneg n2v), ← Real.sqrt_sq (norm_nonneg n1v), hsq]
  have hn3_sq : ‖n3v‖ ^ 2 = (Real.sin θ₂ * Real.cos (d / 2)) ^ 2 + Real.sin (d / 2) ^ 2 := by
    simp only [n3v, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← one_mul (Real.sin (d / 2) ^ 2), ← Real.sin_sq_add_cos_sq θ₂]; ring
  have hn3_pos : 0 < ‖n3v‖ := by
    have hsq : 0 < ‖n3v‖ ^ 2 := by rw [hn3_sq]; positivity
    exact norm_pos_iff.mpr (fun h => by rw [h, norm_zero, zero_pow (by norm_num)] at hsq; linarith)
  have hn4_norm : ‖n4v‖ = ‖n3v‖ := by
    have hsq : ‖n4v‖ ^ 2 = ‖n3v‖ ^ 2 := by
      simp only [n4v, n3v, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    rw [← Real.sqrt_sq (norm_nonneg n4v), ← Real.sqrt_sq (norm_nonneg n3v), hsq]
  let e0v : E3 := !₂[1, 0, 0]
  let e1v : E3 := !₂[0, 1, 0]
  have he0n : ‖e0v‖ = 1 := norm_E3_unit_of_sin_cos_half 1 0 (by norm_num)
  have he1n : ‖e1v‖ = 1 := norm_E3_unit_of_yz 1 0 (by norm_num)
  let e0s : ↑(Metric.sphere (0 : E3) 1) := ⟨e0v, mem_sphere_zero_iff_norm.mpr he0n⟩
  let e1s : ↑(Metric.sphere (0 : E3) 1) := ⟨e1v, mem_sphere_zero_iff_norm.mpr he1n⟩
  let ne0s : ↑(Metric.sphere (0 : E3) 1) := ⟨-e0v, mem_sphere_zero_iff_norm.mpr (by simp [he0n])⟩
  let ne1s : ↑(Metric.sphere (0 : E3) 1) := ⟨-e1v, mem_sphere_zero_iff_norm.mpr (by simp [he1n])⟩
  let w1v : E3 := (1 / ‖n1v‖) • n1v
  let w2v : E3 := (1 / ‖n2v‖) • n2v
  let w3v : E3 := (1 / ‖n3v‖) • n3v
  let w4v : E3 := (1 / ‖n4v‖) • n4v
  have hw1n : ‖w1v‖ = 1 := by
    dsimp [w1v]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn1_pos),
      one_div_mul_cancel hn1_pos.ne']
  have hw2n : ‖w2v‖ = 1 := by
    have hn2_pos : 0 < ‖n2v‖ := hn2_norm ▸ hn1_pos
    dsimp [w2v]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn2_pos),
      one_div_mul_cancel hn2_pos.ne']
  have hw3n : ‖w3v‖ = 1 := by
    dsimp [w3v]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn3_pos),
      one_div_mul_cancel hn3_pos.ne']
  have hw4n : ‖w4v‖ = 1 := by
    have hn4_pos : 0 < ‖n4v‖ := hn4_norm ▸ hn3_pos
    dsimp [w4v]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn4_pos),
      one_div_mul_cancel hn4_pos.ne']
  let w1s : ↑(Metric.sphere (0 : E3) 1) := ⟨w1v, mem_sphere_zero_iff_norm.mpr hw1n⟩
  let w2s : ↑(Metric.sphere (0 : E3) 1) := ⟨w2v, mem_sphere_zero_iff_norm.mpr hw2n⟩
  let w3s : ↑(Metric.sphere (0 : E3) 1) := ⟨w3v, mem_sphere_zero_iff_norm.mpr hw3n⟩
  let w4s : ↑(Metric.sphere (0 : E3) 1) := ⟨w4v, mem_sphere_zero_iff_norm.mpr hw4n⟩
  have hn1_A1 : inner ℝ n1v A₁v = 0 := by
    simp [n1v, A₁v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn1_B : inner ℝ n1v Bv = 0 := by
    simp [n1v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn1_C : 0 < inner ℝ n1v Cv := by
    have hval : inner ℝ n1v Cv = 2 * Real.sin θ₁ * Real.sin (d / 2) * Real.cos (d / 2) := by
      simp [n1v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn1_A2 : 0 < inner ℝ n1v A₂v := by
    have hval : inner ℝ n1v A₂v = Real.sin (d / 2) * Real.sin (θ₁ + θ₂) := by
      simp [n1v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
      rw [Real.sin_add]; ring
    rw [hval]; positivity
  have hn2_A1 : inner ℝ n2v A₁v = 0 := by
    simp [n2v, A₁v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn2_C : inner ℝ n2v Cv = 0 := by
    simp [n2v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn2_B : 0 < inner ℝ n2v Bv := by
    have hval : inner ℝ n2v Bv = 2 * Real.sin θ₁ * Real.sin (d / 2) * Real.cos (d / 2) := by
      simp [n2v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn2_A2 : 0 < inner ℝ n2v A₂v := by
    have hval : inner ℝ n2v A₂v = Real.sin (d / 2) * Real.sin (θ₁ + θ₂) := by
      simp [n2v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
      rw [Real.sin_add]; ring
    rw [hval]; positivity
  have hn3_A2 : inner ℝ n3v A₂v = 0 := by
    simp [n3v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn3_B : inner ℝ n3v Bv = 0 := by
    simp [n3v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn3_C : 0 < inner ℝ n3v Cv := by
    have hval : inner ℝ n3v Cv = 2 * Real.sin θ₂ * Real.sin (d / 2) * Real.cos (d / 2) := by
      simp [n3v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn3_A1 : 0 < inner ℝ n3v A₁v := by
    have hval : inner ℝ n3v A₁v = Real.sin (d / 2) * Real.sin (θ₁ + θ₂) := by
      simp [n3v, A₁v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
      rw [Real.sin_add]; ring
    rw [hval]; positivity
  have hn4_A2 : inner ℝ n4v A₂v = 0 := by
    simp [n4v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn4_C : inner ℝ n4v Cv = 0 := by
    simp [n4v, Cv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
  have hn4_B : 0 < inner ℝ n4v Bv := by
    have hval : inner ℝ n4v Bv = 2 * Real.sin θ₂ * Real.sin (d / 2) * Real.cos (d / 2) := by
      simp [n4v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring
    rw [hval]; positivity
  have hn4_A1 : 0 < inner ℝ n4v A₁v := by
    have hval : inner ℝ n4v A₁v = Real.sin (d / 2) * Real.sin (θ₁ + θ₂) := by
      simp [n4v, A₁v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
      rw [Real.sin_add]; ring
    rw [hval]; positivity
  have hm1_excess :
      MeasureTheory.volume.toSphere.real (triSet ![w1s, e1s, w2s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₁ m₁ d := by
    have htri := triSet_sphExcess_eq (V₀ := A₁s) (V₁ := Bs) (V₂ := Cs) (w₀ := w1s) (w₁ := e1s) (w₂ := w2s)
      (by dsimp [w1s, w1v, A₁s]; rw [inner_smul_left, hn1_A1, mul_zero])
      (by dsimp [w1s, w1v, Bs]; rw [inner_smul_left, hn1_B, mul_zero])
      (by dsimp [w1s, w1v, Cs]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr hn1_pos) hn1_C)
      (by simp [e1s, e1v, Bs, Bv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, Cs, Cv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e1s, e1v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_θ1)
      (by dsimp [w2s, w2v, Cs]; rw [inner_smul_left, hn2_C, mul_zero])
      (by dsimp [w2s, w2v, A₁s]; rw [inner_smul_left, hn2_A1, mul_zero])
      (by dsimp [w2s, w2v, Bs]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr (hn2_norm ▸ hn1_pos)) hn2_B)
    dsimp [Bs, Cs, A₁s] at htri
    rw [real_inner_comm A₁v Cv, hd_BC, hd_A1C, hd_A1B,
        sphExcess_perm_cyc m₁ d m₁, sphExcess_perm_cyc m₁ m₁ d] at htri
    exact htri
  have hm2_excess :
      MeasureTheory.volume.toSphere.real (triSet ![w3s, ne1s, w4s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₂ m₂ d := by
    have htri := triSet_sphExcess_eq (V₀ := A₂s) (V₁ := Bs) (V₂ := Cs) (w₀ := w3s) (w₁ := ne1s) (w₂ := w4s)
      (by dsimp [w3s, w3v, A₂s]; rw [inner_smul_left, hn3_A2, mul_zero])
      (by dsimp [w3s, w3v, Bs]; rw [inner_smul_left, hn3_B, mul_zero])
      (by dsimp [w3s, w3v, Cs]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr hn3_pos) hn3_C)
      (by simp [ne1s, e1v, Bs, Bv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [ne1s, e1v, Cs, Cv, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [ne1s, e1v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_θ2)
      (by dsimp [w4s, w4v, Cs]; rw [inner_smul_left, hn4_C, mul_zero])
      (by dsimp [w4s, w4v, A₂s]; rw [inner_smul_left, hn4_A2, mul_zero])
      (by dsimp [w4s, w4v, Bs]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr (hn4_norm ▸ hn3_pos)) hn4_B)
    dsimp [Bs, Cs, A₂s] at htri
    rw [real_inner_comm A₂v Cv, hd_BC, hd_A2C, hd_A2B,
        sphExcess_perm_cyc m₂ d m₂, sphExcess_perm_cyc m₂ m₂ d] at htri
    exact htri
  have hhalf1 :
      MeasureTheory.volume.toSphere.real (triSet ![e0s, w1s, w3s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₁ m₂ (θ₁ + θ₂) := by
    have htri := triSet_sphExcess_eq (V₀ := A₂s) (V₁ := A₁s) (V₂ := Bs) (w₀ := e0s) (w₁ := w1s) (w₂ := w3s)
      (by simp [e0s, e0v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e0s, e0v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [e0s, e0v, Bs, Bv, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_d)
      (by dsimp [w1s, w1v, A₁s]; rw [inner_smul_left, hn1_A1, mul_zero])
      (by dsimp [w1s, w1v, Bs]; rw [inner_smul_left, hn1_B, mul_zero])
      (by dsimp [w1s, w1v, A₂s]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr hn1_pos) hn1_A2)
      (by dsimp [w3s, w3v, Bs]; rw [inner_smul_left, hn3_B, mul_zero])
      (by dsimp [w3s, w3v, A₂s]; rw [inner_smul_left, hn3_A2, mul_zero])
      (by dsimp [w3s, w3v, A₁s]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr hn3_pos) hn3_A1)
    dsimp [A₁s, Bs, A₂s] at htri
    rw [real_inner_comm A₂v Bv, real_inner_comm A₁v A₂v, hd_A1B, hd_A2B, hd_A1A2] at htri
    exact htri
  have hhalf2 :
      MeasureTheory.volume.toSphere.real (triSet ![ne0s, w4s, w2s]) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
          sphExcess m₁ m₂ (θ₁ + θ₂) := by
    have htri := triSet_sphExcess_eq (V₀ := A₁s) (V₁ := A₂s) (V₂ := Cs) (w₀ := ne0s) (w₁ := w4s) (w₂ := w2s)
      (by simp [ne0s, e0v, A₁s, A₁v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [ne0s, e0v, A₂s, A₂v, PiLp.inner_apply, Fin.sum_univ_three])
      (by simp [ne0s, e0v, Cs, Cv, PiLp.inner_apply, Fin.sum_univ_three]; exact hsin_d)
      (by dsimp [w4s, w4v, A₂s]; rw [inner_smul_left, hn4_A2, mul_zero])
      (by dsimp [w4s, w4v, Cs]; rw [inner_smul_left, hn4_C, mul_zero])
      (by dsimp [w4s, w4v, A₁s]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr (hn4_norm ▸ hn3_pos)) hn4_A1)
      (by dsimp [w2s, w2v, Cs]; rw [inner_smul_left, hn2_C, mul_zero])
      (by dsimp [w2s, w2v, A₁s]; rw [inner_smul_left, hn2_A1, mul_zero])
      (by dsimp [w2s, w2v, A₂s]; rw [inner_smul_left]; simp only [conj_trivial]; exact mul_pos (one_div_pos.mpr (hn2_norm ▸ hn1_pos)) hn2_A2)
    dsimp [A₁s, Cs, A₂s] at htri
    rw [real_inner_comm A₁v Cv, hd_A2C, hd_A1C, hd_A1A2, sphExcess_perm_12] at htri
    exact htri
  have htot := kite_quad_partition_measure_eq
    (w1s := w1s) (w2s := w2s) (w3s := w3s) (w4s := w4s)
    (e0s := e0s) (e1s := e1s) (ne0s := ne0s) (ne1s := ne1s)
    rfl rfl
    (c1 := ‖n1v‖ / Real.sin θ₁) (c2 := ‖n2v‖ / Real.sin θ₁)
    (c3 := ‖n3v‖ / Real.sin θ₂) (c4 := ‖n4v‖ / Real.sin θ₂)
    (cr := Real.sin (θ₁ + θ₂) * Real.sin (d / 2) / (Real.sin θ₁ * Real.sin θ₂))
    (p1 := 2 * Real.sin θ₁ * Real.cos (d / 2) / ‖n1v‖)
    (p2 := 2 * Real.sin θ₂ * Real.cos (d / 2) / ‖n3v‖)
    (by positivity) (by rw [hn2_norm]; positivity) (by positivity) (by rw [hn4_norm]; positivity)
    (by positivity) (by positivity) (by positivity)
    (fun y => by
      have hn1_re : (‖n1v‖ / Real.sin θ₁) * inner ℝ (w1s : E3) (y : E3) = (1 / Real.sin θ₁) * inner ℝ n1v (y : E3) := by
        dsimp [w1s, w1v]; rw [inner_smul_left]; simp only [conj_trivial]; field_simp [hn1_pos.ne', hsin_θ1.ne']
      have hn3_re : (‖n3v‖ / Real.sin θ₂) * inner ℝ (w3s : E3) (y : E3) = (1 / Real.sin θ₂) * inner ℝ n3v (y : E3) := by
        dsimp [w3s, w3v]; rw [inner_smul_left]; simp only [conj_trivial]; field_simp [hn3_pos.ne', hsin_θ2.ne']
      rw [hn1_re, hn3_re]
      simp only [n1v, n3v, e1s, e1v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [Real.sin_add]
      field_simp [hsin_θ1.ne', hsin_θ2.ne']
      ring)
    (fun y => by
      have hn2_re : (‖n2v‖ / Real.sin θ₁) * inner ℝ (w2s : E3) (y : E3) = (1 / Real.sin θ₁) * inner ℝ n2v (y : E3) := by
        dsimp [w2s, w2v]; rw [inner_smul_left]; simp only [conj_trivial]; field_simp [(hn2_norm ▸ hn1_pos).ne', hsin_θ1.ne']
      have hn4_re : (‖n4v‖ / Real.sin θ₂) * inner ℝ (w4s : E3) (y : E3) = (1 / Real.sin θ₂) * inner ℝ n4v (y : E3) := by
        dsimp [w4s, w4v]; rw [inner_smul_left]; simp only [conj_trivial]; field_simp [(hn4_norm ▸ hn3_pos).ne', hsin_θ2.ne']
      rw [hn2_re, hn4_re]
      simp only [n2v, n4v, e1s, e1v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [Real.sin_add]
      field_simp [hsin_θ1.ne', hsin_θ2.ne']
      ring)
    (fun y => by
      have hw2_eq : (w2s : E3) = (1 / ‖n1v‖) • n2v := by dsimp [w2s, w2v]; rw [hn2_norm]
      rw [hw2_eq]
      change inner ℝ ((1 / ‖n1v‖) • n2v) (y : E3) - inner ℝ ((1 / ‖n1v‖) • n1v) (y : E3) = _
      rw [inner_smul_left, inner_smul_left]
      simp only [conj_trivial]
      rw [← mul_sub, ← inner_sub_left]
      have hsub_n : n2v - n1v = (2 * Real.sin θ₁ * Real.cos (d / 2)) • e0v := by
        ext i; fin_cases i <;> simp [n2v, n1v, e0v] <;> ring
      rw [hsub_n, inner_smul_left]
      simp only [conj_trivial]
      change _ = (2 * Real.sin θ₁ * Real.cos (d / 2) / ‖n1v‖) * inner ℝ (e0s : E3) (y : E3)
      dsimp [e0s]; ring)
    (fun y => by
      have hw4_eq : (w4s : E3) = (1 / ‖n3v‖) • n4v := by dsimp [w4s, w4v]; rw [hn4_norm]
      rw [hw4_eq]
      change inner ℝ ((1 / ‖n3v‖) • n4v) (y : E3) - inner ℝ ((1 / ‖n3v‖) • n3v) (y : E3) = _
      rw [inner_smul_left, inner_smul_left]
      simp only [conj_trivial]
      rw [← mul_sub, ← inner_sub_left]
      have hsub_n : n4v - n3v = (2 * Real.sin θ₂ * Real.cos (d / 2)) • e0v := by
        ext i; fin_cases i <;> simp [n4v, n3v, e0v] <;> ring
      rw [hsub_n, inner_smul_left]
      simp only [conj_trivial]
      change _ = (2 * Real.sin θ₂ * Real.cos (d / 2) / ‖n3v‖) * inner ℝ (e0s : E3) (y : E3)
      dsimp [e0s]; ring)
  rw [hm1_excess, hm2_excess, hhalf1, hhalf2] at htot
  have hM : 0 < MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) :=
    div_pos sphere3_E3_univ_pos (by positivity [Real.pi_pos])
  have hfactor :
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
        (sphExcess m₁ m₁ d + sphExcess m₂ m₂ d) =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E3) 1)) / (4 * Real.pi) *
        (2 * sphExcess m₁ m₂ (θ₁ + θ₂)) := by linarith only [htot]
  exact mul_left_cancel₀ hM.ne' hfactor

lemma sphExcess_kite_half {m₁ m₂ d : ℝ}
    (hd0 : 0 < d) (hd1 : d < Real.pi)
    (hm1_lo : d / 2 < m₁) (hm1_hi : m₁ < Real.pi - d / 2)
    (hm2_lo : d / 2 ≤ m₂) (hm2_hi : m₂ < Real.pi - d / 2)
    (hsum : m₁ + m₂ < Real.pi) :
    let d' := Real.arccos (Real.cos m₁ / Real.cos (d / 2)) +
      Real.arccos (Real.cos m₂ / Real.cos (d / 2))
    0 < d' ∧ d' < Real.pi ∧ d' < m₁ + m₂ ∧ m₁ < m₂ + d' ∧ m₂ < d' + m₁ ∧
      m₁ + m₂ + d' < 2 * Real.pi ∧
      sphExcess m₁ m₁ d + (if m₂ = d / 2 then 0 else sphExcess m₂ m₂ d) =
        2 * sphExcess m₁ m₂ d' := by
  intro d'
  have hd2_pos : 0 < d / 2 := by linarith
  have hd2_lt : d / 2 < Real.pi / 2 := by linarith
  have hcos_d : 0 < Real.cos (d / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd2_lt⟩
  have hsin_d : 0 < Real.sin (d / 2) := Real.sin_pos_of_pos_of_lt_pi hd2_pos (by linarith [Real.pi_pos])
  have hratio₁_lt : Real.cos m₁ / Real.cos (d / 2) < 1 := by
    rw [div_lt_one hcos_d]
    exact Real.strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [Real.pi_pos]⟩ hm1_lo
  have hratio₁_gt : -1 < Real.cos m₁ / Real.cos (d / 2) := by
    rw [lt_div_iff₀ hcos_d, neg_one_mul, ← Real.cos_pi_sub (d / 2)]
    exact Real.strictAntiOn_cos ⟨by linarith, by linarith [Real.pi_pos]⟩
      ⟨by linarith, by linarith [Real.pi_pos]⟩ hm1_hi
  have hratio₂_le : Real.cos m₂ / Real.cos (d / 2) ≤ 1 := by
    rw [div_le_one hcos_d]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) hm2_lo
  have hratio₂_gt : -1 < Real.cos m₂ / Real.cos (d / 2) := by
    rw [lt_div_iff₀ hcos_d, neg_one_mul, ← Real.cos_pi_sub (d / 2)]
    exact Real.strictAntiOn_cos ⟨by linarith, by linarith [Real.pi_pos]⟩
      ⟨by linarith, by linarith [Real.pi_pos]⟩ hm2_hi
  obtain ⟨θ₁, hθ1_eq⟩ : ∃ x : ℝ, x = Real.arccos (Real.cos m₁ / Real.cos (d / 2)) := ⟨_, rfl⟩
  obtain ⟨θ₂, hθ2_eq⟩ : ∃ x : ℝ, x = Real.arccos (Real.cos m₂ / Real.cos (d / 2)) := ⟨_, rfl⟩
  have hd'_eq : d' = θ₁ + θ₂ := by dsimp [d']; rw [hθ1_eq, hθ2_eq]
  have hθ1_pos : 0 < θ₁ := by rw [hθ1_eq]; exact Real.arccos_pos.mpr hratio₁_lt
  have hθ1_lt : θ₁ < Real.pi := by rw [hθ1_eq]; exact Real.arccos_lt_pi.mpr hratio₁_gt
  have hθ2_nonneg : 0 ≤ θ₂ := by rw [hθ2_eq]; exact Real.arccos_nonneg _
  have hθ2_lt : θ₂ < Real.pi := by rw [hθ2_eq]; exact Real.arccos_lt_pi.mpr hratio₂_gt
  have hcos_θ1 : Real.cos θ₁ = Real.cos m₁ / Real.cos (d / 2) := by
    rw [hθ1_eq]; exact Real.cos_arccos hratio₁_gt.le hratio₁_lt.le
  have hcos_θ2 : Real.cos θ₂ = Real.cos m₂ / Real.cos (d / 2) := by
    rw [hθ2_eq]; exact Real.cos_arccos hratio₂_gt.le hratio₂_le
  have hcos_sum_pos : 0 < Real.cos θ₁ + Real.cos θ₂ := by
    rw [hcos_θ1, hcos_θ2, ← add_div]
    apply div_pos _ hcos_d
    rw [Real.cos_add_cos]
    have h1 : 0 < Real.cos ((m₁ + m₂) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    have h2 : 0 < Real.cos ((m₁ - m₂) / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    positivity
  have hd'_lt_pi : θ₁ + θ₂ < Real.pi := by
    have hcos_lt : Real.cos (Real.pi - θ₂) < Real.cos θ₁ := by
      rw [Real.cos_pi_sub]; linarith
    have hlt_sub : θ₁ < Real.pi - θ₂ := by
      by_contra hle
      rcases eq_or_lt_of_le (le_of_not_gt hle) with h_eq | h_lt
      · rw [h_eq] at hcos_lt; exact lt_irrefl _ hcos_lt
      · have hanti : Real.cos θ₁ < Real.cos (Real.pi - θ₂) :=
          Real.strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨hθ1_pos.le, hθ1_lt.le⟩ h_lt
        linarith
    linarith
  have hd'_pos : 0 < θ₁ + θ₂ := by linarith
  have hsin_sum_pos : 0 < Real.sin (θ₁ + θ₂) := Real.sin_pos_of_pos_of_lt_pi hd'_pos hd'_lt_pi
  have htri_A1BA2 : θ₁ + θ₂ < m₁ + m₂ ∧ m₁ < m₂ + (θ₁ + θ₂) ∧
      m₂ < (θ₁ + θ₂) + m₁ ∧ m₁ + m₂ + (θ₁ + θ₂) < 2 * Real.pi := by
    let Bv : E3 := !₂[Real.sin (d / 2), 0, Real.cos (d / 2)]
    let A₁v : E3 := !₂[0, Real.sin θ₁, Real.cos θ₁]
    let A₂v : E3 := !₂[0, -Real.sin θ₂, Real.cos θ₂]
    have hBnorm : ‖Bv‖ = 1 := norm_E3_unit_of_sin_cos_half _ _ (Real.sin_sq_add_cos_sq (d / 2))
    have hA1norm : ‖A₁v‖ = 1 := norm_E3_unit_of_yz _ _ (Real.sin_sq_add_cos_sq θ₁)
    have hA2norm : ‖A₂v‖ = 1 := norm_E3_unit_of_yz _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ₂])
    have hdet : det3 A₁v Bv A₂v ≠ 0 := det3_kite_ne_zero hsin_d hsin_sum_pos
    have hineq := sphTriangleInequalities_of_det3_ne_zero hA1norm hBnorm hA2norm hdet
    have hd_A1B : Real.arccos (inner ℝ A₁v Bv) = m₁ := by
      have hip : inner ℝ A₁v Bv = Real.cos m₁ := by
        simp only [A₁v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [hcos_θ1]; field_simp [hcos_d.ne']; ring
      rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
    have hd_A2B : Real.arccos (inner ℝ Bv A₂v) = m₂ := by
      have hip : inner ℝ Bv A₂v = Real.cos m₂ := by
        simp only [A₂v, Bv, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [hcos_θ2]; field_simp [hcos_d.ne']; ring
      rw [hip, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
    have hd_A1A2 : Real.arccos (inner ℝ A₂v A₁v) = θ₁ + θ₂ := by
      have hip : inner ℝ A₂v A₁v = Real.cos (θ₁ + θ₂) := by
        simp only [A₁v, A₂v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        rw [Real.cos_add]; ring
      rw [hip, Real.arccos_cos hd'_pos.le hd'_lt_pi.le]
    rw [hd_A1B, hd_A2B, hd_A1A2] at hineq
    rcases hineq with ⟨_, _, _, _, _, _, ha, hb, hc, hs⟩
    exact ⟨hb, hc, ha, by linarith⟩
  rw [hd'_eq]
  refine ⟨hd'_pos, hd'_lt_pi, htri_A1BA2.1, htri_A1BA2.2.1, htri_A1BA2.2.2.1, htri_A1BA2.2.2.2, ?_⟩
  by_cases hm2_eq : m₂ = d / 2
  · have hθ2_0 : θ₂ = 0 := by
      rw [hθ2_eq, hm2_eq, div_self hcos_d.ne', Real.arccos_one]
    rw [if_pos hm2_eq, add_zero, hθ2_0, add_zero]
    exact sphExcess_kite_half_eq_d2 hd0 hd1 hm1_lo hm1_hi hm2_eq hθ1_pos hθ1_lt hcos_θ1
  · have hm2_gt : d / 2 < m₂ := lt_of_le_of_ne hm2_lo (Ne.symm hm2_eq)
    have hratio₂_lt : Real.cos m₂ / Real.cos (d / 2) < 1 := by
      rw [div_lt_one hcos_d]
      exact Real.strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [Real.pi_pos]⟩ hm2_gt
    have hθ2_pos : 0 < θ₂ := by rw [hθ2_eq]; exact Real.arccos_pos.mpr hratio₂_lt
    rw [if_neg hm2_eq]
    exact sphExcess_kite_half_gt_d2 hd0 hd1 hm1_lo hm1_hi hm2_gt hm2_hi
      hθ1_pos hθ1_lt hθ2_pos hθ2_lt hd'_lt_pi hcos_θ1 hcos_θ2

section BoundaryPolygon

private lemma finrank_span_lt_four_of_not_linIndep
    (u : Fin 4 → ↑(Metric.sphere (0 : E4) 1))
    (hdeg : ¬ LinearIndependent ℝ (fun i => (u i : E4))) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => (u i : E4))) < 4 := by
  let S := Submodule.span ℝ (Set.range fun i => (u i : E4))
  have hle : Module.finrank ℝ S ≤ 4 := by
    have := Submodule.finrank_le S
    rwa [finrank_euclideanSpace_fin] at this
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hdeg
  have htop : S = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [heq, finrank_euclideanSpace_fin])
  exact linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge
    (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])

private noncomputable def embE3 (b : Fin 4 → E4) (y : E3) : E4 :=
  y.ofLp 0 • b 1 + y.ofLp 1 • b 2 + y.ofLp 2 • b 3

private noncomputable def projE3 (b : Fin 4 → E4) (x : E4) : E3 :=
  !₂[inner ℝ (b 1) x, inner ℝ (b 2) x, inner ℝ (b 3) x]

private lemma embE3_inner {b : Fin 4 → E4} (hb : Orthonormal ℝ b) (y z : E3) :
    inner ℝ (embE3 b y) (embE3 b z) = inner ℝ y z := by
  have horth := (orthonormal_iff_ite.mp hb)
  have h11 : inner ℝ (b 1) (b 1) = 1 := by simpa using horth 1 1
  have h22 : inner ℝ (b 2) (b 2) = 1 := by simpa using horth 2 2
  have h33 : inner ℝ (b 3) (b 3) = 1 := by simpa using horth 3 3
  have h12 : inner ℝ (b 1) (b 2) = 0 := by simpa using horth 1 2
  have h13 : inner ℝ (b 1) (b 3) = 0 := by simpa using horth 1 3
  have h21 : inner ℝ (b 2) (b 1) = 0 := by simpa using horth 2 1
  have h23 : inner ℝ (b 2) (b 3) = 0 := by simpa using horth 2 3
  have h31 : inner ℝ (b 3) (b 1) = 0 := by simpa using horth 3 1
  have h32 : inner ℝ (b 3) (b 2) = 0 := by simpa using horth 3 2
  simp only [embE3, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    conj_trivial, h11, h22, h33, h12, h13, h21, h23, h31, h32,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  ring

private lemma embE3_norm {b : Fin 4 → E4} (hb : Orthonormal ℝ b) (y : E3) :
    ‖embE3 b y‖ = ‖y‖ := by
  refine sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp ?_
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact embE3_inner hb y y

private lemma inner_embE3_left (b : Fin 4 → E4) (y : E3) (x : E4) :
    inner ℝ (embE3 b y) x = inner ℝ y (projE3 b x) := by
  simp only [embE3, projE3, inner_add_left, inner_smul_left, conj_trivial,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private lemma inner_b0_embE3 {b : Fin 4 → E4} (hb : Orthonormal ℝ b) (y : E3) :
    inner ℝ (b 0) (embE3 b y) = 0 := by
  have horth := (orthonormal_iff_ite.mp hb)
  have h01 : inner ℝ (b 0) (b 1) = 0 := by simpa using horth 0 1
  have h02 : inner ℝ (b 0) (b 2) = 0 := by simpa using horth 0 2
  have h03 : inner ℝ (b 0) (b 3) = 0 := by simpa using horth 0 3
  simp only [embE3, inner_add_right, inner_smul_right, h01, h02, h03]
  ring

private lemma embE3_projE3_of_ortho {b : Fin 4 → E4} (hb : Orthonormal ℝ b)
    {x : E4} (hx : inner ℝ (b 0) x = 0) :
    embE3 b (projE3 b x) = x := by
  have horth := (orthonormal_iff_ite.mp hb)
  set r : E4 := x - embE3 b (projE3 b x)
  have hr_b : ∀ j : Fin 4, inner ℝ (b j) r = 0 := by
    intro j
    fin_cases j
    · dsimp only
      rw [show (⟨0, by decide⟩ : Fin 4) = 0 from rfl]
      simp only [r, inner_sub_right, hx, inner_b0_embE3 hb, sub_zero]
    · dsimp only
      simp [r, embE3, projE3, inner_sub_right, inner_add_right, inner_smul_right,
        show ‖b 1‖ = 1 from hb.1 1,
        show inner ℝ (b 1) (b 2) = 0 by simpa using horth 1 2,
        show inner ℝ (b 1) (b 3) = 0 by simpa using horth 1 3]
    · dsimp only
      simp [r, embE3, projE3, inner_sub_right, inner_add_right, inner_smul_right,
        show ‖b 2‖ = 1 from hb.1 2,
        show inner ℝ (b 2) (b 1) = 0 by simpa using horth 2 1,
        show inner ℝ (b 2) (b 3) = 0 by simpa using horth 2 3]
    · dsimp only
      simp [r, embE3, projE3, inner_sub_right, inner_add_right, inner_smul_right,
        show ‖b 3‖ = 1 from hb.1 3,
        show inner ℝ (b 3) (b 1) = 0 by simpa using horth 3 1,
        show inner ℝ (b 3) (b 2) = 0 by simpa using horth 3 2]
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hb.linearIndependent.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin, finrank_euclideanSpace_fin])
  have hr_all : ∀ z : E4, inner ℝ z r = 0 := by
    intro z
    have hz : z ∈ Submodule.span ℝ (Set.range b) := by rw [hspan]; trivial
    induction hz using Submodule.span_induction with
    | mem y hy => rcases hy with ⟨j, rfl⟩; exact hr_b j
    | zero => simp
    | add x₁ x₂ _ _ hx₁ hx₂ => rw [inner_add_left, hx₁, hx₂, add_zero]
    | smul c x₁ _ hx₁ => rw [inner_smul_left, hx₁, mul_zero]
  have hnorm : ‖r‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hr_all r
  have hr0 : r = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  exact (sub_eq_zero.mp hr0).symm

private lemma exists_ortho_frame_E4 (w : E4) (hw : ‖w‖ = 1) :
    ∃ b : Fin 4 → E4, Orthonormal ℝ b ∧ b 0 = w := by
  have hfin : Module.finrank ℝ (Submodule.span ℝ ({w} : Set E4)) < 4 := by
    have hle : Module.finrank ℝ (Submodule.span ℝ ({w} : Set E4)) ≤ 1 :=
      finrank_span_singleton (by intro h; rw [h, norm_zero] at hw; norm_num at hw) |>.le
    omega
  obtain ⟨v₀, hv₀_norm, hv₀_orth⟩ := exists_unit_orthogonal_of_finrank_lt hfin
  have hwv₀ : inner ℝ w v₀ = 0 :=
    hv₀_orth w (Submodule.subset_span (Set.mem_singleton w))
  obtain ⟨b, hb, hb0, _⟩ := exists_orthonormal_extension_pair hw hv₀_norm hwv₀
  exact ⟨b, hb, hb0⟩

private lemma rhs_square_area_nonneg {A : ℝ} (hA0 : 0 < A) (hA4pi : A < 4 * Real.pi) :
    0 ≤ 4 * Real.arccos (-Real.tan (A / 16) ^ 2) - 2 * Real.pi := by
  have hpos : 0 < A / 16 := by linarith
  have hlt : A / 16 < Real.pi / 4 := by linarith
  have htan_nonneg : 0 ≤ Real.tan (A / 16) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hpos.le (by linarith [Real.pi_pos])
  have htan_lt : Real.tan (A / 16) < 1 := by
    rw [← Real.tan_pi_div_four]
    exact Real.strictMonoOn_tan
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hlt
  have hsq_lt : Real.tan (A / 16) ^ 2 < 1 := by nlinarith
  have hpi2 : Real.pi / 2 ≤ Real.arccos (-Real.tan (A / 16) ^ 2) := by
    by_contra hlt_arc
    push Not at hlt_arc
    have hcos := Real.strictAntiOn_cos
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      hlt_arc
    rw [Real.cos_pi_div_two, Real.cos_arccos (by nlinarith) (by nlinarith)] at hcos
    nlinarith
  linarith

private lemma measure_three_null_of_ortho_dot_zero
    (u : Fin 4 → ↑(Metric.sphere (0 : E4) 1))
    {n : E4} (hn : n ≠ 0)
    (hsub : ∀ x : E4, x ∈ Metric.sphere (0 : E4) 1 → (∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x) →
      inner ℝ n x = 0) :
    measure 3 {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} = 0 := by
  let B : Set E4 := {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
  have hB_sub : B ⊆ Metric.sphere 0 1 := fun _ hx => hx.1
  have hB_cl : IsClosed B := by
    refine Metric.isClosed_sphere.inter ?_
    have heq : {x : E4 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} =
        ⋂ i : Fin 4, {x : E4 | 0 ≤ inner ℝ (u i : E4) x} := by ext x; simp
    change IsClosed {x : E4 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_const : Continuous fun _ : E4 => (u i : E4)).inner continuous_id)
  have hm : measure 3 B =
      sphereScale 3 * MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' B) := by
    simpa [measure] using hausdorffMeasure_real_eq_scale_mul_toSphere (d := 3) (by decide) hB_sub
      hB_cl.measurableSet
  rw [hm]
  have hpre_sub : (Subtype.val ⁻¹' B) ⊆
      {z : ↑(Metric.sphere (0 : E4) 1) | inner ℝ n (z : E4) = 0} := by
    intro z hz
    exact hsub z.1 hz.1 hz.2
  have hnull : MeasureTheory.volume.toSphere (Subtype.val ⁻¹' B) = 0 :=
    MeasureTheory.measure_mono_null hpre_sub (toSphere_hyperplane_null n hn)
  simp [MeasureTheory.measureReal_def, hnull]

private lemma sphere_cone_exists_pole_or_null
    (V : Finset ↑(Metric.sphere (0 : E3) 1)) (hV : V.Nonempty) :
    (∃ r₀ ∈ V, ∀ x : E3, (∀ r ∈ V, 0 ≤ inner ℝ (r : E3) x) → inner ℝ (r₀ : E3) x = 0) ∨
    (∃ z₀ : ↑(Metric.sphere (0 : E3) 1), ∀ r ∈ V, 0 < inner ℝ (r : E3) (z₀ : E3)) := by
  let S : Set E3 := Subtype.val '' (V : Set ↑(Metric.sphere (0 : E3) 1))
  let C : Set E3 := convexHull ℝ S
  have hS_fin : S.Finite := (V.finite_toSet).image Subtype.val
  have hC_comp : IsCompact C := by
    dsimp only [C]
    exact hS_fin.isCompact_convexHull (𝕜 := ℝ)
  have hS_ne : S.Nonempty := by
    rcases hV with ⟨r, hr⟩
    exact ⟨r, r, hr, rfl⟩
  have hC_ne : C.Nonempty := hS_ne.convexHull
  have hcont : ContinuousOn (fun y : E3 => ‖y‖ ^ 2) C :=
    (continuous_norm.pow 2).continuousOn
  obtain ⟨z, hzC, hz_min⟩ := hC_comp.exists_isMinOn hC_ne hcont
  by_cases hz0 : z = 0
  · left
    have h0C : (0 : E3) ∈ C := hz0 ▸ hzC
    rw [mem_convexHull_iff_exists_fintype] at h0C
    rcases h0C with ⟨ι, _, w, p, hw_nonneg, hw_sum, hp_mem, hp_sum⟩
    have hex : ∃ i₀ : ι, 0 < w i₀ := by
      by_contra h
      push_neg at h
      have hw0 : ∑ i : ι, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    rcases hex with ⟨i₀, hi₀⟩
    obtain ⟨r₀, hr₀V, hr₀eq⟩ := hp_mem i₀
    refine ⟨r₀, hr₀V, fun x hx => ?_⟩
    have hsum0 : ∑ i : ι, w i * inner ℝ (p i) x = 0 := by
      calc ∑ i : ι, w i * inner ℝ (p i) x
          = inner ℝ (∑ i : ι, w i • p i) x := by
              simp [sum_inner, real_inner_smul_left]
        _ = inner ℝ (0 : E3) x := by rw [hp_sum]
        _ = 0 := inner_zero_left x
    have hterm_nonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * inner ℝ (p i) x := by
      intro i _
      obtain ⟨r, hrV, hr_eq⟩ := hp_mem i
      rw [← hr_eq]
      exact mul_nonneg (hw_nonneg i) (hx r hrV)
    have hi₀_mem : i₀ ∈ (Finset.univ : Finset ι) := Finset.mem_univ i₀
    have hsingle : w i₀ * inner ℝ (p i₀) x = 0 := by
      have hge := Finset.single_le_sum hterm_nonneg hi₀_mem
      have hle := hterm_nonneg i₀ hi₀_mem
      linarith
    rcases mul_eq_zero.mp hsingle with hw0 | hrx
    · linarith
    · rw [← hr₀eq] at hrx; exact hrx
  · right
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let z₀ : ↑(Metric.sphere (0 : E3) 1) :=
      ⟨‖z‖⁻¹ • z, by simp [norm_smul, inv_mul_cancel₀ hz_pos.ne']⟩
    refine ⟨z₀, fun r hrV => ?_⟩
    have hrC : (r : E3) ∈ C := subset_convexHull ℝ S ⟨r, hrV, rfl⟩
    have hdiff_ge : 0 ≤ inner ℝ z ((r : E3) - z) := by
      by_contra hlt
      push_neg at hlt
      let d : E3 := (r : E3) - z
      let t : ℝ := min (1 / 2) (-(inner ℝ z d) / (‖d‖ ^ 2 + 1))
      have ht_pos : 0 < t := lt_min (by norm_num) (div_pos (neg_pos.mpr hlt) (by positivity))
      have ht_le1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
      have ht_pt : (1 - t) • z + t • (r : E3) ∈ C :=
        (convex_convexHull ℝ S) hzC hrC (sub_nonneg.mpr ht_le1) ht_pos.le (by ring)
      have hmin := hz_min ht_pt
      have hpt_eq : (1 - t) • z + t • (r : E3) = z + t • d := by
        simp only [d]; module
      rw [hpt_eq] at hmin
      change ‖z‖ ^ 2 ≤ ‖z + t • d‖ ^ 2 at hmin
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_right] at hmin
      have ht_bound : t * (‖d‖ ^ 2 + 1) ≤ -(inner ℝ z d) := by
        have h1 : t ≤ -(inner ℝ z d) / (‖d‖ ^ 2 + 1) := min_le_right _ _
        rwa [le_div_iff₀ (by positivity)] at h1
      have hid : inner ℝ d z = inner ℝ z d := real_inner_comm z d
      have hdd : inner ℝ d d = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
      rw [hid, real_inner_smul_left, real_inner_smul_right, hdd] at hmin
      have hbad : 2 * t * inner ℝ z d + t ^ 2 * ‖d‖ ^ 2 < 0 := by
        have h1 : t * ‖d‖ ^ 2 ≤ t * (‖d‖ ^ 2 + 1) := by nlinarith
        nlinarith
      linarith
    have hinner_ge : ‖z‖ ^ 2 ≤ inner ℝ (r : E3) z := by
      rw [real_inner_comm]
      have hsub : inner ℝ z ((r : E3) - z) = inner ℝ z (r : E3) - ‖z‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      linarith
    have hpos_r : 0 < inner ℝ (r : E3) (z₀ : E3) := by
      change 0 < inner ℝ (r : E3) (‖z‖⁻¹ • z)
      rw [inner_smul_right]
      exact mul_pos (inv_pos.mpr hz_pos) (lt_of_lt_of_le (sq_pos_of_pos hz_pos) hinner_ge)
    exact hpos_r

private lemma measure_two_hemisphere_section {u n₀ : E4} (hu : ‖u‖ = 1) (hn0 : ‖n₀‖ = 1)
    (hu0 : inner ℝ u n₀ = 0) :
    measure 2 {x ∈ Metric.sphere (0 : E4) 1 | inner ℝ u x = 0 ∧ 0 ≤ inner ℝ n₀ x} =
      2 * Real.pi * faceScale := by
  have heq : {x ∈ Metric.sphere (0 : E4) 1 | inner ℝ u x = 0 ∧ 0 ≤ inner ℝ n₀ x} =
      {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ u x = 0 ∧ 0 ≤ inner ℝ n₀ x ∧ 0 ≤ inner ℝ n₀ x} := by
    ext x; simp [and_self]
  rw [heq, measure_two_suspension_arc hu hn0 hn0 hu0 hu0]
  have h1 : inner ℝ n₀ n₀ = 1 := by
    rw [real_inner_self_eq_norm_sq, hn0, one_pow]
  rw [h1, Real.arccos_neg_one]
  ring

private lemma area_degenerate_case_one_or_planar
    (u : Fin 4 → ↑(Metric.sphere (0 : E4) 1))
    {b : Fin 4 → E4} (hb : Orthonormal ℝ b)
    (u3 : Fin 4 → ↑(Metric.sphere (0 : E3) 1))
    (hu_eq : ∀ i : Fin 4, (u i : E4) = embE3 b (u3 i : E3))
    (totalStdArea : ℝ) (hA4pi : totalStdArea < 4 * Real.pi)
    (hArea : ∑ v ∈ Finset.image u Finset.univ,
      measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ Finset.image u Finset.univ, 0 ≤ inner ℝ (v' : E4) x} ≤
      faceScale * totalStdArea)
    (z₀ : ↑(Metric.sphere (0 : E3) 1))
    (hz₀ : ∀ r ∈ Finset.image u3 Finset.univ, 0 < inner ℝ (r : E3) (z₀ : E3)) :
    ¬ (∃ q : ↑(Metric.sphere (0 : E3) 1),
      ∀ r ∈ Finset.image u3 Finset.univ, inner ℝ (r : E3) (q : E3) = 0) := by
  let V : Finset ↑(Metric.sphere (0 : E4) 1) := Finset.image u Finset.univ
  let V₃ : Finset ↑(Metric.sphere (0 : E3) 1) := Finset.image u3 Finset.univ
  intro ⟨q, hq⟩
  have hV₃_ne : V₃.Nonempty := ⟨u3 0, Finset.mem_image_of_mem u3 (Finset.mem_univ 0)⟩
  have hf_inj : ∀ r₁ r₂ : ↑(Metric.sphere (0 : E3) 1),
      embE3 b (r₁ : E3) = embE3 b (r₂ : E3) → r₁ = r₂ := by
    intro r₁ r₂ h
    ext1
    have hnorm : ‖(r₁ : E3) - (r₂ : E3)‖ = 0 := by
      rw [← embE3_norm hb, show embE3 b ((r₁ : E3) - (r₂ : E3)) =
        embE3 b (r₁ : E3) - embE3 b (r₂ : E3) by simp [embE3]; module, h, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hf_mem : ∀ r ∈ V₃, (⟨embE3 b (r : E3), by
      simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using r.2⟩ :
      ↑(Metric.sphere (0 : E4) 1)) ∈ V := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨i, _, rfl⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
    ext1; exact hu_eq i
  by_cases hcard1 : V₃.card ≤ 1
  · obtain ⟨r₀, hr₀⟩ := hV₃_ne
    have hV_sing : V = {⟨embE3 b (r₀ : E3), by
        simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using r₀.2⟩} := by
      have hr₀_eq : ∀ r ∈ V₃, r = r₀ := by
        intro r hr
        exact (Finset.card_le_one.mp hcard1) r hr r₀ hr₀
      ext v
      simp only [V, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        have hri : u3 i = r₀ := hr₀_eq (u3 i) (Finset.mem_image_of_mem u3 (Finset.mem_univ i))
        ext1; rw [hu_eq i, hri]
      · intro hv
        rcases Finset.mem_image.mp hr₀ with ⟨i, _, rfl⟩
        refine ⟨i, ?_⟩
        ext1; rw [hv, hu_eq i]
    let v₀ : ↑(Metric.sphere (0 : E4) 1) :=
      ⟨embE3 b (r₀ : E3), by simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using r₀.2⟩
    have hv₀_norm : ‖(v₀ : E4)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using v₀.2
    have hsum_eq : ∑ v ∈ V, measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} =
        4 * Real.pi * faceScale := by
      rw [hV_sing, Finset.sum_singleton]
      have hset : {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (v₀ : E4) x = 0 ∧ ∀ v' ∈ ({v₀} : Finset _), 0 ≤ inner ℝ (v' : E4) x} =
          {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v₀ : E4) x = 0} := by
        ext x; simp (config := { contextual := true })
      rw [hset, measure_sphere_two_section (v₀ : E4) hv₀_norm]
    have hA : ∑ v ∈ V, measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} ≤
        faceScale * totalStdArea := hArea
    have hcontra : 4 * Real.pi * faceScale ≤ faceScale * totalStdArea := by linarith [hsum_eq, hA]
    have hfpos := faceScale_pos
    nlinarith
  · push_neg at hcard1
    have hq_norm : ‖(q : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using q.2
    let p : E3 := (z₀ : E3) - inner ℝ (q : E3) (z₀ : E3) • (q : E3)
    have hp_ne : p ≠ 0 := by
      intro hp0
      obtain ⟨r₀, hr₀⟩ := hV₃_ne
      have h1 : inner ℝ (r₀ : E3) p = 0 := by rw [hp0, inner_zero_right]
      have h2 : inner ℝ (r₀ : E3) p = inner ℝ (r₀ : E3) (z₀ : E3) := by
        simp only [p, inner_sub_right, inner_smul_right, hq r₀ hr₀, mul_zero, sub_zero]
      linarith [hz₀ r₀ hr₀]
    let e₀ : E3 := ‖p‖⁻¹ • p
    have he₀_norm : ‖e₀‖ = 1 := by simp [e₀, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp_ne)]
    have hqe₀ : inner ℝ (q : E3) e₀ = 0 := by
      simp [e₀, p, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hq_norm]
    have hr_e₀_pos : ∀ r ∈ V₃, 0 < inner ℝ (r : E3) e₀ := by
      intro r hr
      have hnorm_p_pos : 0 < ‖p‖ := norm_pos_iff.mpr hp_ne
      have heq : inner ℝ (r : E3) p = inner ℝ (r : E3) (z₀ : E3) := by
        simp only [p, inner_sub_right, inner_smul_right, hq r hr, mul_zero, sub_zero]
      change 0 < inner ℝ (r : E3) (‖p‖⁻¹ • p)
      rw [inner_smul_right, heq]
      exact mul_pos (inv_pos.mpr hnorm_p_pos) (hz₀ r hr)
    let e₁ : E3 := cross3 (q : E3) e₀
    have he₁_norm : ‖e₁‖ = 1 := by
      have hsq : ‖e₁‖ ^ 2 = 1 := by
        rw [norm_sq_cross3, hq_norm, he₀_norm, hqe₀]
        norm_num
      exact (sq_eq_one_iff.mp hsq).resolve_right (by linarith [norm_nonneg e₁])
    have hqe₁ : inner ℝ (q : E3) e₁ = 0 := inner_left_cross3 _ _
    have he₀₁ : inner ℝ e₀ e₁ = 0 := inner_right_cross3 _ _
    let slope : ↑(Metric.sphere (0 : E3) 1) → ℝ :=
      fun r => inner ℝ (r : E3) e₁ / inner ℝ (r : E3) e₀
    obtain ⟨r_min, hr_min_mem, hr_min_le⟩ := V₃.exists_min_image slope hV₃_ne
    obtain ⟨r_max, hr_max_mem, hr_max_ge⟩ := V₃.exists_max_image slope hV₃_ne
    have hslope_inj : ∀ r₁ ∈ V₃, ∀ r₂ ∈ V₃, slope r₁ = slope r₂ → r₁ = r₂ := by
      intro r₁ hr₁ r₂ hr₂ hsl
      have ha₁ : 0 < inner ℝ (r₁ : E3) e₀ := hr_e₀_pos r₁ hr₁
      have ha₂ : 0 < inner ℝ (r₂ : E3) e₀ := hr_e₀_pos r₂ hr₂
      let lam : ℝ := inner ℝ (r₂ : E3) e₀ / inner ℝ (r₁ : E3) e₀
      have hlam_pos : 0 < lam := div_pos ha₂ ha₁
      have hr₂_eq : (r₂ : E3) = lam • (r₁ : E3) := by
        have hdiff : (r₂ : E3) - lam • (r₁ : E3) = 0 := by
          have hsq : ‖(r₂ : E3) - lam • (r₁ : E3)‖ ^ 2 = 0 := by
            rw [← real_inner_self_eq_norm_sq,
              orthonormal_E3_inner hq_norm he₀_norm he₁_norm hqe₀ hqe₁ he₀₁]
            have hq_sub : inner ℝ ((r₂ : E3) - lam • (r₁ : E3)) (q : E3) = 0 := by
              rw [inner_sub_left, real_inner_smul_left, hq r₂ hr₂, hq r₁ hr₁, mul_zero, sub_zero]
            have he₀_sub : inner ℝ ((r₂ : E3) - lam • (r₁ : E3)) e₀ = 0 := by
              rw [inner_sub_left, real_inner_smul_left]
              dsimp [lam]; field_simp [ha₁.ne']; ring
            have he₁_sub : inner ℝ ((r₂ : E3) - lam • (r₁ : E3)) e₁ = 0 := by
              rw [inner_sub_left, real_inner_smul_left]
              dsimp [slope] at hsl
              dsimp [lam]
              rw [div_eq_div_iff ha₁.ne' ha₂.ne'] at hsl
              field_simp [ha₁.ne']; linarith
            rw [hq_sub, he₀_sub, he₁_sub]; ring
          exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
        exact sub_eq_zero.mp hdiff
      have hnorm_lam : lam = 1 := by
        have h1 : ‖(r₂ : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using r₂.2
        have h2 : ‖(r₁ : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using r₁.2
        rw [hr₂_eq, norm_smul, Real.norm_of_nonneg hlam_pos.le, h2, mul_one] at h1
        exact h1
      ext1; rw [hr₂_eq, hnorm_lam, one_smul]
    have hr_ne : r_min ≠ r_max := by
      intro heq
      have hconst : ∀ r ∈ V₃, slope r = slope r_min := fun r hr => by
        have h1 := hr_min_le r hr
        have h2 := hr_max_ge r hr
        rw [← heq] at h2
        linarith
      obtain ⟨r₁, hr₁, r₂, hr₂, h12⟩ := Finset.one_lt_card.mp hcard1
      exact h12 (hslope_inj r₁ hr₁ r₂ hr₂ (by rw [hconst r₁ hr₁, hconst r₂ hr₂]))
    have hslope_lt : slope r_min < slope r_max :=
      lt_of_le_of_ne (hr_min_le r_max hr_max_mem)
        (fun h => hr_ne (hslope_inj r_min hr_min_mem r_max hr_max_mem h))
    have hfacet_hem : ∀ a₁ a₂ : ↑(Metric.sphere (0 : E3) 1),
        a₁ ∈ V₃ → a₂ ∈ V₃ → a₁ ≠ a₂ →
        (∀ r ∈ V₃, ∀ z : E3, inner ℝ (a₁ : E3) z = 0 → 0 ≤ inner ℝ (a₂ : E3) z →
          0 ≤ inner ℝ (r : E3) z) →
        measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (embE3 b (a₁ : E3)) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} =
          2 * Real.pi * faceScale := by
      intro a₁ a₂ ha₁ ha₂ ha₁₂ hcone
      let u₁ : E4 := embE3 b (a₁ : E3)
      let u₂ : E4 := embE3 b (a₂ : E3)
      have hu₁_norm : ‖u₁‖ = 1 := by
        rw [embE3_norm hb]; simpa [Metric.mem_sphere, dist_zero_right] using a₁.2
      have hdiff_ne : (a₂ : E3) - inner ℝ (a₁ : E3) (a₂ : E3) • (a₁ : E3) ≠ 0 := by
        intro h0
        have ha₂_eq : (a₂ : E3) = inner ℝ (a₁ : E3) (a₂ : E3) • (a₁ : E3) := sub_eq_zero.mp h0
        have hnorm_a1 : ‖(a₁ : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using a₁.2
        have hnorm_a2 : ‖(a₂ : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using a₂.2
        have habs : |inner ℝ (a₁ : E3) (a₂ : E3)| = 1 := by
          have := congrArg norm ha₂_eq
          rw [hnorm_a2, norm_smul, Real.norm_eq_abs, hnorm_a1, mul_one] at this
          exact this.symm
        rcases eq_or_eq_neg_of_abs_eq habs with hk | hk
        · apply ha₁₂; ext1; rw [ha₂_eq, hk, one_smul]
        · have hpos1 : 0 < inner ℝ (a₁ : E3) e₀ := hr_e₀_pos a₁ ha₁
          have hpos2 : 0 < inner ℝ (a₂ : E3) e₀ := hr_e₀_pos a₂ ha₂
          rw [ha₂_eq, hk, neg_smul, one_smul, inner_neg_left] at hpos2
          linarith
      let w₂_E3 : E3 := (a₂ : E3) - inner ℝ (a₁ : E3) (a₂ : E3) • (a₁ : E3)
      let w₂ : E4 := embE3 b w₂_E3
      have hw₂_ne : w₂ ≠ 0 := by
        intro h0
        apply hdiff_ne
        have : ‖w₂_E3‖ = 0 := by rw [← embE3_norm hb, ← show w₂ = embE3 b w₂_E3 from rfl, h0, norm_zero]
        exact norm_eq_zero.mp this
      let n₀ : E4 := ‖w₂‖⁻¹ • w₂
      have hn₀_norm : ‖n₀‖ = 1 := by simp [n₀, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw₂_ne)]
      have hu₁n₀ : inner ℝ u₁ n₀ = 0 := by
        have hinner3 : inner ℝ (a₁ : E3) w₂_E3 = 0 := by
          simp [w₂_E3, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
            show ‖(a₁ : E3)‖ = 1 by simpa [Metric.mem_sphere, dist_zero_right] using a₁.2]
        simp [n₀, u₁, w₂, inner_smul_right, embE3_inner hb, hinner3]
      have hset : {x ∈ Metric.sphere (0 : E4) 1 |
            inner ℝ u₁ x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} =
          {x ∈ Metric.sphere (0 : E4) 1 | inner ℝ u₁ x = 0 ∧ 0 ≤ inner ℝ n₀ x} := by
        ext x
        refine and_congr_right fun _ => and_congr_right fun hx1 => ?_
        have hzx : inner ℝ (a₁ : E3) (projE3 b x) = 0 := by
          rwa [← inner_embE3_left]
        have hn₀_equiv : 0 ≤ inner ℝ n₀ x ↔ 0 ≤ inner ℝ u₂ x := by
          have hw₂_eq : inner ℝ w₂ x = inner ℝ u₂ x := by
            have hw2_def : w₂ = u₂ - inner ℝ (a₁ : E3) (a₂ : E3) • u₁ := by
              simp [w₂, w₂_E3, u₁, u₂, embE3]; module
            rw [hw2_def, inner_sub_left, inner_smul_left, hx1, mul_zero, sub_zero]
          have hpos_inv : 0 < ‖w₂‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw₂_ne)
          simp only [n₀, inner_smul_left, hw₂_eq]
          constructor
          · intro h; exact nonneg_of_mul_nonneg_right h hpos_inv
          · intro h; exact mul_nonneg hpos_inv.le h
        rw [hn₀_equiv]
        constructor
        · intro hall
          have hu₂_mem : (⟨u₂, by
              simpa [Metric.mem_sphere, dist_zero_right, u₂, embE3_norm hb] using a₂.2⟩ :
              ↑(Metric.sphere (0 : E4) 1)) ∈ V := hf_mem a₂ ha₂
          exact hall _ hu₂_mem
        · intro hx2 v' hv'
          rcases Finset.mem_image.mp hv' with ⟨i, _, rfl⟩
          have hri : u3 i ∈ V₃ := Finset.mem_image_of_mem u3 (Finset.mem_univ i)
          rw [hu_eq i, inner_embE3_left]
          refine hcone (u3 i) hri (projE3 b x) hzx ?_
          rwa [← inner_embE3_left]
      rw [hset]
      exact measure_two_hemisphere_section hu₁_norm hn₀_norm hu₁n₀
    have hcone_min : ∀ r ∈ V₃, ∀ z : E3, inner ℝ (r_min : E3) z = 0 →
        0 ≤ inner ℝ (r_max : E3) z → 0 ≤ inner ℝ (r : E3) z := by
      intro r hr z hz0 hz1
      have ha₀ : 0 < inner ℝ (r_min : E3) e₀ := hr_e₀_pos r_min hr_min_mem
      have ha₁ : 0 < inner ℝ (r_max : E3) e₀ := hr_e₀_pos r_max hr_max_mem
      have ha : 0 < inner ℝ (r : E3) e₀ := hr_e₀_pos r hr
      let c : ℝ := (inner ℝ (r : E3) e₀ * (slope r - slope r_min)) /
        (inner ℝ (r_max : E3) e₀ * (slope r_max - slope r_min))
      have hc_nonneg : 0 ≤ c :=
        div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr (hr_min_le r hr)))
          (mul_pos ha₁ (sub_pos.mpr hslope_lt)).le
      have hdecomp : (r : E3) =
          (inner ℝ (r : E3) e₀ / inner ℝ (r_min : E3) e₀ -
            c * (inner ℝ (r_max : E3) e₀ / inner ℝ (r_min : E3) e₀)) • (r_min : E3) +
          c • (r_max : E3) := by
        set diff := (r : E3) -
          ((inner ℝ (r : E3) e₀ / inner ℝ (r_min : E3) e₀ -
              c * (inner ℝ (r_max : E3) e₀ / inner ℝ (r_min : E3) e₀)) • (r_min : E3) +
            c • (r_max : E3))
        have hsq0 : ‖diff‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq,
            orthonormal_E3_inner hq_norm he₀_norm he₁_norm hqe₀ hqe₁ he₀₁]
          have hd_q : inner ℝ diff (q : E3) = 0 := by
            simp only [diff, inner_sub_left, inner_add_left, real_inner_smul_left,
              hq r hr, hq r_min hr_min_mem, hq r_max hr_max_mem]; ring
          have hd_e₀ : inner ℝ diff e₀ = 0 := by
            simp only [diff, inner_sub_left, inner_add_left, real_inner_smul_left]
            field_simp [ha₀.ne']; ring
          have hd_e₁ : inner ℝ diff e₁ = 0 := by
            simp only [diff, inner_sub_left, inner_add_left, real_inner_smul_left]
            have hm1 : inner ℝ (r_min : E3) e₁ = slope r_min * inner ℝ (r_min : E3) e₀ := by
              dsimp [slope]; field_simp [ha₀.ne']
            have hm2 : inner ℝ (r_max : E3) e₁ = slope r_max * inner ℝ (r_max : E3) e₀ := by
              dsimp [slope]; field_simp [ha₁.ne']
            have hm3 : inner ℝ (r : E3) e₁ = slope r * inner ℝ (r : E3) e₀ := by
              dsimp [slope]; field_simp [ha.ne']
            rw [hm1, hm2, hm3]
            dsimp [c]
            have hne1 : slope r_max - slope r_min ≠ 0 := (sub_pos.mpr hslope_lt).ne'
            field_simp [ha₀.ne', ha₁.ne', hne1]; ring
          rw [hd_q, hd_e₀, hd_e₁]; ring
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0))
      rw [hdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hz0, mul_zero, zero_add]
      exact mul_nonneg hc_nonneg hz1
    have hcone_max : ∀ r ∈ V₃, ∀ z : E3, inner ℝ (r_max : E3) z = 0 →
        0 ≤ inner ℝ (r_min : E3) z → 0 ≤ inner ℝ (r : E3) z := by
      intro r hr z hz0 hz1
      have ha₀ : 0 < inner ℝ (r_min : E3) e₀ := hr_e₀_pos r_min hr_min_mem
      have ha₁ : 0 < inner ℝ (r_max : E3) e₀ := hr_e₀_pos r_max hr_max_mem
      have ha : 0 < inner ℝ (r : E3) e₀ := hr_e₀_pos r hr
      let c : ℝ := (inner ℝ (r : E3) e₀ * (slope r_max - slope r)) /
        (inner ℝ (r_min : E3) e₀ * (slope r_max - slope r_min))
      have hc_nonneg : 0 ≤ c :=
        div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr (hr_max_ge r hr)))
          (mul_pos ha₀ (sub_pos.mpr hslope_lt)).le
      have hdecomp : (r : E3) =
          (inner ℝ (r : E3) e₀ / inner ℝ (r_max : E3) e₀ -
            c * (inner ℝ (r_min : E3) e₀ / inner ℝ (r_max : E3) e₀)) • (r_max : E3) +
          c • (r_min : E3) := by
        set diff := (r : E3) -
          ((inner ℝ (r : E3) e₀ / inner ℝ (r_max : E3) e₀ -
              c * (inner ℝ (r_min : E3) e₀ / inner ℝ (r_max : E3) e₀)) • (r_max : E3) +
            c • (r_min : E3))
        have hsq0 : ‖diff‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq,
            orthonormal_E3_inner hq_norm he₀_norm he₁_norm hqe₀ hqe₁ he₀₁]
          have hd_q : inner ℝ diff (q : E3) = 0 := by
            simp only [diff, inner_sub_left, inner_add_left, real_inner_smul_left,
              hq r hr, hq r_min hr_min_mem, hq r_max hr_max_mem]; ring
          have hd_e₀ : inner ℝ diff e₀ = 0 := by
            simp only [diff, inner_sub_left, inner_add_left, real_inner_smul_left]
            field_simp [ha₁.ne']; ring
          have hd_e₁ : inner ℝ diff e₁ = 0 := by
            simp only [diff, inner_sub_left, inner_add_left, real_inner_smul_left]
            have hm1 : inner ℝ (r_min : E3) e₁ = slope r_min * inner ℝ (r_min : E3) e₀ := by
              dsimp [slope]; field_simp [ha₀.ne']
            have hm2 : inner ℝ (r_max : E3) e₁ = slope r_max * inner ℝ (r_max : E3) e₀ := by
              dsimp [slope]; field_simp [ha₁.ne']
            have hm3 : inner ℝ (r : E3) e₁ = slope r * inner ℝ (r : E3) e₀ := by
              dsimp [slope]; field_simp [ha.ne']
            rw [hm1, hm2, hm3]
            dsimp [c]
            have hne1 : slope r_max - slope r_min ≠ 0 := (sub_pos.mpr hslope_lt).ne'
            field_simp [ha₀.ne', ha₁.ne', hne1]; ring
          rw [hd_q, hd_e₀, hd_e₁]; ring
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0))
      rw [hdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hz0, mul_zero, zero_add]
      exact mul_nonneg hc_nonneg hz1
    have hmin_area := hfacet_hem r_min r_max hr_min_mem hr_max_mem hr_ne hcone_min
    have hmax_area := hfacet_hem r_max r_min hr_max_mem hr_min_mem hr_ne.symm hcone_max
    let v_min : ↑(Metric.sphere (0 : E4) 1) :=
      ⟨embE3 b (r_min : E3), by simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using r_min.2⟩
    let v_max : ↑(Metric.sphere (0 : E4) 1) :=
      ⟨embE3 b (r_max : E3), by simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using r_max.2⟩
    have hv_ne : v_min ≠ v_max := fun h => hr_ne (hf_inj _ _ (congrArg Subtype.val h))
    have hsub2 : ({v_min, v_max} : Finset _) ⊆ V := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv'
      · exact hf_mem r_min hr_min_mem
      · rw [Finset.mem_singleton.mp hv']
        exact hf_mem r_max hr_max_mem
    have hsum_ge : 4 * Real.pi * faceScale ≤
        ∑ v ∈ V, measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} := by
      have hnonneg : ∀ v ∈ V, 0 ≤ measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} :=
        fun _ _ => ENNReal.toReal_nonneg
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun v hv _ => hnonneg v hv)
      rw [Finset.sum_pair hv_ne] at hle
      have h1 : measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (v_min : E4) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} =
          2 * Real.pi * faceScale := hmin_area
      have h2 : measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (v_max : E4) x = 0 ∧ ∀ v' ∈ V, 0 ≤ inner ℝ (v' : E4) x} =
          2 * Real.pi * faceScale := hmax_area
      linarith
    have h4lt : faceScale * totalStdArea < 4 * Real.pi * faceScale := by
      have hfpos := faceScale_pos
      nlinarith
    linarith

private lemma exists_minimal_halfspace_set
    (V : Finset ↑(Metric.sphere (0 : E3) 1)) :
    ∀ n : ℕ, ∀ A : Finset ↑(Metric.sphere (0 : E3) 1),
      A ⊆ V → A.card = n →
      (∀ y : E3, (∀ s ∈ A, 0 ≤ inner ℝ (s : E3) y) → ∀ r ∈ V, 0 ≤ inner ℝ (r : E3) y) →
      ∃ S ⊆ A,
        (∀ y : E3, (∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y) → ∀ r ∈ V, 0 ≤ inner ℝ (r : E3) y) ∧
        ∀ s ∈ S, ∃ y_s : E3, inner ℝ (s : E3) y_s < 0 ∧
          ∀ r ∈ S, r ≠ s → 0 ≤ inner ℝ (r : E3) y_s := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hAV hcard hcone
    by_cases hmin : ∀ s ∈ A, ∃ y_s : E3, inner ℝ (s : E3) y_s < 0 ∧
        ∀ r ∈ A, r ≠ s → 0 ≤ inner ℝ (r : E3) y_s
    · exact ⟨A, Finset.Subset.rfl, hcone, hmin⟩
    · push_neg at hmin
      rcases hmin with ⟨s, hsA, hno⟩
      let A' := A.erase s
      have hA'V : A' ⊆ V := (Finset.erase_subset s A).trans hAV
      have hA'card : A'.card < n := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem hsA
      have hA'cone : ∀ y : E3, (∀ r ∈ A', 0 ≤ inner ℝ (r : E3) y) →
          ∀ v ∈ V, 0 ≤ inner ℝ (v : E3) y := by
        intro y hy
        have hsy : 0 ≤ inner ℝ (s : E3) y := by
          by_contra hlt
          push_neg at hlt
          obtain ⟨r, hrA, hne, hbad⟩ := hno y hlt
          exact absurd (hy r (Finset.mem_erase.mpr ⟨hne, hrA⟩)) (not_le.mpr hbad)
        refine hcone y (fun r hrA => ?_)
        by_cases hrs : r = s
        · rwa [hrs]
        · exact hy r (Finset.mem_erase.mpr ⟨hrs, hrA⟩)
      obtain ⟨S, hSA', hScone, hSmin⟩ := ih A'.card hA'card A' hA'V rfl hA'cone
      exact ⟨S, hSA'.trans (Finset.erase_subset s A), hScone, hSmin⟩

private lemma sphere_polygon_pole_and_edges
    {V S : Finset ↑(Metric.sphere (0 : E3) 1)}
    (hSV : S ⊆ V) (hV_card : V.card ≤ 4)
    (hScone : ∀ y : E3, (∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y) → ∀ r ∈ V, 0 ≤ inner ℝ (r : E3) y)
    (hno_planar : ¬ (∃ q : ↑(Metric.sphere (0 : E3) 1),
      ∀ r ∈ V, inner ℝ (r : E3) (q : E3) = 0))
    (z₀ : ↑(Metric.sphere (0 : E3) 1))
    (hz₀ : ∀ r ∈ V, 0 < inner ℝ (r : E3) (z₀ : E3))
    (hSmin : ∀ s ∈ S, ∃ y_s : E3, inner ℝ (s : E3) y_s < 0 ∧
      ∀ r ∈ S, r ≠ s → 0 ≤ inner ℝ (r : E3) y_s) :
    (S.card = 3 ∨ S.card = 4) ∧
    (∃ w₀ : ↑(Metric.sphere (0 : E3) 1),
      ∀ y : E3, y ≠ 0 → (∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y) → 0 < inner ℝ (w₀ : E3) y) ∧
    (∀ s ∈ S, ∃ x_s : E3, x_s ≠ 0 ∧ inner ℝ (s : E3) x_s = 0 ∧
      ∀ r ∈ S, r ≠ s → 0 < inner ℝ (r : E3) x_s) := by
  let S_E3 : Set E3 := Subtype.val '' (S : Set ↑(Metric.sphere (0 : E3) 1))
  have hspan_top : Submodule.span ℝ S_E3 = ⊤ := by
    by_contra hntop
    have hlt : Module.finrank ℝ (Submodule.span ℝ S_E3) < 3 := by
      have hle : Module.finrank ℝ (Submodule.span ℝ S_E3) ≤ 3 := by
        have := Submodule.finrank_le (Submodule.span ℝ S_E3)
        rwa [finrank_euclideanSpace_fin] at this
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hntop (Submodule.eq_top_of_finrank_eq (by rw [heq, finrank_euclideanSpace_fin]))
    have hadd : Module.finrank ℝ (Submodule.span ℝ S_E3) +
        Module.finrank ℝ (Submodule.span ℝ S_E3)ᗮ = 3 := by
      have := (Submodule.span ℝ S_E3).finrank_add_finrank_orthogonal
      rwa [finrank_euclideanSpace_fin] at this
    have hpos : 0 < Module.finrank ℝ (Submodule.span ℝ S_E3)ᗮ := by omega
    have hne_bot : (Submodule.span ℝ S_E3)ᗮ ≠ ⊥ := fun hbot => by
      rw [hbot, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨q₀, hq₀_mem, hq₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    have hq_orth : ∀ s ∈ S, inner ℝ (s : E3) q₀ = 0 := by
      intro s hs
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal' _ _).mp hq₀_mem _
        (Submodule.subset_span (Set.mem_image_of_mem _ hs))
    let q : ↑(Metric.sphere (0 : E3) 1) :=
      ⟨‖q₀‖⁻¹ • q₀, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq₀_ne)]⟩
    apply hno_planar
    refine ⟨q, fun r hr => ?_⟩
    have hplus : 0 ≤ inner ℝ (r : E3) (q : E3) := by
      refine hScone (q : E3) (fun s hs => ?_) r hr
      simp [q, inner_smul_right, hq_orth s hs]
    have hminus : 0 ≤ inner ℝ (r : E3) (-(q : E3)) := by
      refine hScone (-(q : E3)) (fun s hs => ?_) r hr
      simp [q, inner_neg_right, inner_smul_right, hq_orth s hs]
    rw [inner_neg_right] at hminus
    linarith
  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent ℝ S_E3
  have ht_top : ⊤ ≤ Submodule.span ℝ t := by rw [ht_span, hspan_top]
  have ht_top' : ⊤ ≤ Submodule.span ℝ (Set.range (Subtype.val : t → E3)) := by
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq]; exact ht_top
  have ht_fin : t.Finite := (S.finite_toSet.image Subtype.val).subset ht_sub
  letI : Fintype t := ht_fin.fintype
  let B : Module.Basis t ℝ E3 := Module.Basis.mk ht_li ht_top'
  have hcard_t : Fintype.card t = 3 := by
    rw [← Module.finrank_eq_card_basis B, finrank_euclideanSpace_fin]
  have hS_ge3 : 3 ≤ S.card := by
    have hmem_S : ∀ x : t, ∃ s ∈ S, (s : E3) = (x : E3) := fun x => ht_sub x.2
    choose fS hfS_mem hfS_eq using hmem_S
    have hfS_inj : Function.Injective fS := by
      intro x y hxy
      ext1
      rw [← hfS_eq x, ← hfS_eq y, hxy]
    have himg_sub : Finset.image fS Finset.univ ⊆ S := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
      exact hfS_mem x
    calc 3 = Fintype.card t := hcard_t.symm
      _ = (Finset.image fS Finset.univ).card := (Finset.card_image_of_injective _ hfS_inj).symm
      _ ≤ S.card := Finset.card_le_card himg_sub
  have hS_le4 : S.card ≤ 4 := (Finset.card_le_card hSV).trans hV_card
  have hcard34 : S.card = 3 ∨ S.card = 4 := by omega
  let eFin : Fin 3 ≃ t := (Fintype.equivFinOfCardEq hcard_t).symm
  let b : Fin 3 → E3 := fun j => (eFin j : E3)
  have hb_li : LinearIndependent ℝ b := ht_li.comp eFin eFin.injective
  have hb_span : Submodule.span ℝ (Set.range b) = ⊤ := by
    have : Set.range b = t := by
      ext x; simp only [Set.mem_range, b]; constructor
      · rintro ⟨j, rfl⟩; exact (eFin j).2
      · intro hx; exact ⟨eFin.symm ⟨x, hx⟩, by simp⟩
    rw [this]; exact ht_span.trans hspan_top
  have hb_mem : ∀ j : Fin 3, ∃ s ∈ S, (s : E3) = b j := by
    intro j
    obtain ⟨s, hs, hsq⟩ := ht_sub (eFin j).2
    exact ⟨s, hs, hsq⟩
  let wtilde : E3 := b 0 + b 1 + b 2
  have hwtilde_pos : ∀ y : E3, y ≠ 0 → (∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y) →
      0 < inner ℝ wtilde y := by
    intro y hy_ne hy
    have h0 : 0 ≤ inner ℝ (b 0) y := by obtain ⟨s, hs, hsq⟩ := hb_mem 0; rw [← hsq]; exact hy s hs
    have h1 : 0 ≤ inner ℝ (b 1) y := by obtain ⟨s, hs, hsq⟩ := hb_mem 1; rw [← hsq]; exact hy s hs
    have h2 : 0 ≤ inner ℝ (b 2) y := by obtain ⟨s, hs, hsq⟩ := hb_mem 2; rw [← hsq]; exact hy s hs
    have hsum_nonneg : 0 ≤ inner ℝ wtilde y := by
      simp only [wtilde, inner_add_left]; linarith
    refine lt_of_le_of_ne hsum_nonneg ?_
    intro h0eq
    simp only [wtilde, inner_add_left] at h0eq
    have hb0 : inner ℝ (b 0) y = 0 := by linarith
    have hb1 : inner ℝ (b 1) y = 0 := by linarith
    have hb2 : inner ℝ (b 2) y = 0 := by linarith
    have hy_all : ∀ z : E3, inner ℝ z y = 0 := by
      intro z
      have hz : z ∈ Submodule.span ℝ (Set.range b) := by rw [hb_span]; trivial
      induction hz using Submodule.span_induction with
      | mem u hu =>
          rcases hu with ⟨j, rfl⟩
          fin_cases j <;> assumption
      | zero => simp
      | add x₁ x₂ _ _ hx₁ hx₂ => rw [inner_add_left, hx₁, hx₂, add_zero]
      | smul c x₁ _ hx₁ => rw [inner_smul_left, hx₁, mul_zero]
    have hny : ‖y‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact hy_all y
    exact hy_ne (norm_eq_zero.mp (sq_eq_zero_iff.mp hny))
  have hwtilde_ne : wtilde ≠ 0 := by
    intro h0
    have hz_ne : (z₀ : E3) ≠ 0 := by
      intro hz; have := z₀.2; simp [Metric.mem_sphere, hz] at this
    have := hwtilde_pos (z₀ : E3) hz_ne (fun s hs => (hz₀ s (hSV hs)).le)
    rw [h0, inner_zero_left] at this
    linarith
  have hw_pos : 0 < ‖wtilde‖ := norm_pos_iff.mpr hwtilde_ne
  let w₀ : ↑(Metric.sphere (0 : E3) 1) :=
    ⟨‖wtilde‖⁻¹ • wtilde, by simp [norm_smul, inv_mul_cancel₀ hw_pos.ne']⟩
  have hw₀_pos : ∀ y : E3, y ≠ 0 → (∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y) →
      0 < inner ℝ (w₀ : E3) y := by
    intro y hy_ne hy
    change 0 < inner ℝ (‖wtilde‖⁻¹ • wtilde) y
    rw [real_inner_smul_left]
    exact mul_pos (inv_pos.mpr hw_pos) (hwtilde_pos y hy_ne hy)
  refine ⟨hcard34, ⟨w₀, hw₀_pos⟩, fun s hs => ?_⟩
  obtain ⟨y_s, hys_neg, hys_nonneg⟩ := hSmin s hs
  let x_s : E3 := (-inner ℝ (s : E3) y_s) • (z₀ : E3) + inner ℝ (s : E3) (z₀ : E3) • y_s
  have hxs_zero : inner ℝ (s : E3) x_s = 0 := by
    simp only [x_s, inner_add_right, inner_smul_right]; ring
  have hxs_pos : ∀ r ∈ S, r ≠ s → 0 < inner ℝ (r : E3) x_s := by
    intro r hr hrs
    have h1 : 0 < -inner ℝ (s : E3) y_s := neg_pos.mpr hys_neg
    have h2 : 0 < inner ℝ (r : E3) (z₀ : E3) := hz₀ r (hSV hr)
    have h3 : 0 < inner ℝ (s : E3) (z₀ : E3) := hz₀ s (hSV hs)
    have h4 : 0 ≤ inner ℝ (r : E3) y_s := hys_nonneg r hr hrs
    simp only [x_s, inner_add_right, inner_smul_right]
    nlinarith
  have hxs_ne : x_s ≠ 0 := by
    have hex : ∃ r ∈ S, r ≠ s := by
      have hcard2 : 1 < (S.erase s).card := by
        rw [Finset.card_erase_of_mem hs]; omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase s).card)
      exact ⟨r, Finset.mem_of_mem_erase hr, Finset.ne_of_mem_erase hr⟩
    rcases hex with ⟨r, hr, hrs⟩
    intro h0
    have := hxs_pos r hr hrs
    rw [h0, inner_zero_right] at this
    linarith
  exact ⟨x_s, hxs_ne, hxs_zero, hxs_pos⟩

private noncomputable def ang2 (a b : ℝ) : ℝ :=
  if 0 ≤ b then Real.arccos (a / Real.sqrt (a ^ 2 + b ^ 2))
  else 2 * Real.pi - Real.arccos (a / Real.sqrt (a ^ 2 + b ^ 2))

private lemma ang2_cos_sin {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < Real.sqrt (a ^ 2 + b ^ 2) ∧
    a = Real.sqrt (a ^ 2 + b ^ 2) * Real.cos (ang2 a b) ∧
    b = Real.sqrt (a ^ 2 + b ^ 2) * Real.sin (ang2 a b) := by
  have hsq_pos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero hb)
  set r := Real.sqrt (a ^ 2 + b ^ 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hsq_pos
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hsq_pos.le
  have hunit : (a / r) ^ 2 + (b / r) ^ 2 = 1 := by
    field_simp [hr_pos.ne']
    linarith [hr2]
  have har_lo : -1 ≤ a / r := by nlinarith [sq_nonneg (b / r)]
  have har_hi : a / r ≤ 1 := by nlinarith [sq_nonneg (b / r)]
  refine ⟨hr_pos, ?_, ?_⟩
  · by_cases hb : 0 ≤ b
    · rw [ang2, if_pos hb, Real.cos_arccos har_lo har_hi]
      field_simp [hr_pos.ne']
    · rw [ang2, if_neg hb, Real.cos_two_pi_sub, Real.cos_arccos har_lo har_hi]
      field_simp [hr_pos.ne']
  · have hsin_sq : 1 - (a / √(a ^ 2 + b ^ 2)) ^ 2 = ((-b) / √(a ^ 2 + b ^ 2)) ^ 2 := by
      change 1 - (a / r) ^ 2 = ((-b) / r) ^ 2
      have hneg : ((-b) / r) ^ 2 = (b / r) ^ 2 := by ring
      rw [hneg]
      linarith
    by_cases hb : 0 ≤ b
    · rw [ang2, if_pos hb, Real.sin_arccos,
        show 1 - (a / r) ^ 2 = (b / r) ^ 2 by linarith,
        Real.sqrt_sq (div_nonneg hb hr_pos.le)]
      field_simp [hr_pos.ne']
    · push_neg at hb
      rw [ang2, if_neg hb.not_ge, Real.sin_two_pi_sub, Real.sin_arccos,
        hsin_sq, Real.sqrt_sq (div_nonneg (by linarith) hr_pos.le)]
      change b = r * -((-b) / r)
      field_simp [hr_pos.ne']

private lemma ang2_bounds {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) :
    0 ≤ ang2 a b ∧ ang2 a b < 2 * Real.pi := by
  have hsq_pos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg b)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero hb)
  set r := Real.sqrt (a ^ 2 + b ^ 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hsq_pos
  have hr2 : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hsq_pos.le
  by_cases hb : 0 ≤ b
  · rw [ang2, if_pos hb]
    exact ⟨Real.arccos_nonneg _, (Real.arccos_le_pi _).trans_lt (by linarith [Real.pi_pos])⟩
  · push_neg at hb
    rw [ang2, if_neg hb.not_ge]
    have har_lt : a / r < 1 := by
      have hunit : (a / r) ^ 2 + (b / r) ^ 2 = 1 := by field_simp [hr_pos.ne']; linarith [hr2]
      have hbr2 : 0 < (b / r) ^ 2 := sq_pos_of_ne_zero (div_ne_zero hb.ne hr_pos.ne')
      nlinarith
    have harc_pos : 0 < Real.arccos (a / r) := Real.arccos_pos.mpr har_lt
    have harc_le : Real.arccos (a / r) ≤ Real.pi := Real.arccos_le_pi _
    constructor <;> linarith [Real.pi_pos]

private lemma finset_sort_by_inj {α : Type*} (S : Finset α) (φ : α → ℝ)
    (hφ : Set.InjOn φ (S : Set α)) :
    ∃ seq : Fin S.card → α,
      (∀ i, seq i ∈ S) ∧ Function.Injective seq ∧ (∀ s ∈ S, ∃ i, seq i = s) ∧
      StrictMono (fun i => φ (seq i)) := by
  let img := S.image φ
  have hcard : img.card = S.card := Finset.card_image_of_injOn hφ
  let emb := img.orderEmbOfFin hcard
  have hex : ∀ i : Fin S.card, ∃ a ∈ S, φ a = emb i := fun i =>
    Finset.mem_image.mp (img.orderEmbOfFin_mem hcard i)
  choose seq hseq_mem hseq_eq using hex
  have hmono : StrictMono (fun i => φ (seq i)) := by
    intro i j hij
    dsimp only
    rw [hseq_eq i, hseq_eq j]
    exact emb.strictMono hij
  have hinj : Function.Injective seq := by
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (congrArg φ hij) (hmono h).ne
    · exact h
    · exact absurd (congrArg φ hij.symm) (hmono h).ne
  have hsurj : ∀ s ∈ S, ∃ i, seq i = s := by
    intro s hs
    have himg_eq : Finset.image (fun i : Fin S.card => (emb i : ℝ)) Finset.univ = img := by
      refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
      · rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
        exact img.orderEmbOfFin_mem hcard i
      · rw [Finset.card_image_of_injective _ emb.injective, Finset.card_fin, hcard]
    have hmem : φ s ∈ Finset.image (fun i : Fin S.card => (emb i : ℝ)) Finset.univ :=
      himg_eq ▸ Finset.mem_image_of_mem φ hs
    rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
    refine ⟨i, hφ (hseq_mem i) hs ?_⟩
    rw [hseq_eq i, hi]
  exact ⟨seq, hseq_mem, hinj, hsurj, hmono⟩

private lemma fin_val_add_one_lt {m : ℕ} [NeZero m] (hm : 3 ≤ m) {i : Fin m}
    (h : (i : ℕ) + 1 ≠ m) : ((i + 1 : Fin m) : ℕ) = (i : ℕ) + 1 := by
  have h1val : ((1 : Fin m) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  rw [Fin.val_add, h1val, Nat.mod_eq_of_lt (lt_of_le_of_ne i.isLt h)]

private lemma fin_add_one_eq_zero {m : ℕ} [NeZero m] (hm : 3 ≤ m) {i : Fin m}
    (h : (i : ℕ) + 1 = m) : (i + 1 : Fin m) = 0 := by
  have h1val : ((1 : Fin m) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  ext
  rw [Fin.val_add, h1val, h, Nat.mod_self, Fin.val_zero]

private lemma fin_succ_ne_self {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i : Fin m) : i + 1 ≠ i := by
  intro h
  have h1 : (1 : Fin m) = 0 := by
    calc (1 : Fin m) = (i + 1) - i := by abel
      _ = i - i := by rw [h]
      _ = 0 := sub_self i
  have h1val : ((1 : Fin m) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  have hv := congrArg Fin.val h1
  rw [h1val, Fin.val_zero] at hv
  exact one_ne_zero hv

private lemma affine_pos_case1 {Lk p1k p1i M1 : ℝ}
    (hp1k : 0 < p1k) (hp1i : 0 < p1i) (hM1 : M1 < 0) (heq : p1k = Lk + M1 * p1i) : 0 < Lk := by
  nlinarith

private lemma affine_pos_case2 {Lk qk qi qi1 M1 M2 : ℝ}
    (hqk : 0 < qk) (hqi : 0 < qi) (hqi1 : 0 < qi1) (hM1 : M1 ≤ 0) (hM2 : M2 ≤ 0)
    (heq : qk = Lk + M1 * qi + M2 * qi1) : 0 < Lk := by
  nlinarith

private lemma affine_pos_case3 {Lk p0k p0i1 M2 : ℝ}
    (hp0k : 0 < p0k) (hp0i1 : 0 < p0i1) (hM2 : M2 < 0) (heq : p0k = Lk + M2 * p0i1) : 0 < Lk := by
  nlinarith

private lemma polygon_cyclic_vertices
    {S : Finset ↑(Metric.sphere (0 : E3) 1)}
    [NeZero S.card]
    (hS_card : 3 ≤ S.card)
    (z₀ : ↑(Metric.sphere (0 : E3) 1))
    (hz₀ : ∀ s ∈ S, 0 < inner ℝ (s : E3) (z₀ : E3))
    (w₀ : ↑(Metric.sphere (0 : E3) 1))
    (hw₀ : ∀ y : E3, y ≠ 0 → (∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y) → 0 < inner ℝ (w₀ : E3) y)
    (hx_edge : ∀ s ∈ S, ∃ x_s : E3, x_s ≠ 0 ∧ inner ℝ (s : E3) x_s = 0 ∧
      ∀ r ∈ S, r ≠ s → 0 < inner ℝ (r : E3) x_s) :
    ∃ seq : Fin S.card → ↑(Metric.sphere (0 : E3) 1),
    ∃ V : Fin S.card → ↑(Metric.sphere (0 : E3) 1),
      (∀ k, seq k ∈ S) ∧ Function.Injective seq ∧ (∀ s ∈ S, ∃ k, seq k = s) ∧
      (∀ i k : Fin S.card, 0 ≤ inner ℝ (seq k : E3) (V i : E3)) ∧
      (∀ i : Fin S.card, inner ℝ (seq i : E3) (V i : E3) = 0 ∧
        inner ℝ (seq (i + 1) : E3) (V i : E3) = 0) ∧
      (∀ i k : Fin S.card, k ≠ i → k ≠ i + 1 → 0 < inner ℝ (seq k : E3) (V i : E3)) ∧
      (∀ i : Fin S.card, 0 < inner ℝ (w₀ : E3) (V i : E3)) := by
  have hw0_norm : ‖(w₀ : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w₀.2
  obtain ⟨e₁, e₂, he1, he2, he1w, he2w, he12⟩ := exists_orthonormal_pair_ortho_E3 (w₀ : E3) hw0_norm
  have hwo_e1 : inner ℝ (w₀ : E3) e₁ = 0 := by rw [real_inner_comm]; exact he1w
  have hwo_e2 : inner ℝ (w₀ : E3) e₂ = 0 := by rw [real_inner_comm]; exact he2w
  let aF : ↑(Metric.sphere (0 : E3) 1) → ℝ := fun s => inner ℝ (s : E3) e₁
  let bF : ↑(Metric.sphere (0 : E3) 1) → ℝ := fun s => inner ℝ (s : E3) e₂
  let cF : ↑(Metric.sphere (0 : E3) 1) → ℝ := fun s => inner ℝ (s : E3) (w₀ : E3)
  let linForm : ↑(Metric.sphere (0 : E3) 1) → ℝ × ℝ → ℝ :=
    fun s q => cF s + aF s * q.1 + bF s * q.2
  have hz₀_ne : (z₀ : E3) ≠ 0 := by
    intro hz; have := z₀.2; simp [Metric.mem_sphere, hz] at this
  have hwz₀ : 0 < inner ℝ (w₀ : E3) (z₀ : E3) :=
    hw₀ (z₀ : E3) hz₀_ne (fun r hr => (hz₀ r hr).le)
  let q₀ : ℝ × ℝ := (inner ℝ (z₀ : E3) e₁ / inner ℝ (w₀ : E3) (z₀ : E3),
    inner ℝ (z₀ : E3) e₂ / inner ℝ (w₀ : E3) (z₀ : E3))
  have hq₀_pos : ∀ s ∈ S, 0 < linForm s q₀ := by
    intro s hs
    have hy_decomp : inner ℝ (s : E3) (z₀ : E3) =
        inner ℝ (s : E3) (w₀ : E3) * inner ℝ (w₀ : E3) (z₀ : E3) +
        inner ℝ (s : E3) e₁ * inner ℝ (z₀ : E3) e₁ +
        inner ℝ (s : E3) e₂ * inner ℝ (z₀ : E3) e₂ := by
      rw [orthonormal_E3_inner hw0_norm he1 he2 hwo_e1 hwo_e2 he12,
        real_inner_comm e₁ (z₀ : E3), real_inner_comm e₂ (z₀ : E3)]
    have hval : linForm s q₀ = inner ℝ (s : E3) (z₀ : E3) / inner ℝ (w₀ : E3) (z₀ : E3) := by
      dsimp [linForm, cF, aF, bF, q₀]
      rw [hy_decomp]
      field_simp [hwz₀.ne']
    rw [hval]
    exact div_pos (hz₀ s hs) hwz₀
  have hp_exists : ∀ s ∈ S, ∃ p : ℝ × ℝ, linForm s p = 0 ∧
      ∀ r ∈ S, r ≠ s → 0 < linForm r p := by
    intro s hs
    obtain ⟨x_s, hxs_ne, hxs0, hxs_pos⟩ := hx_edge s hs
    have hwxs : 0 < inner ℝ (w₀ : E3) x_s := hw₀ x_s hxs_ne (fun r hr => by
      by_cases hrs : r = s
      · rw [hrs, hxs0]
      · exact (hxs_pos r hr hrs).le)
    let p : ℝ × ℝ := (inner ℝ x_s e₁ / inner ℝ (w₀ : E3) x_s,
      inner ℝ x_s e₂ / inner ℝ (w₀ : E3) x_s)
    have hval : ∀ r : ↑(Metric.sphere (0 : E3) 1),
        linForm r p = inner ℝ (r : E3) x_s / inner ℝ (w₀ : E3) x_s := by
      intro r
      have hy_decomp : inner ℝ (r : E3) x_s =
          inner ℝ (r : E3) (w₀ : E3) * inner ℝ (w₀ : E3) x_s +
          inner ℝ (r : E3) e₁ * inner ℝ x_s e₁ +
          inner ℝ (r : E3) e₂ * inner ℝ x_s e₂ := by
        rw [orthonormal_E3_inner hw0_norm he1 he2 hwo_e1 hwo_e2 he12,
          real_inner_comm e₁ x_s, real_inner_comm e₂ x_s]
      dsimp [linForm, cF, aF, bF, p]
      rw [hy_decomp]
      field_simp [hwxs.ne']
    refine ⟨p, ?_, fun r hr hrs => ?_⟩
    · rw [hval s, hxs0, zero_div]
    · rw [hval r]; exact div_pos (hxs_pos r hr hrs) hwxs
  choose pF hpF_zero hpF_pos using fun (s : {s // s ∈ S}) => hp_exists s.1 s.2
  have hlVec_ne : ∀ s ∈ S, aF s ≠ 0 ∨ bF s ≠ 0 := by
    intro s hs
    by_contra h
    push_neg at h
    rcases h with ⟨ha0, hb0⟩
    have hex : ∃ r ∈ S, r ≠ s := by
      have hcard2 : 0 < (S.erase s).card := by rw [Finset.card_erase_of_mem hs]; omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp hcard2
      exact ⟨r, Finset.mem_of_mem_erase hr, Finset.ne_of_mem_erase hr⟩
    rcases hex with ⟨r, hr, hrs⟩
    have hzero := hpF_zero ⟨s, hs⟩
    have hpos := hpF_pos ⟨r, hr⟩ s hs hrs.symm
    dsimp [linForm] at hzero hpos
    rw [ha0, hb0] at hzero hpos
    linarith
  have hphi_inj : Set.InjOn (fun s => ang2 (aF s) (bF s)) (S : Set _) := by
    intro s₁ hs₁ s₂ hs₂ heq
    dsimp only at heq
    have hcs1 := ang2_cos_sin (hlVec_ne s₁ hs₁)
    have hcs2 := ang2_cos_sin (hlVec_ne s₂ hs₂)
    set r₁ := Real.sqrt (aF s₁ ^ 2 + bF s₁ ^ 2)
    set r₂ := Real.sqrt (aF s₂ ^ 2 + bF s₂ ^ 2)
    let lam : ℝ := r₂ / r₁
    have hlam_pos : 0 < lam := div_pos hcs2.1 hcs1.1
    have ha2 : aF s₂ = lam * aF s₁ := by
      calc aF s₂ = r₂ * Real.cos (ang2 (aF s₂) (bF s₂)) := hcs2.2.1
        _ = r₂ * Real.cos (ang2 (aF s₁) (bF s₁)) := by rw [heq]
        _ = lam * (r₁ * Real.cos (ang2 (aF s₁) (bF s₁))) := by
            dsimp [lam]; field_simp [hcs1.1.ne']
        _ = lam * aF s₁ := by rw [← hcs1.2.1]
    have hb2 : bF s₂ = lam * bF s₁ := by
      calc bF s₂ = r₂ * Real.sin (ang2 (aF s₂) (bF s₂)) := hcs2.2.2
        _ = r₂ * Real.sin (ang2 (aF s₁) (bF s₁)) := by rw [heq]
        _ = lam * (r₁ * Real.sin (ang2 (aF s₁) (bF s₁))) := by
            dsimp [lam]; field_simp [hcs1.1.ne']
        _ = lam * bF s₁ := by rw [← hcs1.2.2]
    by_contra hne
    by_cases hc : cF s₂ ≤ lam * cF s₁
    · have h1 := hpF_zero ⟨s₁, hs₁⟩
      have h2 := hpF_pos ⟨s₁, hs₁⟩ s₂ hs₂ (Ne.symm hne)
      have : linForm s₂ (pF ⟨s₁, hs₁⟩) ≤ lam * linForm s₁ (pF ⟨s₁, hs₁⟩) := by
        dsimp [linForm]; rw [ha2, hb2]; linarith
      rw [h1, mul_zero] at this
      linarith
    · push_neg at hc
      have h1 := hpF_zero ⟨s₂, hs₂⟩
      have h2 := hpF_pos ⟨s₂, hs₂⟩ s₁ hs₁ hne
      have : lam * linForm s₁ (pF ⟨s₂, hs₂⟩) < linForm s₂ (pF ⟨s₂, hs₂⟩) := by
        dsimp [linForm]; rw [ha2, hb2]; linarith
      rw [h1] at this
      nlinarith
  obtain ⟨seq, hseq_mem, hseq_inj, hseq_surj, hseq_mono⟩ :=
    finset_sort_by_inj S (fun s => ang2 (aF s) (bF s)) hphi_inj
  let θ : Fin S.card → ℝ := fun i => ang2 (aF (seq i)) (bF (seq i))
  have hθ_bounds : ∀ i, 0 ≤ θ i ∧ θ i < 2 * Real.pi :=
    fun i => ang2_bounds (hlVec_ne (seq i) (hseq_mem i))
  have hno_half : ∀ u₁ u₂ : ℝ, u₁ ≠ 0 ∨ u₂ ≠ 0 →
      ¬ (∀ i : Fin S.card, 0 ≤ aF (seq i) * u₁ + bF (seq i) * u₂) := by
    intro u₁ u₂ hu hall
    let y : E3 := u₁ • e₁ + u₂ • e₂
    have hy_ne : y ≠ 0 := by
      intro h0
      have hi1 : inner ℝ e₁ y = 0 := by rw [h0, inner_zero_right]
      have hi2 : inner ℝ e₂ y = 0 := by rw [h0, inner_zero_right]
      have h1e : inner ℝ e₁ y = u₁ := by
        simp [y, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he1, he12]
      have h2e : inner ℝ e₂ y = u₂ := by
        simp [y, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he2,
          show inner ℝ e₂ e₁ = 0 by rw [real_inner_comm]; exact he12]
      rcases hu with h1 | h2
      · exact h1 (h1e ▸ hi1)
      · exact h2 (h2e ▸ hi2)
    have hy_mem : ∀ s ∈ S, 0 ≤ inner ℝ (s : E3) y := by
      intro s hs
      obtain ⟨i, rfl⟩ := hseq_surj s hs
      have heq : inner ℝ (seq i : E3) y = aF (seq i) * u₁ + bF (seq i) * u₂ := by
        simp only [y, aF, bF, inner_add_right, inner_smul_right]; ring
      rw [heq]; exact hall i
    have hwy : 0 < inner ℝ (w₀ : E3) y := hw₀ y hy_ne hy_mem
    have hwy0 : inner ℝ (w₀ : E3) y = 0 := by
      simp [y, inner_add_right, inner_smul_right, hwo_e1, hwo_e2]
    linarith
  let θnext : Fin S.card → ℝ := fun i =>
    if (i : ℕ) + 1 = S.card then θ (i + 1) + 2 * Real.pi else θ (i + 1)
  let δ : Fin S.card → ℝ := fun i => θnext i - θ i
  have hδ_pos : ∀ i, 0 < δ i := by
    intro i
    dsimp [δ, θnext]
    split_ifs with h
    · linarith [(hθ_bounds (i + 1)).1, (hθ_bounds i).2]
    · have hsucc : i < i + 1 := by
        change (i : ℕ) < ((i + 1 : Fin S.card) : ℕ)
        rw [fin_val_add_one_lt hS_card h]
        exact Nat.lt_succ_self _
      exact sub_pos.mpr (hseq_mono hsucc)
  have hδ_lt_pi : ∀ i, δ i < Real.pi := by
    intro i
    by_contra hpi
    push_neg at hpi
    by_cases hwrap : (i : ℕ) + 1 = S.card
    · have hzero : (i + 1 : Fin S.card) = 0 := fin_add_one_eq_zero hS_card hwrap
      have hδ_eq : δ i = θ 0 + 2 * Real.pi - θ i := by
        dsimp [δ, θnext]; rw [if_pos hwrap, hzero]
      dsimp [δ, θnext] at hpi
      rw [if_pos hwrap, hzero] at hpi
      have hspan_le : θ i - θ 0 ≤ Real.pi := by linarith
      let ψ : ℝ := (θ 0 + θ i) / 2
      have hcos_ge : ∀ j : Fin S.card, 0 ≤ Real.cos (θ j - ψ) := by
        intro j
        have hj0 : (0 : Fin S.card) ≤ j := Fin.zero_le j
        have hji : j ≤ i := by
          change (j : ℕ) ≤ (i : ℕ); omega
        have hθ0j : θ 0 ≤ θ j := hseq_mono.monotone hj0
        have hθji : θ j ≤ θ i := hseq_mono.monotone hji
        dsimp only [ψ]
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      apply hno_half (Real.cos ψ) (Real.sin ψ) (by
        by_contra h0; push_neg at h0
        have h1 := Real.sin_sq_add_cos_sq ψ
        rw [h0.1, h0.2] at h1; norm_num at h1)
      intro j
      have hcsj := ang2_cos_sin (hlVec_ne (seq j) (hseq_mem j))
      set rj := Real.sqrt (aF (seq j) ^ 2 + bF (seq j) ^ 2)
      have ha_j : aF (seq j) = rj * Real.cos (θ j) := hcsj.2.1
      have hb_j : bF (seq j) = rj * Real.sin (θ j) := hcsj.2.2
      calc 0 ≤ rj * Real.cos (θ j - ψ) := mul_nonneg hcsj.1.le (hcos_ge j)
        _ = rj * (Real.cos (θ j) * Real.cos ψ + Real.sin (θ j) * Real.sin ψ) := by
            rw [Real.cos_sub]
        _ = aF (seq j) * Real.cos ψ + bF (seq j) * Real.sin ψ := by rw [ha_j, hb_j]; ring
    · have hδ_eq : δ i = θ (i + 1) - θ i := by dsimp [δ, θnext]; rw [if_neg hwrap]
      dsimp [δ, θnext] at hpi
      rw [if_neg hwrap] at hpi
      let ψ : ℝ := (θ (i + 1) + θ i + 2 * Real.pi) / 2
      have hcos_ge : ∀ j : Fin S.card, 0 ≤ Real.cos (θ j - ψ) := by
        intro j
        by_cases hji : j ≤ i
        · rw [← Real.cos_add_two_pi (θ j - ψ), show θ j - ψ + 2 * Real.pi = (θ j + 2 * Real.pi) - ψ by ring]
          have h0j : 0 ≤ θ j := (hθ_bounds j).1
          have hi1_lt : θ (i + 1) < 2 * Real.pi := (hθ_bounds (i + 1)).2
          have hθji : θ j ≤ θ i := hseq_mono.monotone hji
          dsimp only [ψ]
          exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
        · push_neg at hji
          have hsucc_le : i + 1 ≤ j := by
            change ((i + 1 : Fin S.card) : ℕ) ≤ (j : ℕ)
            rw [fin_val_add_one_lt hS_card hwrap]
            exact hji
          have h0i : 0 ≤ θ i := (hθ_bounds i).1
          have hj_lt : θ j < 2 * Real.pi := (hθ_bounds j).2
          have h1 : θ (i + 1) ≤ θ j := hseq_mono.monotone hsucc_le
          dsimp only [ψ]
          exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      apply hno_half (Real.cos ψ) (Real.sin ψ) (by
        by_contra h0; push_neg at h0
        have h1 := Real.sin_sq_add_cos_sq ψ
        rw [h0.1, h0.2] at h1; norm_num at h1)
      intro j
      have hcsj := ang2_cos_sin (hlVec_ne (seq j) (hseq_mem j))
      set rj := Real.sqrt (aF (seq j) ^ 2 + bF (seq j) ^ 2)
      have ha_j : aF (seq j) = rj * Real.cos (θ j) := hcsj.2.1
      have hb_j : bF (seq j) = rj * Real.sin (θ j) := hcsj.2.2
      calc 0 ≤ rj * Real.cos (θ j - ψ) := mul_nonneg hcsj.1.le (hcos_ge j)
        _ = rj * (Real.cos (θ j) * Real.cos ψ + Real.sin (θ j) * Real.sin ψ) := by
            rw [Real.cos_sub]
        _ = aF (seq j) * Real.cos ψ + bF (seq j) * Real.sin ψ := by rw [ha_j, hb_j]; ring
  have hsin_δ_eq : ∀ i, Real.sin (θ (i + 1) - θ i) = Real.sin (δ i) := by
    intro i
    dsimp [δ, θnext]
    split_ifs with h
    · rw [show θ (i + 1) + 2 * Real.pi - θ i = (θ (i + 1) - θ i) + 2 * Real.pi by ring,
        Real.sin_add_two_pi]
    · rfl
  let rF : Fin S.card → ℝ := fun i => Real.sqrt (aF (seq i) ^ 2 + bF (seq i) ^ 2)
  have hrF_pos : ∀ i, 0 < rF i := fun i => (ang2_cos_sin (hlVec_ne (seq i) (hseq_mem i))).1
  let detF : Fin S.card → ℝ := fun i =>
    aF (seq i) * bF (seq (i + 1)) - bF (seq i) * aF (seq (i + 1))
  have hdetF_eq : ∀ i, detF i = rF i * rF (i + 1) * Real.sin (δ i) := by
    intro i
    have hcs1 := ang2_cos_sin (hlVec_ne (seq i) (hseq_mem i))
    have hcs2 := ang2_cos_sin (hlVec_ne (seq (i + 1)) (hseq_mem (i + 1)))
    have ha1 : aF (seq i) = rF i * Real.cos (θ i) := hcs1.2.1
    have hb1 : bF (seq i) = rF i * Real.sin (θ i) := hcs1.2.2
    have ha2 : aF (seq (i + 1)) = rF (i + 1) * Real.cos (θ (i + 1)) := hcs2.2.1
    have hb2 : bF (seq (i + 1)) = rF (i + 1) * Real.sin (θ (i + 1)) := hcs2.2.2
    calc detF i
        = aF (seq i) * bF (seq (i + 1)) - bF (seq i) * aF (seq (i + 1)) := rfl
      _ = rF i * rF (i + 1) * (Real.sin (θ (i + 1)) * Real.cos (θ i) -
            Real.cos (θ (i + 1)) * Real.sin (θ i)) := by rw [ha1, hb1, ha2, hb2]; ring
      _ = rF i * rF (i + 1) * Real.sin (θ (i + 1) - θ i) := by rw [← Real.sin_sub]
      _ = rF i * rF (i + 1) * Real.sin (δ i) := by rw [hsin_δ_eq i]
  have hdetF_pos : ∀ i, 0 < detF i := by
    intro i
    rw [hdetF_eq i]
    exact mul_pos (mul_pos (hrF_pos i) (hrF_pos (i + 1)))
      (Real.sin_pos_of_pos_of_lt_pi (hδ_pos i) (hδ_lt_pi i))
  let qV : Fin S.card → ℝ × ℝ := fun i =>
    ((bF (seq i) * cF (seq (i + 1)) - bF (seq (i + 1)) * cF (seq i)) / detF i,
     (aF (seq (i + 1)) * cF (seq i) - aF (seq i) * cF (seq (i + 1))) / detF i)
  have hqV_zero : ∀ i, linForm (seq i) (qV i) = 0 ∧ linForm (seq (i + 1)) (qV i) = 0 := by
    intro i
    have hne : detF i ≠ 0 := (hdetF_pos i).ne'
    dsimp [linForm, qV]
    constructor <;> · field_simp [hne]; dsimp [detF]; ring
  have hqV_pos : ∀ i k : Fin S.card, k ≠ i → k ≠ i + 1 → 0 < linForm (seq k) (qV i) := by
    intro i k hki hki1
    let φ : ℝ := if θ i ≤ θ k then θ k - θ i else θ k + 2 * Real.pi - θ i
    have hφ_gt : δ i < φ := by
      dsimp [φ, δ, θnext]
      by_cases hwrap : (i : ℕ) + 1 = S.card
      · rw [if_pos hwrap]
        have hzero : (i + 1 : Fin S.card) = 0 := fin_add_one_eq_zero hS_card hwrap
        have hk_lt_i : k < i := lt_of_le_of_ne (by change (k : ℕ) ≤ (i : ℕ); omega) hki
        have hnot_le : ¬ θ i ≤ θ k := not_le.mpr (hseq_mono hk_lt_i)
        rw [if_neg hnot_le, hzero]
        have hk0 : 0 < k :=
          lt_of_le_of_ne (Fin.zero_le k) (fun h0 => hki1 (h0.symm.trans hzero.symm))
        linarith [hseq_mono hk0]
      · rw [if_neg hwrap]
        by_cases hle : θ i ≤ θ k
        · rw [if_pos hle]
          have hik : i < k := lt_of_le_of_ne (by
            by_contra hlt; push_neg at hlt
            exact absurd (hseq_mono hlt) (not_lt.mpr hle)) hki.symm
          have hi1_lt_k : i + 1 < k := by
            refine lt_of_le_of_ne ?_ hki1.symm
            change ((i + 1 : Fin S.card) : ℕ) ≤ (k : ℕ)
            rw [fin_val_add_one_lt hS_card hwrap]
            exact hik
          linarith [hseq_mono hi1_lt_k]
        · rw [if_neg hle]
          linarith [(hθ_bounds (i + 1)).2, (hθ_bounds k).1]
    have hφ_lt_2pi : φ < 2 * Real.pi := by
      dsimp [φ]
      split_ifs with hle
      · linarith [(hθ_bounds k).2, (hθ_bounds i).1]
      · linarith [not_le.mp hle]
    have hsin_φ : Real.sin (θ k - θ i) = Real.sin φ := by
      dsimp [φ]
      split_ifs with hle
      · rfl
      · rw [show θ k + 2 * Real.pi - θ i = (θ k - θ i) + 2 * Real.pi by ring, Real.sin_add_two_pi]
    have hsin_δφ : Real.sin (θ (i + 1) - θ k) = Real.sin (δ i - φ) := by
      dsimp [δ, θnext, φ]
      by_cases hwrap : (i : ℕ) + 1 = S.card <;> by_cases hle : θ i ≤ θ k
      · rw [if_pos hwrap, if_pos hle]
        rw [show θ (i + 1) + 2 * Real.pi - θ i - (θ k - θ i) =
          (θ (i + 1) - θ k) + 2 * Real.pi by ring, Real.sin_add_two_pi]
      · rw [if_pos hwrap, if_neg hle]
        rw [show θ (i + 1) + 2 * Real.pi - θ i - (θ k + 2 * Real.pi - θ i) =
          θ (i + 1) - θ k by ring]
      · rw [if_neg hwrap, if_pos hle]
        rw [show θ (i + 1) - θ i - (θ k - θ i) = θ (i + 1) - θ k by ring]
      · rw [if_neg hwrap, if_neg hle]
        rw [show θ (i + 1) - θ i - (θ k + 2 * Real.pi - θ i) =
          (θ (i + 1) - θ k) - 2 * Real.pi by ring, Real.sin_sub_two_pi]
    have hsin_δ_pos : 0 < Real.sin (δ i) :=
      Real.sin_pos_of_pos_of_lt_pi (hδ_pos i) (hδ_lt_pi i)
    let M₁ : ℝ := (rF k / rF i) * (Real.sin (δ i - φ) / Real.sin (δ i))
    let M₂ : ℝ := (rF k / rF (i + 1)) * (Real.sin φ / Real.sin (δ i))
    have hcs_i := ang2_cos_sin (hlVec_ne (seq i) (hseq_mem i))
    have hcs_i1 := ang2_cos_sin (hlVec_ne (seq (i + 1)) (hseq_mem (i + 1)))
    have hcs_k := ang2_cos_sin (hlVec_ne (seq k) (hseq_mem k))
    have ha_comb : aF (seq k) = M₁ * aF (seq i) + M₂ * aF (seq (i + 1)) := by
      have hid : Real.sin (θ (i + 1) - θ i) * Real.cos (θ k) =
          Real.sin (θ (i + 1) - θ k) * Real.cos (θ i) +
          Real.sin (θ k - θ i) * Real.cos (θ (i + 1)) := by
        rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring
      have ha_i : aF (seq i) = rF i * Real.cos (θ i) := hcs_i.2.1
      have ha_i1 : aF (seq (i + 1)) = rF (i + 1) * Real.cos (θ (i + 1)) := hcs_i1.2.1
      have ha_k : aF (seq k) = rF k * Real.cos (θ k) := hcs_k.2.1
      have hden_ne : Real.sin (δ i) ≠ 0 := hsin_δ_pos.ne'
      calc aF (seq k)
          = rF k * Real.cos (θ k) := ha_k
        _ = (rF k / Real.sin (δ i)) * (Real.sin (θ (i + 1) - θ i) * Real.cos (θ k)) := by
            rw [hsin_δ_eq i]; field_simp [hden_ne]
        _ = (rF k / Real.sin (δ i)) * (Real.sin (θ (i + 1) - θ k) * Real.cos (θ i) +
              Real.sin (θ k - θ i) * Real.cos (θ (i + 1))) := by rw [hid]
        _ = (rF k / Real.sin (δ i)) * (Real.sin (δ i - φ) * Real.cos (θ i) +
              Real.sin φ * Real.cos (θ (i + 1))) := by rw [hsin_δφ, hsin_φ]
        _ = M₁ * (rF i * Real.cos (θ i)) + M₂ * (rF (i + 1) * Real.cos (θ (i + 1))) := by
            dsimp [M₁, M₂]; field_simp [(hrF_pos i).ne', (hrF_pos (i + 1)).ne', hden_ne]
        _ = M₁ * aF (seq i) + M₂ * aF (seq (i + 1)) := by rw [← ha_i, ← ha_i1]
    have hb_comb : bF (seq k) = M₁ * bF (seq i) + M₂ * bF (seq (i + 1)) := by
      have hid : Real.sin (θ (i + 1) - θ i) * Real.sin (θ k) =
          Real.sin (θ (i + 1) - θ k) * Real.sin (θ i) +
          Real.sin (θ k - θ i) * Real.sin (θ (i + 1)) := by
        rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring
      have hb_i : bF (seq i) = rF i * Real.sin (θ i) := hcs_i.2.2
      have hb_i1 : bF (seq (i + 1)) = rF (i + 1) * Real.sin (θ (i + 1)) := hcs_i1.2.2
      have hb_k : bF (seq k) = rF k * Real.sin (θ k) := hcs_k.2.2
      have hden_ne : Real.sin (δ i) ≠ 0 := hsin_δ_pos.ne'
      calc bF (seq k)
          = rF k * Real.sin (θ k) := hb_k
        _ = (rF k / Real.sin (δ i)) * (Real.sin (θ (i + 1) - θ i) * Real.sin (θ k)) := by
            rw [hsin_δ_eq i]; field_simp [hden_ne]
        _ = (rF k / Real.sin (δ i)) * (Real.sin (θ (i + 1) - θ k) * Real.sin (θ i) +
              Real.sin (θ k - θ i) * Real.sin (θ (i + 1))) := by rw [hid]
        _ = (rF k / Real.sin (δ i)) * (Real.sin (δ i - φ) * Real.sin (θ i) +
              Real.sin φ * Real.sin (θ (i + 1))) := by rw [hsin_δφ, hsin_φ]
        _ = M₁ * (rF i * Real.sin (θ i)) + M₂ * (rF (i + 1) * Real.sin (θ (i + 1))) := by
            dsimp [M₁, M₂]; field_simp [(hrF_pos i).ne', (hrF_pos (i + 1)).ne', hden_ne]
        _ = M₁ * bF (seq i) + M₂ * bF (seq (i + 1)) := by rw [← hb_i, ← hb_i1]
    have haff : ∀ q : ℝ × ℝ,
        linForm (seq k) q = linForm (seq k) (qV i) +
          M₁ * linForm (seq i) q + M₂ * linForm (seq (i + 1)) q := by
      intro q
      have h0i := (hqV_zero i).1
      have h0i1 := (hqV_zero i).2
      dsimp [linForm] at h0i h0i1 ⊢
      rw [ha_comb, hb_comb]
      linear_combination -M₁ * h0i - M₂ * h0i1
    by_cases hφ1 : φ < Real.pi
    · have hsin_neg1 : Real.sin (δ i - φ) < 0 := by
        rw [← neg_neg (δ i - φ), Real.sin_neg, neg_lt_zero]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hδ_pos i])
      have hM₁_neg : M₁ < 0 := by
        dsimp [M₁]
        exact mul_neg_of_pos_of_neg (div_pos (hrF_pos k) (hrF_pos i))
          (div_neg_of_neg_of_pos hsin_neg1 hsin_δ_pos)
      have hp1_k : 0 < linForm (seq k) (pF ⟨seq (i + 1), hseq_mem (i + 1)⟩) :=
        hpF_pos ⟨seq (i + 1), hseq_mem (i + 1)⟩ (seq k) (hseq_mem k) (fun h => hki1 (hseq_inj h))
      have hp1_i : 0 < linForm (seq i) (pF ⟨seq (i + 1), hseq_mem (i + 1)⟩) :=
        hpF_pos ⟨seq (i + 1), hseq_mem (i + 1)⟩ (seq i) (hseq_mem i)
          (fun h => fin_succ_ne_self hS_card i (hseq_inj h.symm))
      have hp1_i1 : linForm (seq (i + 1)) (pF ⟨seq (i + 1), hseq_mem (i + 1)⟩) = 0 :=
        hpF_zero ⟨seq (i + 1), hseq_mem (i + 1)⟩
      have hsub := haff (pF ⟨seq (i + 1), hseq_mem (i + 1)⟩)
      rw [hp1_i1, mul_zero, add_zero] at hsub
      exact affine_pos_case1 hp1_k hp1_i hM₁_neg hsub
    · push_neg at hφ1
      by_cases hφ2 : φ ≤ Real.pi + δ i
      · have hsin_le1 : Real.sin (δ i - φ) ≤ 0 := by
          rw [← neg_neg (δ i - φ), Real.sin_neg, neg_nonpos]
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hδ_lt_pi i]) (by linarith)
        have hsin_le2 : Real.sin φ ≤ 0 := by
          rw [← neg_neg (Real.sin φ), neg_nonpos, ← Real.sin_sub_pi]
          exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hδ_lt_pi i])
        have hM₁_le : M₁ ≤ 0 := by
          dsimp [M₁]
          exact mul_nonpos_of_nonneg_of_nonpos (div_pos (hrF_pos k) (hrF_pos i)).le
            (div_nonpos_of_nonpos_of_nonneg hsin_le1 hsin_δ_pos.le)
        have hM₂_le : M₂ ≤ 0 := by
          dsimp [M₂]
          exact mul_nonpos_of_nonneg_of_nonpos (div_pos (hrF_pos k) (hrF_pos (i + 1))).le
            (div_nonpos_of_nonpos_of_nonneg hsin_le2 hsin_δ_pos.le)
        have hq_k := hq₀_pos (seq k) (hseq_mem k)
        have hq_i := hq₀_pos (seq i) (hseq_mem i)
        have hq_i1 := hq₀_pos (seq (i + 1)) (hseq_mem (i + 1))
        have hsub := haff q₀
        exact affine_pos_case2 hq_k hq_i hq_i1 hM₁_le hM₂_le hsub
      · push_neg at hφ2
        have hsin_neg2 : Real.sin φ < 0 := by
          rw [← neg_neg (Real.sin φ), neg_lt_zero, ← Real.sin_sub_pi]
          exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hδ_pos i]) (by linarith)
        have hM₂_neg : M₂ < 0 := by
          dsimp [M₂]
          exact mul_neg_of_pos_of_neg (div_pos (hrF_pos k) (hrF_pos (i + 1)))
            (div_neg_of_neg_of_pos hsin_neg2 hsin_δ_pos)
        have hp_k := hpF_pos ⟨seq i, hseq_mem i⟩ (seq k) (hseq_mem k) (fun h => hki (hseq_inj h))
        have hp_i := hpF_zero ⟨seq i, hseq_mem i⟩
        have hp_i1 : 0 < linForm (seq (i + 1)) (pF ⟨seq i, hseq_mem i⟩) :=
          hpF_pos ⟨seq i, hseq_mem i⟩ (seq (i + 1)) (hseq_mem (i + 1))
            (fun h => fin_succ_ne_self hS_card i (hseq_inj h))
        have hsub := haff (pF ⟨seq i, hseq_mem i⟩)
        rw [hp_i, mul_zero, add_zero] at hsub
        exact affine_pos_case3 hp_k hp_i1 hM₂_neg hsub
  let Vtilde : Fin S.card → E3 := fun i => (w₀ : E3) + (qV i).1 • e₁ + (qV i).2 • e₂
  have hVt_w : ∀ i, inner ℝ (w₀ : E3) (Vtilde i) = 1 := by
    intro i
    simp [Vtilde, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hw0_norm, hwo_e1, hwo_e2]
  have hVt_ne : ∀ i, Vtilde i ≠ 0 := by
    intro i h0
    have h1 := hVt_w i
    rw [h0, inner_zero_right] at h1
    norm_num at h1
  let V : Fin S.card → ↑(Metric.sphere (0 : E3) 1) := fun i =>
    ⟨‖Vtilde i‖⁻¹ • Vtilde i,
      by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hVt_ne i))]⟩
  have hinner_V : ∀ i (s : ↑(Metric.sphere (0 : E3) 1)),
      inner ℝ (s : E3) (V i : E3) = ‖Vtilde i‖⁻¹ * linForm s (qV i) := by
    intro i s
    change inner ℝ (s : E3) (‖Vtilde i‖⁻¹ • Vtilde i) = _
    rw [inner_smul_right]
    congr 1
    simp [Vtilde, linForm, cF, aF, bF, inner_add_right, inner_smul_right]
    ring
  refine ⟨seq, V, hseq_mem, hseq_inj, hseq_surj, ?_, ?_, ?_, ?_⟩
  · intro i k
    rw [hinner_V i (seq k)]
    refine mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ?_
    by_cases h1 : k = i
    · rw [h1, (hqV_zero i).1]
    · by_cases h2 : k = i + 1
      · rw [h2, (hqV_zero i).2]
      · exact (hqV_pos i k h1 h2).le
  · intro i
    rw [hinner_V i (seq i), hinner_V i (seq (i + 1)), (hqV_zero i).1, (hqV_zero i).2, mul_zero]
    exact ⟨rfl, rfl⟩
  · intro i k hki hki1
    rw [hinner_V i (seq k)]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hVt_ne i))) (hqV_pos i k hki hki1)
  · intro i
    change 0 < inner ℝ (w₀ : E3) (‖Vtilde i‖⁻¹ • Vtilde i)
    rw [inner_smul_right, hVt_w i, mul_one]
    exact inv_pos.mpr (norm_pos_iff.mpr (hVt_ne i))

private lemma measure_facet_eq_two_faceScale_mul_arccos
    {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    {b : Fin 4 → E4} (hb : Orthonormal ℝ b)
    (V_E4 : Finset ↑(Metric.sphere (0 : E4) 1))
    (seq V : Fin m → ↑(Metric.sphere (0 : E3) 1))
    (hcone_iff : ∀ x : E4, (∀ k : Fin m, 0 ≤ inner ℝ (embE3 b (seq k : E3)) x) ↔
      (∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x))
    (hV_nonneg : ∀ i k : Fin m, 0 ≤ inner ℝ (seq k : E3) (V i : E3))
    (hV_zero : ∀ i : Fin m, inner ℝ (seq i : E3) (V i : E3) = 0 ∧
      inner ℝ (seq (i + 1) : E3) (V i : E3) = 0)
    (hV_pos : ∀ i k : Fin m, k ≠ i → k ≠ i + 1 → 0 < inner ℝ (seq k : E3) (V i : E3)) :
    ∀ i : Fin m,
      measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ (embE3 b (seq i : E3)) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x} =
        2 * faceScale * Real.arccos (inner ℝ (V (i - 1) : E3) (V i : E3)) := by
  intro i
  have h1val : ((1 : Fin m) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < m)
  have h1_ne_0 : (1 : Fin m) ≠ 0 := fun h => by
    have hv := congrArg Fin.val h
    rw [h1val, Fin.val_zero] at hv
    exact one_ne_zero hv
  have h2_ne_0 : (1 : Fin m) + 1 ≠ 0 := fun h => by
    have hv := congrArg Fin.val h
    rw [Fin.val_add, h1val, Nat.mod_eq_of_lt (by omega : 1 + 1 < m), Fin.val_zero] at hv
    exact (by decide : 1 + 1 ≠ 0) hv
  have h1m : i - 1 ≠ i := fun h => h1_ne_0 <| by
    calc (1 : Fin m) = i - (i - 1) := by abel
      _ = i - i := by rw [h]
      _ = 0 := sub_self i
  have h1p1 : i - 1 ≠ i + 1 := fun h => h2_ne_0 <| by
    calc (1 : Fin m) + 1 = (i + 1) - (i - 1) := by abel
      _ = (i + 1) - (i + 1) := by rw [← h]
      _ = 0 := sub_self _
  have him1_succ : (i - 1) + 1 = i := by abel
  let Vp : E3 := (V (i - 1) : E3)
  let Vc : E3 := (V i : E3)
  have hVp_si : inner ℝ (seq i : E3) Vp = 0 := by rw [← him1_succ]; exact (hV_zero (i - 1)).2
  have hVp_sim1 : inner ℝ (seq (i - 1) : E3) Vp = 0 := (hV_zero (i - 1)).1
  have hVp_sip1 : 0 < inner ℝ (seq (i + 1) : E3) Vp := by
    refine hV_pos (i - 1) (i + 1) h1p1.symm (by rw [him1_succ]; exact fin_succ_ne_self hm i)
  have hVc_si : inner ℝ (seq i : E3) Vc = 0 := (hV_zero i).1
  have hVc_sip1 : inner ℝ (seq (i + 1) : E3) Vc = 0 := (hV_zero i).2
  have hVc_sim1 : 0 < inner ℝ (seq (i - 1) : E3) Vc :=
    hV_pos i (i - 1) h1m h1p1
  have hsi_norm : ‖(seq i : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp (seq i).2
  have hVp_norm : ‖Vp‖ = 1 := mem_sphere_zero_iff_norm.mp (V (i - 1)).2
  have hVc_norm : ‖Vc‖ = 1 := mem_sphere_zero_iff_norm.mp (V i).2
  let pm : E3 := (seq (i - 1) : E3) - inner ℝ (seq i : E3) (seq (i - 1) : E3) • (seq i : E3)
  let pp : E3 := (seq (i + 1) : E3) - inner ℝ (seq i : E3) (seq (i + 1) : E3) • (seq i : E3)
  have hpm_Vc : inner ℝ pm Vc = inner ℝ (seq (i - 1) : E3) Vc := by
    simp [pm, inner_sub_left, inner_smul_left, hVc_si]
  have hpp_Vp : inner ℝ pp Vp = inner ℝ (seq (i + 1) : E3) Vp := by
    simp [pp, inner_sub_left, inner_smul_left, hVp_si]
  have hpm_ne : pm ≠ 0 := fun h => by
    have := hpm_Vc; rw [h, inner_zero_left] at this; linarith
  have hpp_ne : pp ≠ 0 := fun h => by
    have := hpp_Vp; rw [h, inner_zero_left] at this; linarith
  let nm : E3 := ‖pm‖⁻¹ • pm
  let np : E3 := ‖pp‖⁻¹ • pp
  have hnm_norm : ‖nm‖ = 1 := by simp [nm, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpm_ne)]
  have hnp_norm : ‖np‖ = 1 := by simp [np, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpp_ne)]
  have hnm_si : inner ℝ (seq i : E3) nm = 0 := by
    simp [nm, pm, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hsi_norm]
  have hnp_si : inner ℝ (seq i : E3) np = 0 := by
    simp [np, pp, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hsi_norm]
  have hnm_Vp : inner ℝ nm Vp = 0 := by
    simp [nm, pm, inner_smul_left, inner_sub_left, hVp_sim1, hVp_si]
  have hnp_Vc : inner ℝ np Vc = 0 := by
    simp [np, pp, inner_smul_left, inner_sub_left, hVc_sip1, hVc_si]
  have hnm_Vc_pos : 0 < inner ℝ nm Vc := by
    change 0 < inner ℝ (‖pm‖⁻¹ • pm) Vc
    rw [inner_smul_left, hpm_Vc]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hpm_ne)) hVc_sim1
  have hnp_Vp_pos : 0 < inner ℝ np Vp := by
    change 0 < inner ℝ (‖pp‖⁻¹ • pp) Vp
    rw [inner_smul_left, hpp_Vp]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hpp_ne)) hVp_sip1
  have hsi_Vp : inner ℝ (seq i : E3) Vp = 0 := hVp_si
  have hsi_nm : inner ℝ (seq i : E3) nm = 0 := hnm_si
  have hVp_nm : inner ℝ Vp nm = 0 := by rw [real_inner_comm]; exact hnm_Vp
  have hinner_nm_np : -inner ℝ nm np = inner ℝ Vp Vc := by
    have hVc_eq := orthonormal_E3_inner hsi_norm hVp_norm hnm_norm hsi_Vp hsi_nm hVp_nm
    have hVc_sq : inner ℝ (seq i : E3) Vc ^ 2 + inner ℝ Vp Vc ^ 2 + inner ℝ nm Vc ^ 2 = 1 := by
      calc inner ℝ (seq i : E3) Vc ^ 2 + inner ℝ Vp Vc ^ 2 + inner ℝ nm Vc ^ 2
          = inner ℝ Vc (seq i : E3) * inner ℝ (seq i : E3) Vc +
            inner ℝ Vc Vp * inner ℝ Vp Vc + inner ℝ Vc nm * inner ℝ nm Vc := by
              rw [real_inner_comm Vc (seq i : E3), real_inner_comm Vc Vp, real_inner_comm Vc nm]; ring
        _ = 1 := by rw [← hVc_eq Vc Vc, real_inner_self_eq_norm_sq, hVc_norm, one_pow]
    have hab : inner ℝ Vp Vc ^ 2 + inner ℝ nm Vc ^ 2 = 1 := by
      rw [hVc_si] at hVc_sq; linarith
    have hnp_sq : inner ℝ (seq i : E3) np ^ 2 + inner ℝ Vp np ^ 2 + inner ℝ nm np ^ 2 = 1 := by
      calc inner ℝ (seq i : E3) np ^ 2 + inner ℝ Vp np ^ 2 + inner ℝ nm np ^ 2
          = inner ℝ np (seq i : E3) * inner ℝ (seq i : E3) np +
            inner ℝ np Vp * inner ℝ Vp np + inner ℝ np nm * inner ℝ nm np := by
              rw [real_inner_comm np (seq i : E3), real_inner_comm np Vp, real_inner_comm np nm]; ring
        _ = 1 := by rw [← hVc_eq np np, real_inner_self_eq_norm_sq, hnp_norm, one_pow]
    have hcs : inner ℝ Vp np ^ 2 + inner ℝ nm np ^ 2 = 1 := by
      rw [hnp_si] at hnp_sq; linarith
    have hdot : inner ℝ Vp Vc * inner ℝ Vp np + inner ℝ nm Vc * inner ℝ nm np = 0 := by
      have h1 := hVc_eq Vc np
      have hc1 : inner ℝ Vc (seq i : E3) = 0 := by rw [real_inner_comm]; exact hVc_si
      have hc2 : inner ℝ Vc np = 0 := by rw [real_inner_comm]; exact hnp_Vc
      have hc3 : inner ℝ Vc Vp = inner ℝ Vp Vc := real_inner_comm _ _
      have hc4 : inner ℝ Vc nm = inner ℝ nm Vc := real_inner_comm _ _
      rw [hc1, hc2, hc3, hc4, zero_mul, zero_add] at h1
      exact h1.symm
    have hVpnp : inner ℝ Vp np = inner ℝ np Vp := real_inner_comm _ _
    rw [hVpnp] at hcs hdot
    have hdot' : inner ℝ np Vp * inner ℝ Vp Vc + inner ℝ nm np * inner ℝ nm Vc = 0 := by
      linarith [hdot]
    exact ortho_unit_angle_neg hnm_Vc_pos hnp_Vp_pos hab hcs hdot'
  have hfacet_eq : {x ∈ Metric.sphere (0 : E4) 1 |
      inner ℝ (embE3 b (seq i : E3)) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x} =
      {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ (embE3 b (seq i : E3)) x = 0 ∧
        0 ≤ inner ℝ (embE3 b nm) x ∧ 0 ≤ inner ℝ (embE3 b np) x} := by
    ext x
    refine and_congr_right fun _ => and_congr_right fun hxi => ?_
    set z : E3 := projE3 b x
    have hzi : inner ℝ (seq i : E3) z = 0 := by rwa [← inner_embE3_left]
    have hnm_z : 0 ≤ inner ℝ (embE3 b nm) x ↔ 0 ≤ inner ℝ (seq (i - 1) : E3) z := by
      rw [inner_embE3_left]
      have heq : inner ℝ nm z = ‖pm‖⁻¹ * inner ℝ (seq (i - 1) : E3) z := by
        simp [nm, pm, inner_smul_left, inner_sub_left, hzi]
      rw [heq]
      have hpos : 0 < ‖pm‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hpm_ne)
      exact ⟨fun h => nonneg_of_mul_nonneg_right h hpos, fun h => mul_nonneg hpos.le h⟩
    have hnp_z : 0 ≤ inner ℝ (embE3 b np) x ↔ 0 ≤ inner ℝ (seq (i + 1) : E3) z := by
      rw [inner_embE3_left]
      have heq : inner ℝ np z = ‖pp‖⁻¹ * inner ℝ (seq (i + 1) : E3) z := by
        simp [np, pp, inner_smul_left, inner_sub_left, hzi]
      rw [heq]
      have hpos : 0 < ‖pp‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hpp_ne)
      exact ⟨fun h => nonneg_of_mul_nonneg_right h hpos, fun h => mul_nonneg hpos.le h⟩
    rw [hnm_z, hnp_z, ← hcone_iff x]
    simp only [inner_embE3_left]
    constructor
    · intro hz
      exact ⟨hz (i - 1), hz (i + 1)⟩
    · rintro ⟨hz_m, hz_p⟩ k
      let c₂ : ℝ := inner ℝ nm z / inner ℝ nm Vc
      let c₁ : ℝ := inner ℝ Vp z - c₂ * inner ℝ Vp Vc
      have hz_decomp : z = c₁ • Vp + c₂ • Vc := by
        set diff := z - (c₁ • Vp + c₂ • Vc)
        have hsq0 : ‖diff‖ ^ 2 = 0 := by
          rw [← real_inner_self_eq_norm_sq,
            orthonormal_E3_inner hsi_norm hVp_norm hnm_norm hsi_Vp hsi_nm hVp_nm]
          have h1 : inner ℝ diff (seq i : E3) = 0 := by
            rw [real_inner_comm]; simp [diff, inner_sub_right, inner_add_right, inner_smul_right,
              hzi, hVp_si, hVc_si]
          have h2 : inner ℝ diff Vp = 0 := by
            rw [real_inner_comm]; simp only [diff, inner_sub_right, inner_add_right, inner_smul_right,
              real_inner_self_eq_norm_sq, hVp_norm, one_pow, mul_one]
            dsimp [c₁]; ring
          have h3 : inner ℝ diff nm = 0 := by
            rw [real_inner_comm]; simp only [diff, inner_sub_right, inner_add_right, inner_smul_right,
              hnm_Vp, mul_zero, zero_add]
            dsimp [c₂]; field_simp [hnm_Vc_pos.ne']; ring
          rw [h1, h2, h3]; ring
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0))
      have hc₂_nonneg : 0 ≤ c₂ := by
        have hid : inner ℝ (seq (i - 1) : E3) z = c₂ * inner ℝ (seq (i - 1) : E3) Vc := by
          rw [hz_decomp, inner_add_right, inner_smul_right, inner_smul_right, hVp_sim1, mul_zero, zero_add]
        rw [hid] at hz_m
        exact nonneg_of_mul_nonneg_left hz_m hVc_sim1
      have hc₁_nonneg : 0 ≤ c₁ := by
        have hid : inner ℝ (seq (i + 1) : E3) z = c₁ * inner ℝ (seq (i + 1) : E3) Vp := by
          rw [hz_decomp, inner_add_right, inner_smul_right, inner_smul_right, hVc_sip1, mul_zero, add_zero]
        rw [hid] at hz_p
        exact nonneg_of_mul_nonneg_left hz_p hVp_sip1
      change 0 ≤ inner ℝ (seq k : E3) z
      rw [hz_decomp, inner_add_right, inner_smul_right, inner_smul_right]
      exact add_nonneg (mul_nonneg hc₁_nonneg (hV_nonneg (i - 1) k)) (mul_nonneg hc₂_nonneg (hV_nonneg i k))
  rw [hfacet_eq, measure_two_suspension_arc
    (by rw [embE3_norm hb]; exact hsi_norm)
    (by rw [embE3_norm hb]; exact hnm_norm)
    (by rw [embE3_norm hb]; exact hnp_norm)
    (by rw [embE3_inner hb]; exact hnm_si)
    (by rw [embE3_inner hb]; exact hnp_si)]
  rw [embE3_inner hb, hinner_nm_np]

private lemma triSusp4_of_E3_triangle_eq_sphExcess
    {b : Fin 4 → E4} (hb : Orthonormal ℝ b)
    {w₀ w₁ w₂ V₀ V₁ V₂ : ↑(Metric.sphere (0 : E3) 1)}
    (hw00 : inner ℝ (w₀ : E3) (V₀ : E3) = 0)
    (hw01 : inner ℝ (w₀ : E3) (V₁ : E3) = 0)
    (hw02 : 0 < inner ℝ (w₀ : E3) (V₂ : E3))
    (hw11 : inner ℝ (w₁ : E3) (V₁ : E3) = 0)
    (hw12 : inner ℝ (w₁ : E3) (V₂ : E3) = 0)
    (hw10 : 0 < inner ℝ (w₁ : E3) (V₀ : E3))
    (hw22 : inner ℝ (w₂ : E3) (V₂ : E3) = 0)
    (hw20 : inner ℝ (w₂ : E3) (V₀ : E3) = 0)
    (hw21 : 0 < inner ℝ (w₂ : E3) (V₁ : E3)) :
    let d₀ := Real.arccos (inner ℝ (V₁ : E3) (V₂ : E3))
    let d₁ := Real.arccos (inner ℝ (V₂ : E3) (V₀ : E3))
    let d₂ := Real.arccos (inner ℝ (V₀ : E3) (V₁ : E3))
    let wE : Fin 3 → ↑(Metric.sphere (0 : E4) 1) := fun k =>
      ⟨embE3 b (![w₀, w₁, w₂] k : E3), by
        simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using (![w₀, w₁, w₂] k).2⟩
    0 < d₀ ∧ d₀ < Real.pi ∧ 0 < d₁ ∧ d₁ < Real.pi ∧ 0 < d₂ ∧ d₂ < Real.pi ∧
      d₀ < d₁ + d₂ ∧ d₁ < d₂ + d₀ ∧ d₂ < d₀ + d₁ ∧ d₀ + d₁ + d₂ < 2 * Real.pi ∧
      MeasureTheory.volume.toSphere.real (triSusp4 wE) =
        MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
          (4 * Real.pi) * sphExcess d₀ d₁ d₂ := by
  intro d₀ d₁ d₂ wE
  obtain ⟨hliV, _, hstd⟩ := stdTriArea_eq_sphExcess hw00 hw01 hw02 hw11 hw12 hw10 hw22 hw20 hw21
  have hdet : det3 (V₁ : E3) (V₂ : E3) (V₀ : E3) ≠ 0 := by
    have hli' : LinearIndependent ℝ ![(V₁ : E3), (V₂ : E3), (V₀ : E3)] := by
      have heq : ![(V₁ : E3), (V₂ : E3), (V₀ : E3)] =
          (fun j => ![(V₀ : E3), (V₁ : E3), (V₂ : E3)] ((![1, 2, 0] : Fin 3 → Fin 3) j)) := by
        ext j; fin_cases j <;> rfl
      rw [heq]
      exact hliV.comp (![1, 2, 0] : Fin 3 → Fin 3) (fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp_all)
    exact det3_ne_zero_of_linearIndependent hli'
  have htri := sphTriangleInequalities_of_det3_ne_zero
    (by simpa [Metric.mem_sphere, dist_zero_right] using V₁.2)
    (by simpa [Metric.mem_sphere, dist_zero_right] using V₂.2)
    (by simpa [Metric.mem_sphere, dist_zero_right] using V₀.2)
    hdet
  have hVdet2 : det3 (V₀ : E3) (V₁ : E3) (V₂ : E3) ≠ 0 :=
    det3_ne_zero_of_linearIndependent hliV
  have htri2 := sphTriangleInequalities_of_det3_ne_zero
    (by simpa [Metric.mem_sphere, dist_zero_right] using V₀.2)
    (by simpa [Metric.mem_sphere, dist_zero_right] using V₁.2)
    (by simpa [Metric.mem_sphere, dist_zero_right] using V₂.2)
    hVdet2
  rcases htri2 with ⟨hd0_pos, hd0_lt, hd1_pos, hd1_lt, hd2_pos, hd2_lt, h012, h120, h201, hsum⟩
  refine ⟨hd0_pos, hd0_lt, hd1_pos, hd1_lt, hd2_pos, hd2_lt, h012, h120, h201, hsum, ?_⟩
  rw [toSphere_real_triSusp4 wE]
  congr 1
  have h01 : inner ℝ (wE 0 : E4) (wE 1 : E4) = inner ℝ (w₀ : E3) (w₁ : E3) :=
    embE3_inner hb (w₀ : E3) (w₁ : E3)
  have h12 : inner ℝ (wE 1 : E4) (wE 2 : E4) = inner ℝ (w₁ : E3) (w₂ : E3) :=
    embE3_inner hb (w₁ : E3) (w₂ : E3)
  have h20 : inner ℝ (wE 2 : E4) (wE 0 : E4) = inner ℝ (w₂ : E3) (w₀ : E3) :=
    embE3_inner hb (w₂ : E3) (w₀ : E3)
  rw [h01, h12, h20]
  have hlune : stdTriArea ![w₀, w₁, w₂] =
      Real.arccos (-inner ℝ (w₀ : E3) (w₁ : E3)) +
      Real.arccos (-inner ℝ (w₁ : E3) (w₂ : E3)) +
      Real.arccos (-inner ℝ (w₂ : E3) (w₀ : E3)) - Real.pi := by
    simp [stdTriArea, luneAngle]
  rw [← hlune, hstd]

private lemma degenerate_limit_volume_three_case
    {b : Fin 4 → E4} (hb : Orthonormal ℝ b)
    (u : Fin 4 → ↑(Metric.sphere (0 : E4) 1))
    (V_E4 : Finset ↑(Metric.sphere (0 : E4) 1))
    (hV_E4 : V_E4 = Finset.image u Finset.univ)
    (seq V : Fin 3 → ↑(Metric.sphere (0 : E3) 1))
    (hcone_iff : ∀ x : E4, (∀ k : Fin 3, 0 ≤ inner ℝ (embE3 b (seq k : E3)) x) ↔
      (∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x))
    (hV_zero : ∀ i : Fin 3, inner ℝ (seq i : E3) (V i : E3) = 0 ∧
      inner ℝ (seq (i + 1) : E3) (V i : E3) = 0)
    (hV_pos : ∀ i k : Fin 3, k ≠ i → k ≠ i + 1 → 0 < inner ℝ (seq k : E3) (V i : E3))
    (totalStdArea : ℝ) (hA0 : 0 < totalStdArea) (hA4pi : totalStdArea < 4 * Real.pi)
    (hsum_d : ∑ i : Fin 3, Real.arccos (inner ℝ (V (i - 1) : E3) (V i : E3)) ≤ totalStdArea / 2) :
    measure 3 {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} ≤
      sphereScale 3 *
        (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
          (4 * Real.pi)) *
        (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) := by
  let B : Set E4 := {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
  have hB_sub : B ⊆ Metric.sphere 0 1 := fun _ hx => hx.1
  have hB_cl : IsClosed B := by
    refine Metric.isClosed_sphere.inter ?_
    have heq : {x : E4 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} =
        ⋂ i : Fin 4, {x : E4 | 0 ≤ inner ℝ (u i : E4) x} := by ext x; simp
    change IsClosed {x : E4 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_const : Continuous fun _ : E4 => (u i : E4)).inner continuous_id)
  have hm : measure 3 B =
      sphereScale 3 * MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' B) := by
    simpa [measure] using hausdorffMeasure_real_eq_scale_mul_toSphere (d := 3) (by decide) hB_sub
      hB_cl.measurableSet
  let w₀ := seq 1
  let w₁ := seq 2
  let w₂ := seq 0
  let V₀ := V 0
  let V₁ := V 1
  let V₂ := V 2
  have hw00 : inner ℝ (w₀ : E3) (V₀ : E3) = 0 := (hV_zero 0).2
  have hw01 : inner ℝ (w₀ : E3) (V₁ : E3) = 0 := (hV_zero 1).1
  have hw02 : 0 < inner ℝ (w₀ : E3) (V₂ : E3) := hV_pos 2 1 (by decide) (by decide)
  have hw11 : inner ℝ (w₁ : E3) (V₁ : E3) = 0 := (hV_zero 1).2
  have hw12 : inner ℝ (w₁ : E3) (V₂ : E3) = 0 := (hV_zero 2).1
  have hw10 : 0 < inner ℝ (w₁ : E3) (V₀ : E3) := hV_pos 0 2 (by decide) (by decide)
  have hw22 : inner ℝ (w₂ : E3) (V₂ : E3) = 0 := (hV_zero 2).2
  have hw20 : inner ℝ (w₂ : E3) (V₀ : E3) = 0 := (hV_zero 0).1
  have hw21 : 0 < inner ℝ (w₂ : E3) (V₁ : E3) := hV_pos 1 0 (by decide) (by decide)
  have htri := triSusp4_of_E3_triangle_eq_sphExcess hb hw00 hw01 hw02 hw11 hw12 hw10 hw22 hw20 hw21
  dsimp only at htri
  set d₀ := Real.arccos (inner ℝ (V₁ : E3) (V₂ : E3))
  set d₁ := Real.arccos (inner ℝ (V₂ : E3) (V₀ : E3))
  set d₂ := Real.arccos (inner ℝ (V₀ : E3) (V₁ : E3))
  let wE : Fin 3 → ↑(Metric.sphere (0 : E4) 1) := fun k =>
    ⟨embE3 b (![w₀, w₁, w₂] k : E3), by
      simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using (![w₀, w₁, w₂] k).2⟩
  rcases htri with ⟨hd0_pos, hd0_lt, hd1_pos, hd1_lt, hd2_pos, hd2_lt, h012, h120, h201, hsum_lt, htri_vol⟩
  have hpre_eq : (Subtype.val ⁻¹' B) = triSusp4 wE := by
    ext y
    simp only [Set.mem_preimage, B, Set.mem_setOf_eq, triSusp4]
    have hy1 : (y : E4) ∈ Metric.sphere (0 : E4) 1 := y.2
    have hiff := hcone_iff (y : E4)
    have hV_all : (∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) (y : E4)) ↔
        (∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) (y : E4)) := by
      rw [hV_E4]; simp
    have hk_all : (∀ k : Fin 3, 0 ≤ inner ℝ (embE3 b (seq k : E3)) (y : E4)) ↔
        (∀ k : Fin 3, 0 ≤ inner ℝ (wE k : E4) (y : E4)) := by
      constructor
      · intro h k; fin_cases k
        · exact h 1
        · exact h 2
        · exact h 0
      · intro h k; fin_cases k
        · exact h 2
        · exact h 0
        · exact h 1
    constructor
    · intro hy; exact hk_all.mp (hiff.mpr (hV_all.mp hy.2))
    · intro hy; exact ⟨hy1, hV_all.mpr (hiff.mp (hk_all.mpr hy))⟩
  rw [hm, hpre_eq, htri_vol]
  have hsum_d_eq : ∑ i : Fin 3, Real.arccos (inner ℝ (V (i - 1) : E3) (V i : E3)) = d₀ + d₁ + d₂ := by
    rw [Fin.sum_univ_three]
    have hm1 : (0 - 1 : Fin 3) = 2 := by decide
    have hm2 : (1 - 1 : Fin 3) = 0 := by decide
    have hm3 : (2 - 1 : Fin 3) = 1 := by decide
    rw [hm1, hm2, hm3]
    dsimp [d₀, d₁, d₂, V₀, V₁, V₂]
    ring
  have hd_sum_le : d₀ + d₁ + d₂ ≤ totalStdArea / 2 := hsum_d_eq ▸ hsum_d
  set m₁ := (d₀ + d₁) / 2
  set m₂ := d₂ / 2
  have hiso1 : sphExcess d₀ d₁ d₂ ≤ sphExcess m₁ m₁ d₂ :=
    sphExcess_le_isosceles hd0_pos hd0_lt hd1_pos hd1_lt hd2_pos hd2_lt h201 h012 h120 hsum_lt
  have hm1_lo : d₂ / 2 < m₁ := by dsimp [m₁]; linarith
  have hm1_hi : m₁ < Real.pi - d₂ / 2 := by dsimp [m₁]; linarith
  have hm2_lo : d₂ / 2 ≤ m₂ := le_rfl
  have hm2_hi : m₂ < Real.pi - d₂ / 2 := by dsimp [m₂]; linarith
  have hm12_sum : m₁ + m₂ < Real.pi := by dsimp [m₁, m₂]; linarith
  have hkite_res := sphExcess_kite_half hd2_pos hd2_lt hm1_lo hm1_hi hm2_lo hm2_hi hm12_sum
  dsimp only at hkite_res
  set d' := Real.arccos (Real.cos m₁ / Real.cos (d₂ / 2)) +
    Real.arccos (Real.cos m₂ / Real.cos (d₂ / 2))
  rcases hkite_res with ⟨hd'_pos, hd'_lt, hd'_ub, hm1_tri, hm2_tri, hkite_sum, hkite_eq⟩
  have hif_zero : (if m₂ = d₂ / 2 then (0 : ℝ) else sphExcess m₂ m₂ d₂) = 0 :=
    if_pos rfl
  rw [hif_zero, add_zero] at hkite_eq
  have hm1_pos : 0 < m₁ := by linarith
  have hm1_lt : m₁ < Real.pi := by dsimp [m₁]; linarith
  have hm2_pos : 0 < m₂ := by dsimp [m₂]; linarith
  have hm2_lt : m₂ < Real.pi := by dsimp [m₂]; linarith
  have hiso2 : sphExcess m₁ m₂ d' ≤ sphExcess ((m₁ + m₂) / 2) ((m₁ + m₂) / 2) d' :=
    sphExcess_le_isosceles hm1_pos hm1_lt hm2_pos hm2_lt hd'_pos hd'_lt
      hd'_ub hm1_tri hm2_tri hkite_sum
  set M := (m₁ + m₂) / 2
  have hM_pos : 0 < M := by dsimp [M]; linarith
  have hM_le : M ≤ totalStdArea / 8 := by dsimp [M, m₁, m₂]; linarith
  have hM_lt : M < Real.pi / 2 := by linarith
  have hd'_lt2M : d' < 2 * M := by dsimp [M]; linarith
  have hsq1 := sphExcess_isosceles_le_square hM_pos hM_lt hd'_pos hd'_lt2M
  have hsq2 := sphSquare_area_mono hM_pos.le hM_le (by linarith)
  rw [show totalStdArea / 8 / 2 = totalStdArea / 16 by ring] at hsq2
  have hexcess_le : sphExcess d₀ d₁ d₂ ≤
      4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi := by
    linarith [hiso1, hkite_eq, hiso2, hsq1, hsq2]
  have hscale_nonneg : 0 ≤ sphereScale 3 *
      (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi)) := by
    have hss := (sphereScale_pos (d := 3) (by decide)).le
    have huniv : 0 ≤ MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) :=
      ENNReal.toReal_nonneg
    positivity
  calc sphereScale 3 *
        (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
          (4 * Real.pi) * sphExcess d₀ d₁ d₂)
      = (sphereScale 3 *
          (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi))) * sphExcess d₀ d₁ d₂ := by ring
    _ ≤ (sphereScale 3 *
          (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi))) * (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) :=
        mul_le_mul_of_nonneg_left hexcess_le hscale_nonneg

private lemma degenerate_limit_volume_four_case
    {b : Fin 4 → E4} (hb : Orthonormal ℝ b)
    (u : Fin 4 → ↑(Metric.sphere (0 : E4) 1))
    (V_E4 : Finset ↑(Metric.sphere (0 : E4) 1))
    (hV_E4 : V_E4 = Finset.image u Finset.univ)
    (seq V : Fin 4 → ↑(Metric.sphere (0 : E3) 1))
    (hcone_iff : ∀ x : E4, (∀ k : Fin 4, 0 ≤ inner ℝ (embE3 b (seq k : E3)) x) ↔
      (∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x))
    (hV_nonneg : ∀ i k : Fin 4, 0 ≤ inner ℝ (seq k : E3) (V i : E3))
    (hV_zero : ∀ i : Fin 4, inner ℝ (seq i : E3) (V i : E3) = 0 ∧
      inner ℝ (seq (i + 1) : E3) (V i : E3) = 0)
    (hV_pos : ∀ i k : Fin 4, k ≠ i → k ≠ i + 1 → 0 < inner ℝ (seq k : E3) (V i : E3))
    (totalStdArea : ℝ) (hA0 : 0 < totalStdArea) (hA4pi : totalStdArea < 4 * Real.pi)
    (hsum_d : ∑ i : Fin 4, Real.arccos (inner ℝ (V (i - 1) : E3) (V i : E3)) ≤ totalStdArea / 2) :
    measure 3 {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} ≤
      sphereScale 3 *
        (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
          (4 * Real.pi)) *
        (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) := by
  let B : Set E4 := {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
  have hB_sub : B ⊆ Metric.sphere 0 1 := fun _ hx => hx.1
  have hB_cl : IsClosed B := by
    refine Metric.isClosed_sphere.inter ?_
    have heq : {x : E4 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} =
        ⋂ i : Fin 4, {x : E4 | 0 ≤ inner ℝ (u i : E4) x} := by ext x; simp
    change IsClosed {x : E4 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_const : Continuous fun _ : E4 => (u i : E4)).inner continuous_id)
  have hm : measure 3 B =
      sphereScale 3 * MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' B) := by
    simpa [measure] using hausdorffMeasure_real_eq_scale_mul_toSphere (d := 3) (by decide) hB_sub
      hB_cl.measurableSet
  have hV0_s2 : 0 < inner ℝ (seq 2 : E3) (V 0 : E3) := hV_pos 0 2 (by decide) (by decide)
  have hV1_s3 : 0 < inner ℝ (seq 3 : E3) (V 1 : E3) := hV_pos 1 3 (by decide) (by decide)
  have hV2_s0 : 0 < inner ℝ (seq 0 : E3) (V 2 : E3) := hV_pos 2 0 (by decide) (by decide)
  have hV2_s1 : 0 < inner ℝ (seq 1 : E3) (V 2 : E3) := hV_pos 2 1 (by decide) (by decide)
  have hV3_s1 : 0 < inner ℝ (seq 1 : E3) (V 3 : E3) := hV_pos 3 1 (by decide) (by decide)
  have hV3_s2 : 0 < inner ℝ (seq 2 : E3) (V 3 : E3) := hV_pos 3 2 (by decide) (by decide)
  have hV0_s3 : 0 < inner ℝ (seq 3 : E3) (V 0 : E3) := hV_pos 0 3 (by decide) (by decide)
  have hV1_s0 : 0 < inner ℝ (seq 0 : E3) (V 1 : E3) := hV_pos 1 0 (by decide) (by decide)
  have hli012 : LinearIndependent ℝ ![(V 0 : E3), (V 1 : E3), (V 2 : E3)] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hc2 : inner ℝ (seq 1 : E3) (∑ i : Fin 3, c i • ![(V 0 : E3), (V 1 : E3), (V 2 : E3)] i) = 0 := by
      rw [hc, inner_zero_right]
    rw [Fin.sum_univ_three, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right] at hc2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc2
    have h0 : inner ℝ (seq 1 : E3) (V 0 : E3) = 0 := (hV_zero 0).2
    have h1 : inner ℝ (seq 1 : E3) (V 1 : E3) = 0 := (hV_zero 1).1
    rw [h0, h1, mul_zero, mul_zero, zero_add, zero_add] at hc2
    have hc2_eq : c 2 = 0 := (mul_eq_zero.mp hc2).resolve_right hV2_s1.ne'
    have hc0_in : inner ℝ (seq 2 : E3) (∑ i : Fin 3, c i • ![(V 0 : E3), (V 1 : E3), (V 2 : E3)] i) = 0 := by
      rw [hc, inner_zero_right]
    rw [Fin.sum_univ_three, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right] at hc0_in
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc0_in
    have h1' : inner ℝ (seq 2 : E3) (V 1 : E3) = 0 := (hV_zero 1).2
    have h2' : inner ℝ (seq 2 : E3) (V 2 : E3) = 0 := (hV_zero 2).1
    rw [h1', h2', mul_zero, mul_zero, add_zero, add_zero] at hc0_in
    have hc0_eq : c 0 = 0 := (mul_eq_zero.mp hc0_in).resolve_right hV0_s2.ne'
    rw [Fin.sum_univ_three, hc0_eq, hc2_eq, zero_smul, zero_smul, zero_add, add_zero] at hc
    have hc1_eq : c 1 = 0 := by
      have hV1_ne : (V 1 : E3) ≠ 0 := by
        intro hz; have := (V 1).2; simp [Metric.mem_sphere, hz] at this
      exact (smul_eq_zero.mp hc).resolve_right hV1_ne
    fin_cases j <;> assumption
  have hdet012 : det3 (V 0 : E3) (V 1 : E3) (V 2 : E3) ≠ 0 :=
    det3_ne_zero_of_linearIndependent hli012
  let diag : E3 := cross3 (V 0 : E3) (V 2 : E3)
  have hdiag_0 : inner ℝ (V 0 : E3) diag = 0 := inner_left_cross3 _ _
  have hdiag_2 : inner ℝ (V 2 : E3) diag = 0 := inner_right_cross3 _ _
  have hdiag_1 : inner ℝ (V 1 : E3) diag ≠ 0 := by
    have heq : inner ℝ (V 1 : E3) diag = det3 (V 1 : E3) (V 0 : E3) (V 2 : E3) := rfl
    rw [heq, show det3 (V 1 : E3) (V 0 : E3) (V 2 : E3) = -det3 (V 0 : E3) (V 1 : E3) (V 2 : E3) by
      rw [det3_cyclic, det3_swap_23, det3_cyclic, det3_cyclic]]
    exact neg_ne_zero.mpr hdet012
  have hdiag_ne : diag ≠ 0 := fun h => by
    have := hdiag_1; rw [h, inner_zero_right] at this; exact this rfl
  have hdiag_norm_pos : 0 < ‖diag‖ := norm_pos_iff.mpr hdiag_ne
  let n_diag : ↑(Metric.sphere (0 : E3) 1) :=
    if 0 < inner ℝ (V 1 : E3) diag then
      ⟨‖diag‖⁻¹ • diag, by simp [norm_smul, inv_mul_cancel₀ hdiag_norm_pos.ne']⟩
    else
      ⟨-(‖diag‖⁻¹ • diag), by simp [norm_smul, inv_mul_cancel₀ hdiag_norm_pos.ne']⟩
  let n_diag' : ↑(Metric.sphere (0 : E3) 1) :=
    ⟨-(n_diag : E3), by simpa [Metric.mem_sphere, dist_zero_right] using n_diag.2⟩
  have hnd_0 : inner ℝ (n_diag : E3) (V 0 : E3) = 0 := by
    rw [real_inner_comm]
    dsimp [n_diag]
    split_ifs <;> simp [inner_smul_right, inner_neg_right, hdiag_0]
  have hnd_2 : inner ℝ (n_diag : E3) (V 2 : E3) = 0 := by
    rw [real_inner_comm]
    dsimp [n_diag]
    split_ifs <;> simp [inner_smul_right, inner_neg_right, hdiag_2]
  have hnd_1 : 0 < inner ℝ (n_diag : E3) (V 1 : E3) := by
    rw [real_inner_comm]
    dsimp [n_diag]
    split_ifs with hp
    · simp only [inner_smul_right]
      exact mul_pos (inv_pos.mpr hdiag_norm_pos) hp
    · have hlt : inner ℝ (V 1 : E3) diag < 0 := lt_of_le_of_ne (not_lt.mp hp) hdiag_1
      simp only [inner_neg_right, inner_smul_right]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg (inv_pos.mpr hdiag_norm_pos) hlt)
  have hnd'_0 : inner ℝ (n_diag' : E3) (V 0 : E3) = 0 := by
    simp [n_diag', inner_neg_left, hnd_0]
  have hnd'_2 : inner ℝ (n_diag' : E3) (V 2 : E3) = 0 := by
    simp [n_diag', inner_neg_left, hnd_2]
  have hnd'_3 : 0 < inner ℝ (n_diag' : E3) (V 3 : E3) := by
    have hdecomp := det3_decomp (V 0 : E3) (V 1 : E3) (V 2 : E3) (V 3 : E3)
    set d := det3 (V 0 : E3) (V 1 : E3) (V 2 : E3)
    set c₀ := det3 (V 3 : E3) (V 1 : E3) (V 2 : E3) / d
    set c₁ := det3 (V 0 : E3) (V 3 : E3) (V 2 : E3) / d
    set c₂ := det3 (V 0 : E3) (V 1 : E3) (V 3 : E3) / d
    have hV3_eq : (V 3 : E3) = c₀ • (V 0 : E3) + c₁ • (V 1 : E3) + c₂ • (V 2 : E3) := by
      refine smul_right_injective E3 hdet012 ?_
      dsimp only
      rw [hdecomp, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
      simp only [c₀, c₁, c₂, mul_div_cancel₀ _ hdet012]
    have hs1 : inner ℝ (seq 1 : E3) (V 3 : E3) = c₂ * inner ℝ (seq 1 : E3) (V 2 : E3) := by
      have h10 : inner ℝ (seq 1 : E3) (V 0 : E3) = 0 := (hV_zero 0).2
      have h11 : inner ℝ (seq 1 : E3) (V 1 : E3) = 0 := (hV_zero 1).1
      rw [hV3_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right, h10, h11, mul_zero, mul_zero, zero_add, zero_add]
    have hc₂_pos : 0 < c₂ := by
      have : 0 < c₂ * inner ℝ (seq 1 : E3) (V 2 : E3) := hs1 ▸ hV3_s1
      exact pos_of_mul_pos_left this hV2_s1.le
    have hs0 : inner ℝ (seq 0 : E3) (V 3 : E3) =
        c₁ * inner ℝ (seq 0 : E3) (V 1 : E3) + c₂ * inner ℝ (seq 0 : E3) (V 2 : E3) := by
      rw [hV3_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right, (hV_zero 0).1, mul_zero, zero_add]
    have hs0_0 : inner ℝ (seq 0 : E3) (V 3 : E3) = 0 := (hV_zero 3).2
    have hc₁_neg : c₁ < 0 := by
      nlinarith [hs0_0, hs0, hc₂_pos, hV1_s0, hV2_s0]
    have hnd_3 : inner ℝ (n_diag : E3) (V 3 : E3) = c₁ * inner ℝ (n_diag : E3) (V 1 : E3) := by
      rw [hV3_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right, hnd_0, hnd_2, mul_zero, mul_zero, zero_add, add_zero]
    have hneg : inner ℝ (n_diag : E3) (V 3 : E3) < 0 := by nlinarith
    simp [n_diag', inner_neg_left, hneg]
  let wE₁ : Fin 3 → ↑(Metric.sphere (0 : E4) 1) := fun k =>
    ⟨embE3 b (![seq 1, seq 2, n_diag] k : E3), by
      simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using (![seq 1, seq 2, n_diag] k).2⟩
  let wE₂ : Fin 3 → ↑(Metric.sphere (0 : E4) 1) := fun k =>
    ⟨embE3 b (![seq 3, seq 0, n_diag'] k : E3), by
      simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using (![seq 3, seq 0, n_diag'] k).2⟩
  have hpre_eq : (Subtype.val ⁻¹' B) = triSusp4 wE₁ ∪ triSusp4 wE₂ := by
    ext y
    simp only [Set.mem_preimage, B, Set.mem_setOf_eq, Set.mem_union, triSusp4]
    have hy1 : (y : E4) ∈ Metric.sphere (0 : E4) 1 := y.2
    have hV_all : (∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) (y : E4)) ↔
        (∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) (y : E4)) := by
      rw [hV_E4]; simp
    have hiff := hcone_iff (y : E4)
    have hpos_decomp : ∀ (w₀ w₁ w₂ V₀ V₁ V₂ : ↑(Metric.sphere (0 : E3) 1)),
        inner ℝ (w₀ : E3) (V₀ : E3) = 0 → inner ℝ (w₀ : E3) (V₁ : E3) = 0 →
        0 < inner ℝ (w₀ : E3) (V₂ : E3) →
        inner ℝ (w₁ : E3) (V₁ : E3) = 0 → inner ℝ (w₁ : E3) (V₂ : E3) = 0 →
        0 < inner ℝ (w₁ : E3) (V₀ : E3) →
        inner ℝ (w₂ : E3) (V₂ : E3) = 0 → inner ℝ (w₂ : E3) (V₀ : E3) = 0 →
        0 < inner ℝ (w₂ : E3) (V₁ : E3) →
        (∀ i : Fin 3, 0 ≤ inner ℝ (embE3 b (![w₀, w₁, w₂] i : E3)) (y : E4)) →
        (∀ k : Fin 4, 0 ≤ inner ℝ (seq k : E3) (V₀ : E3)) →
        (∀ k : Fin 4, 0 ≤ inner ℝ (seq k : E3) (V₁ : E3)) →
        (∀ k : Fin 4, 0 ≤ inner ℝ (seq k : E3) (V₂ : E3)) →
        (∀ k : Fin 4, 0 ≤ inner ℝ (embE3 b (seq k : E3)) (y : E4)) := by
      intro a₀ a₁ a₂ A₀ A₁ A₂ ha00 ha01 ha02 ha11 ha12 ha10 ha22 ha20 ha21 hyA hA0 hA1 hA2 k
      obtain ⟨hliA, _, _⟩ := stdTriArea_eq_sphExcess ha00 ha01 ha02 ha11 ha12 ha10 ha22 ha20 ha21
      have hdetA := det3_ne_zero_of_linearIndependent hliA
      set z := projE3 b (y : E4)
      have hdec := det3_decomp (A₀ : E3) (A₁ : E3) (A₂ : E3) z
      set dA := det3 (A₀ : E3) (A₁ : E3) (A₂ : E3)
      set α := det3 z (A₁ : E3) (A₂ : E3) / dA
      set β := det3 (A₀ : E3) z (A₂ : E3) / dA
      set γ := det3 (A₀ : E3) (A₁ : E3) z / dA
      have hz_eq : z = α • (A₀ : E3) + β • (A₁ : E3) + γ • (A₂ : E3) := by
        refine smul_right_injective E3 hdetA ?_
        dsimp only
        rw [hdec, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
        simp only [α, β, γ, mul_div_cancel₀ _ hdetA]
      have hza0 : 0 ≤ inner ℝ (a₀ : E3) z := by
        rw [← inner_embE3_left]; exact hyA 0
      have hza1 : 0 ≤ inner ℝ (a₁ : E3) z := by
        rw [← inner_embE3_left]; exact hyA 1
      have hza2 : 0 ≤ inner ℝ (a₂ : E3) z := by
        rw [← inner_embE3_left]; exact hyA 2
      have hγ : 0 ≤ γ := by
        have hid : inner ℝ (a₀ : E3) z = γ * inner ℝ (a₀ : E3) (A₂ : E3) := by
          rw [hz_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
            inner_smul_right, ha00, ha01, mul_zero, mul_zero, zero_add, zero_add]
        exact nonneg_of_mul_nonneg_left (hid ▸ hza0) ha02
      have hα : 0 ≤ α := by
        have hid : inner ℝ (a₁ : E3) z = α * inner ℝ (a₁ : E3) (A₀ : E3) := by
          rw [hz_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
            inner_smul_right, ha11, ha12, mul_zero, mul_zero, add_zero, add_zero]
        exact nonneg_of_mul_nonneg_left (hid ▸ hza1) ha10
      have hβ : 0 ≤ β := by
        have hid : inner ℝ (a₂ : E3) z = β * inner ℝ (a₂ : E3) (A₁ : E3) := by
          rw [hz_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
            inner_smul_right, ha20, ha22, mul_zero, mul_zero, zero_add, add_zero]
        exact nonneg_of_mul_nonneg_left (hid ▸ hza2) ha21
      rw [inner_embE3_left]
      change 0 ≤ inner ℝ (seq k : E3) z
      rw [hz_eq, inner_add_right, inner_add_right, inner_smul_right,
        inner_smul_right, inner_smul_right]
      exact add_nonneg (add_nonneg (mul_nonneg hα (hA0 k)) (mul_nonneg hβ (hA1 k)))
        (mul_nonneg hγ (hA2 k))
    constructor
    · intro hy
      have hk := hiff.mpr (hV_all.mp hy.2)
      by_cases hsign : 0 ≤ inner ℝ (embE3 b (n_diag : E3)) (y : E4)
      · left
        intro k; fin_cases k
        · exact hk 1
        · exact hk 2
        · exact hsign
      · right
        push_neg at hsign
        intro k; fin_cases k
        · exact hk 3
        · exact hk 0
        · change 0 ≤ inner ℝ (embE3 b (n_diag' : E3)) (y : E4)
          have hlin : embE3 b (n_diag' : E3) = -embE3 b (n_diag : E3) := by
            simp [n_diag', embE3]; module
          rw [hlin, inner_neg_left]
          linarith
    · rintro (hT1 | hT2)
      · refine ⟨hy1, hV_all.mpr (hiff.mp (hpos_decomp (seq 1) (seq 2) n_diag (V 0) (V 1) (V 2)
          (hV_zero 0).2 (hV_zero 1).1 hV2_s1 (hV_zero 1).2 (hV_zero 2).1 hV0_s2
          hnd_2 hnd_0 hnd_1 hT1 (hV_nonneg 0) (hV_nonneg 1) (hV_nonneg 2)))⟩
      · refine ⟨hy1, hV_all.mpr (hiff.mp (hpos_decomp (seq 3) (seq 0) n_diag' (V 2) (V 3) (V 0)
          (hV_zero 2).2 (hV_zero 3).1 hV0_s3 (hV_zero 3).2 (hV_zero 0).1 hV2_s0
          hnd'_0 hnd'_2 hnd'_3 hT2 (hV_nonneg 2) (hV_nonneg 3) (hV_nonneg 0)))⟩
  have hinter_null : MeasureTheory.volume.toSphere (triSusp4 wE₁ ∩ triSusp4 wE₂) = 0 := by
    have hsub : triSusp4 wE₁ ∩ triSusp4 wE₂ ⊆
        {z : ↑(Metric.sphere (0 : E4) 1) | inner ℝ (embE3 b (n_diag : E3)) (z : E4) = 0} := by
      intro z ⟨hz1, hz2⟩
      have h1 : 0 ≤ inner ℝ (embE3 b (n_diag : E3)) (z : E4) := hz1 2
      have h2 : 0 ≤ inner ℝ (embE3 b (n_diag' : E3)) (z : E4) := hz2 2
      have hlin : embE3 b (n_diag' : E3) = -embE3 b (n_diag : E3) := by
        simp [n_diag', embE3]; module
      rw [hlin, inner_neg_left] at h2
      exact le_antisymm (neg_nonneg.mp h2) h1
    have hne : embE3 b (n_diag : E3) ≠ 0 := by
      intro h0
      have : ‖(n_diag : E3)‖ = 0 := by rw [← embE3_norm hb, h0, norm_zero]
      have h1 : ‖(n_diag : E3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using n_diag.2
      linarith
    exact MeasureTheory.measure_mono_null hsub (toSphere_hyperplane_null _ hne)
  have hmunion : MeasureTheory.volume.toSphere.real (triSusp4 wE₁ ∪ triSusp4 wE₂) =
      MeasureTheory.volume.toSphere.real (triSusp4 wE₁) +
      MeasureTheory.volume.toSphere.real (triSusp4 wE₂) :=
    measureReal_union_inter_null _ (triSusp4_measurableSet _) (triSusp4_measurableSet _) hinter_null
  have htri1 := triSusp4_of_E3_triangle_eq_sphExcess hb (hV_zero 0).2 (hV_zero 1).1 hV2_s1
    (hV_zero 1).2 (hV_zero 2).1 hV0_s2 hnd_2 hnd_0 hnd_1
  have htri2 := triSusp4_of_E3_triangle_eq_sphExcess hb (hV_zero 2).2 (hV_zero 3).1 hV0_s3
    (hV_zero 3).2 (hV_zero 0).1 hV2_s0 hnd'_0 hnd'_2 hnd'_3
  dsimp only at htri1 htri2
  set d₁ := Real.arccos (inner ℝ (V 0 : E3) (V 1 : E3))
  set d₂ := Real.arccos (inner ℝ (V 1 : E3) (V 2 : E3))
  set d₃ := Real.arccos (inner ℝ (V 2 : E3) (V 3 : E3))
  set d₀ := Real.arccos (inner ℝ (V 3 : E3) (V 0 : E3))
  set d' := Real.arccos (inner ℝ (V 2 : E3) (V 0 : E3))
  have hd'_symm : Real.arccos (inner ℝ (V 0 : E3) (V 2 : E3)) = d' := by
    rw [real_inner_comm]
  rw [hd'_symm] at htri2
  rcases htri1 with ⟨hd2_pos, hd2_lt, hd'_pos, hd'_lt, hd1_pos, hd1_lt, ht1_a, ht1_b, ht1_c, ht1_s, hv1⟩
  rcases htri2 with ⟨hd0_pos, hd0_lt, _, _, hd3_pos, hd3_lt, ht2_a, ht2_b, ht2_c, ht2_s, hv2⟩
  have hwE1 : (fun k : Fin 3 => (⟨embE3 b (![seq (0 + 1), seq (1 + 1), n_diag] k : E3), by
      simp [Metric.mem_sphere, dist_zero_right, embE3_norm hb]⟩ : ↑(Metric.sphere (0 : E4) 1))) = wE₁ := by
    ext k; fin_cases k <;> rfl
  have hwE2 : (fun k : Fin 3 => (⟨embE3 b (![seq (2 + 1), seq (3 + 1), n_diag'] k : E3), by
      simp [Metric.mem_sphere, dist_zero_right, embE3_norm hb]⟩ : ↑(Metric.sphere (0 : E4) 1))) = wE₂ := by
    ext k; fin_cases k <;> rfl
  rw [hwE1] at hv1
  rw [hwE2] at hv2
  have hv2' : MeasureTheory.volume.toSphere.real (triSusp4 wE₂) =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi) * sphExcess d₀ d₃ d' := by
    rw [hv2]; congr 1; simp only [sphExcess, sphAngle_swap]; ring
  rw [hm, hpre_eq, hmunion, hv1, hv2']
  have hsum_d_eq : ∑ i : Fin 4, Real.arccos (inner ℝ (V (i - 1) : E3) (V i : E3)) =
      d₀ + d₁ + d₂ + d₃ := by
    rw [Fin.sum_univ_four]
    have hm1 : (0 - 1 : Fin 4) = 3 := by decide
    have hm2 : (1 - 1 : Fin 4) = 0 := by decide
    have hm3 : (2 - 1 : Fin 4) = 1 := by decide
    have hm4 : (3 - 1 : Fin 4) = 2 := by decide
    rw [hm1, hm2, hm3, hm4]
  have hd_sum_le : d₀ + d₁ + d₂ + d₃ ≤ totalStdArea / 2 := hsum_d_eq ▸ hsum_d
  have hiso1 : sphExcess d₂ d' d₁ ≤ sphExcess ((d₁ + d₂) / 2) ((d₁ + d₂) / 2) d' := by
    rw [sphExcess_perm_cyc d₁ d₂ d']
    exact sphExcess_le_isosceles hd1_pos hd1_lt hd2_pos hd2_lt hd'_pos hd'_lt
      ht1_b ht1_c ht1_a (by linarith [ht1_s])
  have hiso2 : sphExcess d₀ d₃ d' ≤ sphExcess ((d₀ + d₃) / 2) ((d₀ + d₃) / 2) d' :=
    sphExcess_le_isosceles hd0_pos hd0_lt hd3_pos hd3_lt hd'_pos hd'_lt
      (by linarith [ht2_b]) (by linarith [ht2_a]) (by linarith [ht2_c]) (by linarith [ht2_s])
  have hpair_bound : ∀ a b : ℝ,
      d' / 2 < a → a < Real.pi - d' / 2 →
      d' / 2 < b → b < Real.pi - d' / 2 →
      b ≤ a → a + b ≤ totalStdArea / 4 →
      sphExcess a a d' + sphExcess b b d' ≤
        4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi := by
    intro a b ha_lo ha_hi hb_lo hb_hi hba hab_le
    have hab_pi : a + b < Real.pi := by linarith
    have hkite_res := sphExcess_kite_half hd'_pos hd'_lt ha_lo ha_hi hb_lo.le hb_hi hab_pi
    dsimp only at hkite_res
    set d'' := Real.arccos (Real.cos a / Real.cos (d' / 2)) +
      Real.arccos (Real.cos b / Real.cos (d' / 2))
    rcases hkite_res with ⟨hd''_pos, hd''_lt, hd''_ub, ha_tri, hb_tri, hk_sum, hkite⟩
    rw [if_neg hb_lo.ne'] at hkite
    have ha_pos : 0 < a := by linarith
    have ha_lt : a < Real.pi := by linarith
    have hb_pos : 0 < b := by linarith
    have hb_lt : b < Real.pi := by linarith
    have hiso_k := sphExcess_le_isosceles ha_pos ha_lt hb_pos hb_lt hd''_pos hd''_lt
      hd''_ub ha_tri hb_tri hk_sum
    set M := (a + b) / 2
    dsimp only at hiso_k
    have hM_pos : 0 < M := by dsimp [M]; linarith
    have hM_le : M ≤ totalStdArea / 8 := by dsimp [M]; linarith
    have hM_lt : M < Real.pi / 2 := by linarith
    have hd''_lt2M : d'' < 2 * M := by dsimp [M]; linarith
    have hsq1 := sphExcess_isosceles_le_square hM_pos hM_lt hd''_pos hd''_lt2M
    have hsq2 := sphSquare_area_mono hM_pos.le hM_le (by linarith)
    rw [show totalStdArea / 8 / 2 = totalStdArea / 16 by ring] at hsq2
    linarith [hkite, hiso_k, hsq1, hsq2]
  set m₁ := (d₁ + d₂) / 2
  set m₂ := (d₀ + d₃) / 2
  have hm1_lo : d' / 2 < m₁ := by dsimp [m₁]; linarith
  have hm1_hi : m₁ < Real.pi - d' / 2 := by dsimp [m₁]; linarith
  have hm2_lo : d' / 2 < m₂ := by dsimp [m₂]; linarith
  have hm2_hi : m₂ < Real.pi - d' / 2 := by dsimp [m₂]; linarith
  have hm_sum : m₁ + m₂ ≤ totalStdArea / 4 := by dsimp [m₁, m₂]; linarith
  have hexcess_sum : sphExcess d₂ d' d₁ + sphExcess d₀ d₃ d' ≤
      4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi := by
    by_cases hle : m₂ ≤ m₁
    · have h1 := hpair_bound m₁ m₂ hm1_lo hm1_hi hm2_lo hm2_hi hle hm_sum
      linarith
    · push_neg at hle
      have h1 := hpair_bound m₂ m₁ hm2_lo hm2_hi hm1_lo hm1_hi hle.le (by linarith)
      linarith
  have hscale_nonneg : 0 ≤ sphereScale 3 *
      (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi)) := by
    have hss := (sphereScale_pos (d := 3) (by decide)).le
    have huniv : 0 ≤ MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) :=
      ENNReal.toReal_nonneg
    positivity
  calc sphereScale 3 *
        (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi) * sphExcess d₂ d' d₁ +
          MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi) * sphExcess d₀ d₃ d')
      = (sphereScale 3 *
          (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi))) * (sphExcess d₂ d' d₁ + sphExcess d₀ d₃ d') := by ring
    _ ≤ (sphereScale 3 *
          (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi))) * (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) :=
        mul_le_mul_of_nonneg_left hexcess_sum hscale_nonneg

end BoundaryPolygon

/-- **Boundary Volume Upper Bound (Degenerate Configurations)**:
If four unit normals `u` in `ℝ⁴` are linearly dependent and the total 2D facet area of the
corresponding polytope does not exceed `faceScale * totalStdArea`, then the 3D spherical volume
does not exceed that of the degenerate square suspension of equal facet area. -/
theorem degenerate_limit_volume_le_square
    (u : Fin 4 → ↑(Metric.sphere (0 : E4) 1))
    (hdeg : ¬ LinearIndependent ℝ (fun i => (u i : E4)))
    (totalStdArea : ℝ) (hA0 : 0 < totalStdArea) (hA4pi : totalStdArea < 4 * Real.pi)
    (hArea : ∑ v ∈ Finset.image u Finset.univ,
      measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
        inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ Finset.image u Finset.univ, 0 ≤ inner ℝ (v' : E4) x} ≤
      faceScale * totalStdArea) :
    measure 3 {x ∈ Metric.sphere (0 : E4) 1 | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} ≤
      sphereScale 3 *
        (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
          (4 * Real.pi)) *
        (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) := by
  have hrhs_nonneg : 0 ≤ sphereScale 3 *
      (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi)) *
      (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) := by
    have hss := (sphereScale_pos (d := 3) (by decide)).le
    have huniv : 0 ≤ MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) :=
      ENNReal.toReal_nonneg
    have hsq := rhs_square_area_nonneg hA0 hA4pi
    positivity
  have hfin := finrank_span_lt_four_of_not_linIndep u hdeg
  obtain ⟨w, hw_norm, hw_orth⟩ := exists_unit_orthogonal_of_finrank_lt hfin
  obtain ⟨b, hb, hb0⟩ := exists_ortho_frame_E4 w hw_norm
  have hu_orth : ∀ i : Fin 4, inner ℝ (b 0) (u i : E4) = 0 := by
    intro i
    rw [hb0, real_inner_comm]
    exact hw_orth (u i : E4) (Submodule.subset_span ⟨i, rfl⟩)
  let u3 : Fin 4 → ↑(Metric.sphere (0 : E3) 1) := fun i =>
    ⟨projE3 b (u i : E4), by
      have hemb := embE3_projE3_of_ortho hb (hu_orth i)
      have hn : ‖projE3 b (u i : E4)‖ = 1 := by
        rw [← embE3_norm hb, hemb]
        simpa [Metric.mem_sphere, dist_zero_right] using (u i).2
      simpa [Metric.mem_sphere, dist_zero_right] using hn⟩
  have hu_eq : ∀ i : Fin 4, (u i : E4) = embE3 b (u3 i : E3) :=
    fun i => (embE3_projE3_of_ortho hb (hu_orth i)).symm
  let V_E4 : Finset ↑(Metric.sphere (0 : E4) 1) := Finset.image u Finset.univ
  let V₃ : Finset ↑(Metric.sphere (0 : E3) 1) := Finset.image u3 Finset.univ
  have hV₃_ne : V₃.Nonempty := ⟨u3 0, Finset.mem_image_of_mem u3 (Finset.mem_univ 0)⟩
  have hV₃_card : V₃.card ≤ 4 := by
    calc V₃.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := Fintype.card_fin 4
  rcases sphere_cone_exists_pole_or_null V₃ hV₃_ne with ⟨r₀, hr₀, hzero⟩ | ⟨z₀, hz₀⟩
  · let n : E4 := embE3 b (r₀ : E3)
    have hn_norm : ‖n‖ = 1 := by
      rw [embE3_norm hb]; simpa [Metric.mem_sphere, dist_zero_right] using r₀.2
    have hn_ne : n ≠ 0 := fun h => by rw [h, norm_zero] at hn_norm; norm_num at hn_norm
    have hsub : ∀ x : E4, x ∈ Metric.sphere (0 : E4) 1 →
        (∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x) → inner ℝ n x = 0 := by
      intro x _ hx
      rw [show inner ℝ n x = inner ℝ (r₀ : E3) (projE3 b x) from inner_embE3_left b _ x]
      refine hzero (projE3 b x) (fun r hr => ?_)
      rcases Finset.mem_image.mp hr with ⟨i, _, rfl⟩
      rw [← inner_embE3_left, ← hu_eq i]
      exact hx i
    rw [measure_three_null_of_ortho_dot_zero u hn_ne hsub]
    exact hrhs_nonneg
  · have hno_planar := area_degenerate_case_one_or_planar u hb u3 hu_eq totalStdArea hA4pi hArea z₀ hz₀
    have hV₃_cone : ∀ y : E3, (∀ s ∈ V₃, 0 ≤ inner ℝ (s : E3) y) →
        ∀ r ∈ V₃, 0 ≤ inner ℝ (r : E3) y := fun _ hy r hr => hy r hr
    obtain ⟨S, hSV, hScone, hSmin⟩ :=
      exists_minimal_halfspace_set V₃ V₃.card V₃ Finset.Subset.rfl rfl hV₃_cone
    obtain ⟨hcard34, ⟨w₀, hw₀⟩, hx_edge⟩ :=
      sphere_polygon_pole_and_edges hSV hV₃_card hScone hno_planar z₀
        (fun r hr => hz₀ r hr) hSmin
    have hz₀_S : ∀ s ∈ S, 0 < inner ℝ (s : E3) (z₀ : E3) := fun s hs => hz₀ s (hSV hs)
    have hS_ge3 : 3 ≤ S.card := by omega
    haveI : NeZero S.card := ⟨by omega⟩
    obtain ⟨seq, V, hseq_mem, hseq_inj, hseq_surj, hV_nonneg, hV_zero, hV_pos, _⟩ :=
      polygon_cyclic_vertices hS_ge3 z₀ hz₀_S w₀ hw₀ hx_edge
    have hcone_iff : ∀ x : E4, (∀ k : Fin S.card, 0 ≤ inner ℝ (embE3 b (seq k : E3)) x) ↔
        (∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x) := by
      intro x
      constructor
      · intro hk v' hv'
        rcases Finset.mem_image.mp hv' with ⟨i, _, rfl⟩
        rw [hu_eq i, inner_embE3_left]
        refine hScone (projE3 b x) (fun s hs => ?_) (u3 i)
          (Finset.mem_image_of_mem u3 (Finset.mem_univ i))
        obtain ⟨k, rfl⟩ := hseq_surj s hs
        rw [← inner_embE3_left]; exact hk k
      · intro hv k
        have hmem : seq k ∈ V₃ := hSV (hseq_mem k)
        rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
        rw [← hi, ← hu_eq i]
        exact hv (u i) (Finset.mem_image_of_mem u (Finset.mem_univ i))
    have hfac := measure_facet_eq_two_faceScale_mul_arccos hS_ge3 hb V_E4 seq V hcone_iff
      hV_nonneg hV_zero hV_pos
    let embV : Fin S.card → ↑(Metric.sphere (0 : E4) 1) := fun k =>
      ⟨embE3 b (seq k : E3), by
        simpa [Metric.mem_sphere, dist_zero_right, embE3_norm hb] using (seq k).2⟩
    have hembV_inj : Function.Injective embV := by
      intro j k hjk
      apply hseq_inj
      ext1
      have h0 : ‖(seq j : E3) - (seq k : E3)‖ = 0 := by
        rw [← embE3_norm hb, show embE3 b ((seq j : E3) - (seq k : E3)) =
          embE3 b (seq j : E3) - embE3 b (seq k : E3) by simp [embE3]; module]
        have := congrArg Subtype.val hjk
        dsimp [embV] at this
        rw [this, sub_self, norm_zero]
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    have hembV_mem : ∀ k : Fin S.card, embV k ∈ V_E4 := by
      intro k
      have hmem : seq k ∈ V₃ := hSV (hseq_mem k)
      rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
      ext1; dsimp [embV]; rw [hu_eq i, hi]
    have hsum_facets : ∑ k : Fin S.card,
        measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (embE3 b (seq k : E3)) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x} ≤
        faceScale * totalStdArea := by
      have heq_img : ∑ k : Fin S.card,
          measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
            inner ℝ (embE3 b (seq k : E3)) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x} =
          ∑ v ∈ Finset.image embV Finset.univ,
            measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
              inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x} := by
        rw [Finset.sum_image (fun j _ k _ h => hembV_inj h)]
      rw [heq_img]
      have hsub : Finset.image embV Finset.univ ⊆ V_E4 := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨k, _, rfl⟩
        exact hembV_mem k
      let fFac : ↑(Metric.sphere (0 : E4) 1) → ℝ := fun v =>
        measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
          inner ℝ (v : E4) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x}
      have hle : ∑ v ∈ Finset.image embV Finset.univ, fFac v ≤ ∑ v ∈ V_E4, fFac v :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ENNReal.toReal_nonneg
      exact hle.trans hArea
    have hsum_d : ∑ k : Fin S.card, Real.arccos (inner ℝ (V (k - 1) : E3) (V k : E3)) ≤
        totalStdArea / 2 := by
      have h1 : 2 * faceScale *
          (∑ k : Fin S.card, Real.arccos (inner ℝ (V (k - 1) : E3) (V k : E3))) ≤
          faceScale * totalStdArea := by
        rw [Finset.mul_sum]
        calc ∑ k : Fin S.card, 2 * faceScale * Real.arccos (inner ℝ (V (k - 1) : E3) (V k : E3))
            = ∑ k : Fin S.card, measure 2 {x ∈ Metric.sphere (0 : E4) 1 |
                inner ℝ (embE3 b (seq k : E3)) x = 0 ∧ ∀ v' ∈ V_E4, 0 ≤ inner ℝ (v' : E4) x} := by
                refine Finset.sum_congr rfl fun k _ => (hfac k).symm
          _ ≤ faceScale * totalStdArea := hsum_facets
      have hfpos := faceScale_pos
      nlinarith
    rcases hcard34 with h3 | h4
    · let seq3 : Fin 3 → ↑(Metric.sphere (0 : E3) 1) := fun k => seq (Fin.cast h3.symm k)
      let V3 : Fin 3 → ↑(Metric.sphere (0 : E3) 1) := fun k => V (Fin.cast h3.symm k)
      have hcast_inj3 : Function.Injective (Fin.cast h3.symm) := fun a b hab => by
        simpa [Fin.ext_iff] using hab
      have hcast_surj3 : ∀ k : Fin S.card, ∃ j : Fin 3, Fin.cast h3.symm j = k := fun k =>
        ⟨Fin.cast h3 k, by ext; rfl⟩
      have hcast_add3 : ∀ j : Fin 3, Fin.cast h3.symm (j + 1) = Fin.cast h3.symm j + 1 := by
        intro j
        have hj1 : ((1 : Fin 3) : ℕ) = 1 := rfl
        have hs1 : ((1 : Fin S.card) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < S.card)
        ext; change ((j + 1 : Fin 3) : ℕ) = ((Fin.cast h3.symm j + 1 : Fin S.card) : ℕ)
        simp [Fin.val_add, hj1, hs1, h3]
      have hcast_sub3 : ∀ j : Fin 3, Fin.cast h3.symm (j - 1) = Fin.cast h3.symm j - 1 := by
        intro j
        have hadd := hcast_add3 (j - 1)
        rw [show (j - 1 : Fin 3) + 1 = j from by abel] at hadd
        calc Fin.cast h3.symm (j - 1)
            = Fin.cast h3.symm (j - 1) + 1 - 1 := by abel
          _ = Fin.cast h3.symm j - 1 := by rw [← hadd]
      have hsum_d3 : ∑ k : Fin 3, Real.arccos (inner ℝ (V3 (k - 1) : E3) (V3 k : E3)) ≤
          totalStdArea / 2 := by
        have hsum_eq : ∑ k : Fin 3, Real.arccos (inner ℝ (V3 (k - 1) : E3) (V3 k : E3)) =
            ∑ k : Fin S.card, Real.arccos (inner ℝ (V (k - 1) : E3) (V k : E3)) := by
          refine Fintype.sum_bijective (Fin.cast h3.symm) ⟨hcast_inj3, hcast_surj3⟩ _ _ fun j => ?_
          dsimp [V3]; rw [hcast_sub3 j]
        linarith [hsum_d, hsum_eq]
      exact degenerate_limit_volume_three_case hb u V_E4 rfl seq3 V3
        (fun x => ⟨fun hk => (hcone_iff x).mp fun k => by
            obtain ⟨j, rfl⟩ := hcast_surj3 k; exact hk j,
          fun hv j => (hcone_iff x).mpr hv _⟩)
        (fun i => by dsimp [seq3, V3]; rw [hcast_add3 i]; exact hV_zero _)
        (fun i k hki hki1 => hV_pos _ _ (fun h => hki (hcast_inj3 h))
          (fun h => hki1 (hcast_inj3 (by rw [hcast_add3 i]; exact h))))
        totalStdArea hA0 hA4pi hsum_d3
    · let seq4 : Fin 4 → ↑(Metric.sphere (0 : E3) 1) := fun k => seq (Fin.cast h4.symm k)
      let V4 : Fin 4 → ↑(Metric.sphere (0 : E3) 1) := fun k => V (Fin.cast h4.symm k)
      have hcast_inj4 : Function.Injective (Fin.cast h4.symm) := fun a b hab => by
        simpa [Fin.ext_iff] using hab
      have hcast_surj4 : ∀ k : Fin S.card, ∃ j : Fin 4, Fin.cast h4.symm j = k := fun k =>
        ⟨Fin.cast h4 k, by ext; rfl⟩
      have hcast_add4 : ∀ j : Fin 4, Fin.cast h4.symm (j + 1) = Fin.cast h4.symm j + 1 := by
        intro j
        have hj1 : ((1 : Fin 4) : ℕ) = 1 := rfl
        have hs1 : ((1 : Fin S.card) : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < S.card)
        ext; change ((j + 1 : Fin 4) : ℕ) = ((Fin.cast h4.symm j + 1 : Fin S.card) : ℕ)
        simp [Fin.val_add, hj1, hs1, h4]
      have hcast_sub4 : ∀ j : Fin 4, Fin.cast h4.symm (j - 1) = Fin.cast h4.symm j - 1 := by
        intro j
        have hadd := hcast_add4 (j - 1)
        rw [show (j - 1 : Fin 4) + 1 = j from by abel] at hadd
        calc Fin.cast h4.symm (j - 1)
            = Fin.cast h4.symm (j - 1) + 1 - 1 := by abel
          _ = Fin.cast h4.symm j - 1 := by rw [← hadd]
      have hsum_d4 : ∑ k : Fin 4, Real.arccos (inner ℝ (V4 (k - 1) : E3) (V4 k : E3)) ≤
          totalStdArea / 2 := by
        have hsum_eq : ∑ k : Fin 4, Real.arccos (inner ℝ (V4 (k - 1) : E3) (V4 k : E3)) =
            ∑ k : Fin S.card, Real.arccos (inner ℝ (V (k - 1) : E3) (V k : E3)) := by
          refine Fintype.sum_bijective (Fin.cast h4.symm) ⟨hcast_inj4, hcast_surj4⟩ _ _ fun j => ?_
          dsimp [V4]; rw [hcast_sub4 j]
        linarith [hsum_d, hsum_eq]
      exact degenerate_limit_volume_four_case hb u V_E4 rfl seq4 V4
        (fun x => ⟨fun hk => (hcone_iff x).mp fun k => by
            obtain ⟨j, rfl⟩ := hcast_surj4 k; exact hk j,
          fun hv j => (hcone_iff x).mpr hv _⟩)
        (fun i k => hV_nonneg _ _)
        (fun i => by dsimp [seq4, V4]; rw [hcast_add4 i]; exact hV_zero _)
        (fun i k hki hki1 => hV_pos _ _ (fun h => hki (hcast_inj4 h))
          (fun h => hki1 (hcast_inj4 (by rw [hcast_add4 i]; exact h))))
        totalStdArea hA0 hA4pi hsum_d4

/-!
### Part 3: Area-preserving perturbation of the degenerate square suspension
-/

/-- Symmetrized Gram coordinate vector of a square suspension with adjacent inner product `a`
and diagonal inner product `2 * a - 1 + d`. -/
private def sqVec (a d : ℝ) : Fin 6 → ℝ :=
  ![a, 2 * a - 1 + d, a, a, 2 * a - 1 + d, a]

private lemma sqVec_mem_gramOpen {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hd0 : 0 < d) (hd1 : d < 2 * (1 - a)) :
    sqVec a d ∈ gramOpen := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [gramDet2, sqVec]; nlinarith
  · have hpol : gramDet3 (sqVec a d) = Sphere3.squareSuspensionPolarDet a (2 * a - 1 + d) := by
      dsimp [gramDet3, sqVec, Sphere3.squareSuspensionPolarDet]; ring
    rw [hpol]
    exact Sphere3.squareSuspensionPolarDet_pos a d ha0 ha1 hd0 hd1
  · have hdet : gramDet4 (sqVec a d) = (4 * a + d) * d * (2 * (1 - a) - d) ^ 2 := by
      dsimp [gramDet4]
      rw [symUnitMat_det_eq_poly]
      dsimp [symUnitDetPoly, sqVec]
      ring
    rw [hdet]
    have h1 : 0 < 4 * a + d := by linarith
    have h2 : 0 < 2 * (1 - a) - d := by linarith
    positivity

private lemma hasDerivAt_linear (m c x : ℝ) :
    HasDerivAt (fun t : ℝ => m * t + c) m x := by
  refine ((((hasDerivAt_id x).const_mul m).add (hasDerivAt_const x c)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => by simp)).congr_deriv (by ring)

private lemma sqVec_hasDerivAt_d (a d : ℝ) :
    HasDerivAt (fun t => sqVec a t) (![0, 1, 0, 0, 1, 0] : Fin 6 → ℝ) d := by
  rw [hasDerivAt_pi]
  intro k
  fin_cases k
  · exact hasDerivAt_const d a
  · exact (hasDerivAt_linear 1 (2 * a - 1) d).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by dsimp [sqVec]; ring)
  · exact hasDerivAt_const d a
  · exact hasDerivAt_const d a
  · exact (hasDerivAt_linear 1 (2 * a - 1) d).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by dsimp [sqVec]; ring)
  · exact hasDerivAt_const d a

private lemma sqVec_hasDerivAt_a (a d : ℝ) :
    HasDerivAt (fun x => sqVec x d) (![1, 2, 1, 1, 2, 1] : Fin 6 → ℝ) a := by
  rw [hasDerivAt_pi]
  intro k
  fin_cases k
  · exact (hasDerivAt_linear 1 0 a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by dsimp [sqVec]; ring)
  · exact (hasDerivAt_linear 2 (d - 1) a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by dsimp [sqVec]; ring)
  · exact (hasDerivAt_linear 1 0 a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by dsimp [sqVec]; ring)
  · exact (hasDerivAt_linear 1 0 a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by dsimp [sqVec]; ring)
  · exact (hasDerivAt_linear 2 (d - 1) a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by dsimp [sqVec]; ring)
  · exact (hasDerivAt_linear 1 0 a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by dsimp [sqVec]; ring)

private lemma faceLinkAngle_swap_left (u v w : ℝ) :
    faceLinkAngle u v w = faceLinkAngle v u w := by
  dsimp [faceLinkAngle]
  rw [mul_comm u v, mul_comm (1 - u ^ 2) (1 - v ^ 2)]

private lemma stdAreaGram_sqVec (a d : ℝ) :
    stdAreaGram (sqVec a d) =
      8 * faceLinkAngle a (2 * a - 1 + d) a + 4 * faceLinkAngle a a (2 * a - 1 + d) - 4 * Real.pi := by
  dsimp [stdAreaGram, sqVec, vertexLinkSum]
  rw [faceLinkAngle_swap_left (2 * a - 1 + d) a a]
  ring

private lemma stdAreaGram_sqVec_zero {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < Real.pi / 4) :
    let a := Real.tan φ ^ 2
    0 < a ∧ a < 1 ∧ stdAreaGram (sqVec a 0) = 16 * φ := by
  intro a
  have hcos_pos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsin_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have htan_pos : 0 < Real.tan φ := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin_pos hcos_pos
  have htan_lt : Real.tan φ < 1 := by
    have h := Real.strictMonoOn_tan
      ⟨by linarith [Real.pi_pos], by linarith⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hφ1
    rwa [Real.tan_pi_div_four] at h
  have ha0 : 0 < a := sq_pos_of_pos htan_pos
  have ha1 : a < 1 := by
    change Real.tan φ ^ 2 < 1
    nlinarith
  have h1ma_pos : 0 < 1 - a := by linarith
  have ha_sc : a = Real.sin φ ^ 2 / Real.cos φ ^ 2 := by
    change Real.tan φ ^ 2 = _
    rw [Real.tan_eq_sin_div_cos, div_pow]
  have h1a2_pos : 0 < 1 - a ^ 2 := by nlinarith
  have hcos2 : (1 - a) / (1 + a) = Real.cos (2 * φ) := by
    have hcos2_ne : Real.cos φ ^ 2 ≠ 0 := pow_ne_zero 2 hcos_pos.ne'
    have hsin_sq : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith [Real.sin_sq_add_cos_sq φ]
    rw [ha_sc, hsin_sq, Real.cos_two_mul]
    field_simp [hcos2_ne]
    ring
  have hang1 : faceLinkAngle a a (2 * a - 1 + 0) = 2 * φ := by
    dsimp [faceLinkAngle]
    rw [Real.sqrt_mul_self h1a2_pos.le]
    have hrat : (a * a - (2 * a - 1 + 0)) / (1 - a ^ 2) = Real.cos (2 * φ) := by
      rw [← hcos2]
      have hpa_ne : 1 + a ≠ 0 := by linarith
      have h1a_ne : 1 - a ≠ 0 := h1ma_pos.ne'
      field_simp [hpa_ne, h1a_ne]
      ring
    rw [hrat]
    exact Real.arccos_cos (by linarith) (by linarith)
  have hang2 : faceLinkAngle a (2 * a - 1 + 0) a = Real.pi / 2 + φ := by
    dsimp [faceLinkAngle]
    have hs_pos : 0 < 2 * (1 - a) * Real.sin φ / Real.cos φ ^ 2 := by positivity
    have hsub_nonneg : 0 ≤ (1 - a ^ 2) * (1 - (2 * a - 1 + 0) ^ 2) := by
      have hsub1 : 1 - (2 * a - 1 + 0) ^ 2 = 4 * a * (1 - a) := by ring
      rw [hsub1]
      exact mul_nonneg h1a2_pos.le (by positivity)
    have hs_eq : √((1 - a ^ 2) * (1 - (2 * a - 1 + 0) ^ 2)) =
        2 * (1 - a) * Real.sin φ / Real.cos φ ^ 2 := by
      refine (Real.sqrt_eq_iff_eq_sq hsub_nonneg hs_pos.le).mpr ?_
      have hsin_sq : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith [Real.sin_sq_add_cos_sq φ]
      have hcos_ne : Real.cos φ ≠ 0 := hcos_pos.ne'
      have ha1p : a * (1 + a) = Real.sin φ ^ 2 / Real.cos φ ^ 4 := by
        rw [ha_sc, hsin_sq]
        field_simp [hcos_ne]
        ring
      calc (1 - a ^ 2) * (1 - (2 * a - 1 + 0) ^ 2)
          = 4 * (1 - a) ^ 2 * (a * (1 + a)) := by ring
        _ = 4 * (1 - a) ^ 2 * (Real.sin φ ^ 2 / Real.cos φ ^ 4) := by rw [ha1p]
        _ = (2 * (1 - a) * Real.sin φ / Real.cos φ ^ 2) ^ 2 := by ring
    rw [hs_eq]
    have hnum_eq : a * (2 * a - 1 + 0) - a = -2 * (1 - a) * (Real.sin φ ^ 2 / Real.cos φ ^ 2) := by
      rw [← ha_sc]; ring
    have hrat : (a * (2 * a - 1 + 0) - a) / (2 * (1 - a) * Real.sin φ / Real.cos φ ^ 2) =
        Real.cos (Real.pi / 2 + φ) := by
      rw [hnum_eq, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
      field_simp [h1ma_pos.ne', hsin_pos.ne', hcos_pos.ne']
      ring
    rw [hrat]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith)
  refine ⟨ha0, ha1, ?_⟩
  rw [stdAreaGram_sqVec, hang1, hang2]
  ring

private lemma stdAreaGram_sqVec_continuousOn_d {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {dmax : ℝ} (hdmax : dmax < 2 * (1 - a)) :
    ContinuousOn (fun d => stdAreaGram (sqVec a d)) (Set.Icc 0 dmax) := by
  have hb_sub : ∀ d ∈ Set.Icc (0 : ℝ) dmax,
      0 < (1 - a ^ 2) * (1 - (2 * a - 1 + d) ^ 2) := fun d hd => by
    have h1a : 0 < 1 - a ^ 2 := by nlinarith
    have hb1 : -1 < 2 * a - 1 + d := by linarith [hd.1]
    have hb2 : 2 * a - 1 + d < 1 := by linarith [hd.2]
    have h1b : 0 < 1 - (2 * a - 1 + d) ^ 2 := by nlinarith
    exact mul_pos h1a h1b
  have ha_sub : 0 < (1 - a ^ 2) * (1 - a ^ 2) := by
    have h1a : 0 < 1 - a ^ 2 := by nlinarith
    exact mul_pos h1a h1a
  have hf : (fun d => stdAreaGram (sqVec a d)) = fun d =>
      8 * Real.arccos ((a * (2 * a - 1 + d) - a) / √((1 - a ^ 2) * (1 - (2 * a - 1 + d) ^ 2))) +
        4 * Real.arccos ((a ^ 2 - (2 * a - 1 + d)) / √((1 - a ^ 2) * (1 - a ^ 2))) -
        4 * Real.pi := by
    ext d
    rw [stdAreaGram_sqVec]
    dsimp [faceLinkAngle]
    rw [← sq a]
  rw [hf]
  have hc_b : ContinuousOn (fun d : ℝ => 2 * a - 1 + d) (Set.Icc 0 dmax) :=
    continuousOn_const.add continuousOn_id
  have hc1 : ContinuousOn (fun d : ℝ =>
      (a * (2 * a - 1 + d) - a) / √((1 - a ^ 2) * (1 - (2 * a - 1 + d) ^ 2))) (Set.Icc 0 dmax) := by
    refine ContinuousOn.div ((continuousOn_const.mul hc_b).sub continuousOn_const) ?_ fun d hd =>
      (Real.sqrt_pos.mpr (hb_sub d hd)).ne'
    refine Real.continuous_sqrt.comp_continuousOn ?_
    exact continuousOn_const.mul (continuousOn_const.sub (hc_b.pow 2))
  have hc2 : ContinuousOn (fun d : ℝ =>
      (a ^ 2 - (2 * a - 1 + d)) / √((1 - a ^ 2) * (1 - a ^ 2))) (Set.Icc 0 dmax) := by
    exact ContinuousOn.div (continuousOn_const.sub hc_b) continuousOn_const fun _ _ =>
      (Real.sqrt_pos.mpr ha_sub).ne'
  exact (((continuousOn_const.mul (Real.continuous_arccos.comp_continuousOn hc1)).add
    (continuousOn_const.mul (Real.continuous_arccos.comp_continuousOn hc2))).sub
    continuousOn_const)

private lemma stdAreaGram_sqVec_continuousOn_a {d : ℝ} (hd0 : 0 ≤ d)
    {a_lo a_hi : ℝ} (halo : 0 < a_lo) (hahi : a_hi < 1) (hd_hi : d ≤ 1 - a_hi) :
    ContinuousOn (fun a => stdAreaGram (sqVec a d)) (Set.Icc a_lo a_hi) := by
  have ha_sub : ∀ a ∈ Set.Icc a_lo a_hi, 0 < (1 - a ^ 2) * (1 - a ^ 2) := fun a ha => by
    have ha0 : 0 < a := lt_of_lt_of_le halo ha.1
    have ha1 : a < 1 := lt_of_le_of_lt ha.2 hahi
    have h1a : 0 < 1 - a ^ 2 := by nlinarith
    exact mul_pos h1a h1a
  have hb_sub : ∀ a ∈ Set.Icc a_lo a_hi,
      0 < (1 - a ^ 2) * (1 - (2 * a - 1 + d) ^ 2) := fun a ha => by
    have ha0 : 0 < a := lt_of_lt_of_le halo ha.1
    have ha1 : a < 1 := lt_of_le_of_lt ha.2 hahi
    have h1a : 0 < 1 - a ^ 2 := by nlinarith
    have hb1 : -1 < 2 * a - 1 + d := by linarith [ha.1]
    have hb2 : 2 * a - 1 + d < 1 := by linarith [ha.2]
    have h1b : 0 < 1 - (2 * a - 1 + d) ^ 2 := by nlinarith
    exact mul_pos h1a h1b
  have hf : (fun a => stdAreaGram (sqVec a d)) = fun a =>
      8 * Real.arccos ((a * (2 * a - 1 + d) - a) / √((1 - a ^ 2) * (1 - (2 * a - 1 + d) ^ 2))) +
        4 * Real.arccos ((a ^ 2 - (2 * a - 1 + d)) / √((1 - a ^ 2) * (1 - a ^ 2))) -
        4 * Real.pi := by
    ext a
    rw [stdAreaGram_sqVec]
    dsimp [faceLinkAngle]
    rw [← sq a]
  rw [hf]
  have hc_b : ContinuousOn (fun a : ℝ => 2 * a - 1 + d) (Set.Icc a_lo a_hi) :=
    ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).add continuousOn_const
  have hc_a2 : ContinuousOn (fun a : ℝ => 1 - a ^ 2) (Set.Icc a_lo a_hi) :=
    continuousOn_const.sub (continuousOn_id.pow 2)
  have hc1 : ContinuousOn (fun a : ℝ =>
      (a * (2 * a - 1 + d) - a) / √((1 - a ^ 2) * (1 - (2 * a - 1 + d) ^ 2))) (Set.Icc a_lo a_hi) := by
    refine ContinuousOn.div ((continuousOn_id.mul hc_b).sub continuousOn_id) ?_ fun a ha =>
      (Real.sqrt_pos.mpr (hb_sub a ha)).ne'
    exact Real.continuous_sqrt.comp_continuousOn
      (hc_a2.mul (continuousOn_const.sub (hc_b.pow 2)))
  have hc2 : ContinuousOn (fun a : ℝ =>
      (a ^ 2 - (2 * a - 1 + d)) / √((1 - a ^ 2) * (1 - a ^ 2))) (Set.Icc a_lo a_hi) := by
    refine ContinuousOn.div ((continuousOn_id.pow 2).sub hc_b) ?_ fun a ha =>
      (Real.sqrt_pos.mpr (ha_sub a ha)).ne'
    exact Real.continuous_sqrt.comp_continuousOn (hc_a2.mul hc_a2)
  exact (((continuousOn_const.mul (Real.continuous_arccos.comp_continuousOn hc1)).add
    (continuousOn_const.mul (Real.continuous_arccos.comp_continuousOn hc2))).sub
    continuousOn_const)

private lemma triDet3_sqVec_symm (a b : ℝ) :
    triDet3 a b a = Sphere3.squareSuspensionPolarDet a b ∧
    triDet3 b a a = Sphere3.squareSuspensionPolarDet a b ∧
    triDet3 a a b = Sphere3.squareSuspensionPolarDet a b := by
  dsimp [triDet3, Sphere3.squareSuspensionPolarDet]
  refine ⟨by ring, by ring, by ring⟩

private lemma stdAreaFDeriv_sqVec_d (a d : ℝ) :
    stdAreaFDeriv (sqVec a d) ![0, 1, 0, 0, 1, 0] =
      4 * d / ((2 * a + d) * √(Sphere3.squareSuspensionPolarDet a (2 * a - 1 + d))) := by
  set b := 2 * a - 1 + d
  have hD := triDet3_sqVec_symm a b
  simp only [stdAreaFDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    linkMap0, linkMap1, linkMap2, linkMap3, ContinuousLinearMap.pi_apply, coordProj6,
    ContinuousLinearMap.proj_apply, vertexLinkSumFDeriv, ContinuousLinearMap.smul_apply,
    triProj0, triProj1, triProj2, smul_eq_mul, sqVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [hD.1, hD.2.1, hD.2.2]
  change _ = 4 * d / ((2 * a + d) * √(Sphere3.squareSuspensionPolarDet a b))
  have hb1 : 1 + b - a - a = d := by dsimp [b]; ring
  have hb2 : 1 + b = 2 * a + d := by dsimp [b]; ring
  rw [hb1, hb2]
  ring

private lemma stdAreaFDeriv_sqVec_a (a d : ℝ) :
    stdAreaFDeriv (sqVec a d) ![1, 2, 1, 1, 2, 1] =
      8 * (2 * (1 - a) - d) /
          ((1 + a) * √(Sphere3.squareSuspensionPolarDet a (2 * a - 1 + d))) +
        8 * d / ((2 * a + d) * √(Sphere3.squareSuspensionPolarDet a (2 * a - 1 + d))) := by
  set b := 2 * a - 1 + d
  have hD := triDet3_sqVec_symm a b
  simp only [stdAreaFDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    linkMap0, linkMap1, linkMap2, linkMap3, ContinuousLinearMap.pi_apply, coordProj6,
    ContinuousLinearMap.proj_apply, vertexLinkSumFDeriv, ContinuousLinearMap.smul_apply,
    triProj0, triProj1, triProj2, smul_eq_mul, sqVec, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [hD.1, hD.2.1, hD.2.2]
  change _ = 8 * (2 * (1 - a) - d) / ((1 + a) * √(Sphere3.squareSuspensionPolarDet a b)) +
    8 * d / ((2 * a + d) * √(Sphere3.squareSuspensionPolarDet a b))
  have h1 : 1 + a - b - a = 2 * (1 - a) - d := by dsimp [b]; ring
  have h2 : 1 + a - a - b = 2 * (1 - a) - d := by dsimp [b]; ring
  have h3 : 1 + b - a - a = d := by dsimp [b]; ring
  have h4 : 1 + b = 2 * a + d := by dsimp [b]; ring
  rw [h1, h2, h3, h4]
  ring

/-- Unit normal vectors realizing `sqVec a d` in `E4` for all `0 ≤ d < 2 * (1 - a)`. -/
private def sqNormVec (a d : ℝ) : Fin 4 → E4
  | 0 => WithLp.toLp 2 ![√(4 * a + d) / 2, √(2 * (1 - a) - d) / √2, 0, √d / 2]
  | 1 => WithLp.toLp 2 ![√(4 * a + d) / 2, 0, √(2 * (1 - a) - d) / √2, -(√d / 2)]
  | 2 => WithLp.toLp 2 ![√(4 * a + d) / 2, -(√(2 * (1 - a) - d) / √2), 0, √d / 2]
  | 3 => WithLp.toLp 2 ![√(4 * a + d) / 2, 0, -(√(2 * (1 - a) - d) / √2), -(√d / 2)]

private lemma sqNormVec_norm {a d : ℝ} (ha0 : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 2 * (1 - a))
    (i : Fin 4) : ‖sqNormVec a d i‖ = 1 := by
  have hs0 : √(4 * a + d) * √(4 * a + d) = 4 * a + d := Real.mul_self_sqrt (by linarith)
  have hs1 : √(2 * (1 - a) - d) * √(2 * (1 - a) - d) = 2 * (1 - a) - d :=
    Real.mul_self_sqrt (by linarith)
  have hs2 : √d * √d = d := Real.mul_self_sqrt hd0
  have hsq2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, ← real_inner_self_eq_norm_sq,
    PiLp.inner_apply]
  fin_cases i <;>
    · simp only [sqNormVec, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        div_mul_div_comm, neg_mul, mul_neg, neg_neg, mul_zero, zero_mul, add_zero, zero_add,
        hs0, hs1, hs2, hsq2]
      ring

private lemma sqNormVec_inner {a d : ℝ} (ha0 : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 2 * (1 - a)) :
    inner ℝ (sqNormVec a d 0) (sqNormVec a d 1) = a ∧
    inner ℝ (sqNormVec a d 0) (sqNormVec a d 2) = 2 * a - 1 + d ∧
    inner ℝ (sqNormVec a d 0) (sqNormVec a d 3) = a ∧
    inner ℝ (sqNormVec a d 1) (sqNormVec a d 2) = a ∧
    inner ℝ (sqNormVec a d 1) (sqNormVec a d 3) = 2 * a - 1 + d ∧
    inner ℝ (sqNormVec a d 2) (sqNormVec a d 3) = a := by
  have hs0 : √(4 * a + d) * √(4 * a + d) = 4 * a + d := Real.mul_self_sqrt (by linarith)
  have hs1 : √(2 * (1 - a) - d) * √(2 * (1 - a) - d) = 2 * (1 - a) - d :=
    Real.mul_self_sqrt (by linarith)
  have hs2 : √d * √d = d := Real.mul_self_sqrt hd0
  have hsq2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [PiLp.inner_apply]
      simp only [sqNormVec, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        div_mul_div_comm, neg_mul, mul_neg, neg_neg, mul_zero, zero_mul, add_zero, zero_add,
        hs0, hs1, hs2, hsq2]
      ring

private lemma sqNormVec_independent {a d : ℝ} (ha0 : 0 < a) (hd0 : 0 < d) (hd1 : d < 2 * (1 - a)) :
    LinearIndependent ℝ (sqNormVec a d) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hx0 := congrFun (congrArg WithLp.ofLp hc) 0
  have hx1 := congrFun (congrArg WithLp.ofLp hc) 1
  have hx2 := congrFun (congrArg WithLp.ofLp hc) 2
  have hx3 := congrFun (congrArg WithLp.ofLp hc) 3
  simp only [Finset.sum_apply, Fin.sum_univ_four, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    sqNormVec, PiLp.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hx0 hx1 hx2 hx3
  have hr0 : √(4 * a + d) / 2 ≠ 0 := div_ne_zero (Real.sqrt_pos.mpr (by linarith)).ne' (by norm_num)
  have hr1 : √(2 * (1 - a) - d) / √2 ≠ 0 :=
    div_ne_zero (Real.sqrt_pos.mpr (by linarith)).ne' (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hr2 : √d / 2 ≠ 0 := div_ne_zero (Real.sqrt_pos.mpr hd0).ne' (by norm_num)
  have hs0 : c 0 + c 1 + c 2 + c 3 = 0 := by
    have hmul : (√(4 * a + d) / 2) * (c 0 + c 1 + c 2 + c 3) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hr0
  have hs1 : c 0 - c 2 = 0 := by
    have hmul : (√(2 * (1 - a) - d) / √2) * (c 0 - c 2) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hr1
  have hs2 : c 1 - c 3 = 0 := by
    have hmul : (√(2 * (1 - a) - d) / √2) * (c 1 - c 3) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hr1
  have hs3 : c 0 - c 1 + c 2 - c 3 = 0 := by
    have hmul : (√d / 2) * (c 0 - c 1 + c 2 - c 3) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hr2
  have hc0 : c 0 = 0 := by linarith
  have hc1 : c 1 = 0 := by linarith
  have hc2 : c 2 = 0 := by linarith
  have hc3 : c 3 = 0 := by linarith
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact hc3

private lemma sqNormVec_norm_sub_tendsto {a : ℝ} (i : Fin 4) :
    Filter.Tendsto (fun d => ‖sqNormVec a d i - sqNormVec a 0 i‖) (nhds 0) (nhds 0) := by
  have hc : ∀ m : Fin 4, Filter.Tendsto (fun d : ℝ => (sqNormVec a d i).ofLp m)
      (nhds 0) (nhds ((sqNormVec a 0 i).ofLp m)) := by
    intro m
    have h0 : Filter.Tendsto (fun d : ℝ => √(4 * a + d) / 2) (nhds 0) (nhds (√(4 * a + 0) / 2)) :=
      ((Real.continuous_sqrt.comp (continuous_const.add continuous_id)).div_const 2).continuousAt.tendsto
    have h1 : Filter.Tendsto (fun d : ℝ => √(2 * (1 - a) - d) / √2) (nhds 0)
        (nhds (√(2 * (1 - a) - 0) / √2)) :=
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).div_const √2).continuousAt.tendsto
    have h2 : Filter.Tendsto (fun d : ℝ => √d / 2) (nhds 0) (nhds (√0 / 2)) :=
      (Real.continuous_sqrt.div_const 2).continuousAt.tendsto
    fin_cases i <;> fin_cases m <;> dsimp only <;>
      simp only [sqNormVec, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    all_goals first
      | exact h0
      | exact h1
      | exact h1.neg
      | exact h2
      | exact h2.neg
      | exact tendsto_const_nhds
  have hsq : Filter.Tendsto (fun d => ‖sqNormVec a d i - sqNormVec a 0 i‖ ^ 2) (nhds 0) (nhds 0) := by
    have hsum : Filter.Tendsto (fun d : ℝ =>
        ∑ m : Fin 4, ((sqNormVec a d i).ofLp m - (sqNormVec a 0 i).ofLp m) ^ 2)
        (nhds 0) (nhds (∑ _m : Fin 4, (0 : ℝ))) := by
      refine tendsto_finset_sum Finset.univ fun m _ => ?_
      have hs := ((hc m).sub_const ((sqNormVec a 0 i).ofLp m)).pow 2
      simpa using hs
    have hsum' : Filter.Tendsto (fun d => ‖sqNormVec a d i - sqNormVec a 0 i‖ ^ 2)
        (nhds 0) (nhds (∑ _m : Fin 4, (0 : ℝ))) := by
      refine hsum.congr fun d => ?_
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      simp [RCLike.inner_apply, conj_trivial, sq]
    simpa using hsum'
  have hsqrt := hsq.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun d => ?_
  exact Real.sqrt_sq (norm_nonneg _)

private lemma measure_body₀_square {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    let body₀ : Set ↑(Metric.sphere (0 : E4) 1) :=
      {y | ∀ i : Fin 4, 0 ≤ inner ℝ (sqNormVec a 0 i) (y : E4)}
    MeasureTheory.volume.toSphere.real body₀ =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi) * (4 * Real.arccos (-a) - 2 * Real.pi) := by
  intro body₀
  let mVec : E4 := WithLp.toLp 2 ![0, 1 / √2, 1 / √2, 0]
  have hmNorm : ‖mVec‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow, ← real_inner_self_eq_norm_sq,
      PiLp.inner_apply]
    simp [mVec, Fin.sum_univ_four]
    norm_num
  let mS : ↑(Metric.sphere (0 : E4) 1) :=
    ⟨mVec, by simpa [Metric.mem_sphere, dist_zero_right] using hmNorm⟩
  let mNeg : ↑(Metric.sphere (0 : E4) 1) :=
    ⟨-mVec, by simpa [Metric.mem_sphere, dist_zero_right, norm_neg] using hmNorm⟩
  have hnorm0 : ∀ i : Fin 4, ‖sqNormVec a 0 i‖ = 1 :=
    fun i => sqNormVec_norm ha0 le_rfl (by linarith) i
  let uS : Fin 4 → ↑(Metric.sphere (0 : E4) 1) := fun i =>
    ⟨sqNormVec a 0 i, by simpa [Metric.mem_sphere, dist_zero_right] using hnorm0 i⟩
  let w1 : Fin 3 → ↑(Metric.sphere (0 : E4) 1) := ![uS 2, uS 3, mS]
  let w2 : Fin 3 → ↑(Metric.sphere (0 : E4) 1) := ![uS 0, uS 1, mNeg]
  have hr1_eq : √(2 * (1 - a) - 0) / √2 = √(1 - a) := by
    rw [sub_zero, ← Real.sqrt_div (by linarith)]
    congr 1; ring
  have hdecomp : body₀ = triSusp4 w1 ∪ triSusp4 w2 := by
    have hr1_nonneg : 0 ≤ √(2 * (1 - a) - 0) := Real.sqrt_nonneg _
    have hid : ∀ x : E4,
        (inner ℝ (sqNormVec a 0 0) x =
          inner ℝ (sqNormVec a 0 3) x + √(2 * (1 - a) - 0) * inner ℝ mVec x) ∧
        (inner ℝ (sqNormVec a 0 1) x =
          inner ℝ (sqNormVec a 0 2) x + √(2 * (1 - a) - 0) * inner ℝ mVec x) := by
      intro x
      constructor <;>
        · simp only [PiLp.inner_apply, sqNormVec, mVec, Fin.sum_univ_four, RCLike.inner_apply,
            conj_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
            Real.sqrt_zero]
          field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
          ring
    ext y
    simp only [body₀, Set.mem_ofPred_eq, Set.mem_union, triSusp4]
    constructor
    · intro hy
      by_cases hm : 0 ≤ inner ℝ mVec (y : E4)
      · left
        intro k
        fin_cases k
        · exact hy 2
        · exact hy 3
        · exact hm
      · right
        intro k
        fin_cases k
        · exact hy 0
        · exact hy 1
        · change 0 ≤ inner ℝ (-mVec) (y : E4)
          rw [inner_neg_left]
          linarith
    · rintro (h1 | h2)
      · have hy2 : 0 ≤ inner ℝ (sqNormVec a 0 2) (y : E4) := h1 0
        have hy3 : 0 ≤ inner ℝ (sqNormVec a 0 3) (y : E4) := h1 1
        have hym : 0 ≤ inner ℝ mVec (y : E4) := h1 2
        have hi0 : 0 ≤ inner ℝ (sqNormVec a 0 0) (y : E4) := by
          rw [(hid (y : E4)).1]
          exact add_nonneg hy3 (mul_nonneg hr1_nonneg hym)
        have hi1 : 0 ≤ inner ℝ (sqNormVec a 0 1) (y : E4) := by
          rw [(hid (y : E4)).2]
          exact add_nonneg hy2 (mul_nonneg hr1_nonneg hym)
        intro i
        fin_cases i
        · exact hi0
        · exact hi1
        · exact hy2
        · exact hy3
      · have hy0 : 0 ≤ inner ℝ (sqNormVec a 0 0) (y : E4) := h2 0
        have hy1 : 0 ≤ inner ℝ (sqNormVec a 0 1) (y : E4) := h2 1
        have hym : inner ℝ mVec (y : E4) ≤ 0 := by
          have := h2 2
          change 0 ≤ inner ℝ (-mVec) (y : E4) at this
          rw [inner_neg_left] at this
          linarith
        have hi2 : 0 ≤ inner ℝ (sqNormVec a 0 2) (y : E4) := by
          have hhid := (hid (y : E4)).2
          nlinarith [hr1_nonneg, hym, hhid]
        have hi3 : 0 ≤ inner ℝ (sqNormVec a 0 3) (y : E4) := by
          have hhid := (hid (y : E4)).1
          nlinarith [hr1_nonneg, hym, hhid]
        intro i
        fin_cases i
        · exact hy0
        · exact hy1
        · exact hi2
        · exact hi3
  have hinter_null : MeasureTheory.volume.toSphere (triSusp4 w1 ∩ triSusp4 w2) = 0 := by
    have hsub : triSusp4 w1 ∩ triSusp4 w2 ⊆ {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ mVec (y : E4)| ≤ 0} := by
      rintro y ⟨hy1, hy2⟩
      have hm1 : 0 ≤ inner ℝ mVec (y : E4) := hy1 2
      have hm2 : 0 ≤ inner ℝ (-mVec) (y : E4) := hy2 2
      rw [inner_neg_left] at hm2
      have hz : inner ℝ mVec (y : E4) = 0 := by linarith
      simp [hz]
    have hzero : MeasureTheory.volume.toSphere.real
        {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ mVec (y : E4)| ≤ 0} ≤ 0 := by
      simpa using toSphere_slab_bound hmNorm le_rfl
    have hfin : MeasureTheory.volume.toSphere
        {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ mVec (y : E4)| ≤ 0} ≠ ⊤ :=
      measure_ne_top _ _
    have hreal : MeasureTheory.volume.toSphere.real
        {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ mVec (y : E4)| ≤ 0} = 0 :=
      le_antisymm hzero ENNReal.toReal_nonneg
    have hmeas0 : MeasureTheory.volume.toSphere
        {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ mVec (y : E4)| ≤ 0} = 0 :=
      (MeasureTheory.measureReal_eq_zero_iff hfin).mp hreal
    exact measure_mono_null hsub hmeas0
  have hm1 : MeasurableSet (triSusp4 w1) := by
    have hcl : IsClosed (triSusp4 w1) := by
      have heq : triSusp4 w1 = ⋂ k : Fin 3, {y : ↑(Metric.sphere (0 : E4) 1) | 0 ≤ inner ℝ (w1 k : E4) (y : E4)} := by
        ext y; simp [triSusp4]
      rw [heq]
      exact isClosed_iInter fun k =>
        isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
    exact hcl.measurableSet
  have hm2 : MeasurableSet (triSusp4 w2) := by
    have hcl : IsClosed (triSusp4 w2) := by
      have heq : triSusp4 w2 = ⋂ k : Fin 3, {y : ↑(Metric.sphere (0 : E4) 1) | 0 ≤ inner ℝ (w2 k : E4) (y : E4)} := by
        ext y; simp [triSusp4]
      rw [heq]
      exact isClosed_iInter fun k =>
        isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
    exact hcl.measurableSet
  have hsum : MeasureTheory.volume.toSphere.real body₀ =
      MeasureTheory.volume.toSphere.real (triSusp4 w1) +
        MeasureTheory.volume.toSphere.real (triSusp4 w2) := by
    rw [hdecomp]
    exact measureReal_union_inter_null _ hm1 hm2 hinter_null
  have hin := sqNormVec_inner ha0 le_rfl (by linarith)
  have htri_d : 2 * Real.arccos (√((1 - a) / 2)) = Real.arccos (-a) := by
    set α := Real.arccos (√((1 - a) / 2))
    have hnonneg : 0 ≤ √((1 - a) / 2) := Real.sqrt_nonneg _
    have hle1 : √((1 - a) / 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith
    have hα0 : 0 ≤ α := Real.arccos_nonneg _
    have hαpi : 2 * α ≤ Real.pi := by
      have hge0 : Real.cos (Real.pi / 2) ≤ Real.cos α := by
        rw [Real.cos_pi_div_two, Real.cos_arccos (by linarith) hle1]
        exact hnonneg
      have hle_pi2 : α ≤ Real.pi / 2 := by
        by_contra! hgt
        have hlt := Real.strictAntiOn_cos ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          ⟨hα0, Real.arccos_le_pi _⟩ hgt
        linarith
      linarith
    have hcos : Real.cos (2 * α) = -a := by
      rw [Real.cos_two_mul, Real.cos_arccos (by linarith) hle1,
        Real.sq_sqrt (by linarith)]
      ring
    rw [← hcos]
    exact (Real.arccos_cos (by linarith) hαpi).symm
  have hd_u3m : -inner ℝ (uS 3 : E4) (mS : E4) = √((1 - a) / 2) := by
    change -inner ℝ (sqNormVec a 0 3) mVec = _
    rw [PiLp.inner_apply]
    simp only [sqNormVec, mVec, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr1_eq]
    have hs2 : √((1 - a) / 2) = √(1 - a) / √2 := by
      rw [Real.sqrt_div (by linarith)]
    rw [hs2]
    ring
  have hd_mu2 : -inner ℝ (mS : E4) (uS 2 : E4) = √((1 - a) / 2) := by
    change -inner ℝ mVec (sqNormVec a 0 2) = _
    rw [PiLp.inner_apply]
    simp only [sqNormVec, mVec, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr1_eq]
    have hs2 : √((1 - a) / 2) = √(1 - a) / √2 := by
      rw [Real.sqrt_div (by linarith)]
    rw [hs2]
    ring
  have hd_u1mn : -inner ℝ (uS 1 : E4) (mNeg : E4) = √((1 - a) / 2) := by
    change -inner ℝ (sqNormVec a 0 1) (-mVec) = _
    rw [inner_neg_right, neg_neg, PiLp.inner_apply]
    simp only [sqNormVec, mVec, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr1_eq]
    have hs2 : √((1 - a) / 2) = √(1 - a) / √2 := by
      rw [Real.sqrt_div (by linarith)]
    rw [hs2]
    ring
  have hd_mnu0 : -inner ℝ (mNeg : E4) (uS 0 : E4) = √((1 - a) / 2) := by
    change -inner ℝ (-mVec) (sqNormVec a 0 0) = _
    rw [inner_neg_left, neg_neg, PiLp.inner_apply]
    simp only [sqNormVec, mVec, Fin.sum_univ_four, RCLike.inner_apply, conj_trivial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hr1_eq]
    have hs2 : √((1 - a) / 2) = √(1 - a) / √2 := by
      rw [Real.sqrt_div (by linarith)]
    rw [hs2]
    ring
  have hw1_val : MeasureTheory.volume.toSphere.real (triSusp4 w1) =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi) * (2 * Real.arccos (-a) - Real.pi) := by
    rw [toSphere_real_triSusp4]
    have h23 : -inner ℝ (w1 0 : E4) (w1 1 : E4) = -a := by
      change -inner ℝ (sqNormVec a 0 2) (sqNormVec a 0 3) = -a
      rw [hin.2.2.2.2.2]
    have h3m : -inner ℝ (w1 1 : E4) (w1 2 : E4) = √((1 - a) / 2) := hd_u3m
    have hm2 : -inner ℝ (w1 2 : E4) (w1 0 : E4) = √((1 - a) / 2) := hd_mu2
    rw [h23, h3m, hm2]
    congr 1
    linarith [htri_d]
  have hw2_val : MeasureTheory.volume.toSphere.real (triSusp4 w2) =
      MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (4 * Real.pi) * (2 * Real.arccos (-a) - Real.pi) := by
    rw [toSphere_real_triSusp4]
    have h01 : -inner ℝ (w2 0 : E4) (w2 1 : E4) = -a := by
      change -inner ℝ (sqNormVec a 0 0) (sqNormVec a 0 1) = -a
      rw [hin.1]
    have h1m : -inner ℝ (w2 1 : E4) (w2 2 : E4) = √((1 - a) / 2) := hd_u1mn
    have hm0 : -inner ℝ (w2 2 : E4) (w2 0 : E4) = √((1 - a) / 2) := hd_mnu0
    rw [h01, h1m, hm0]
    congr 1
    linarith [htri_d]
  rw [hsum, hw1_val, hw2_val]
  ring

private lemma tendsto_gaussVolGram_sqVec_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Filter.Tendsto (fun d => gaussVolGram (sqVec a d)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (8 * Real.pi)) * (4 * Real.arccos (-a) - 2 * Real.pi))) := by
  let body₀ : Set ↑(Metric.sphere (0 : E4) 1) :=
    {y | ∀ i : Fin 4, 0 ≤ inner ℝ (sqNormVec a 0 i) (y : E4)}
  have hbody0 := measure_body₀_square ha0 ha1
  change MeasureTheory.volume.toSphere.real body₀ = _ at hbody0
  have hdiff_bound : ∀ {d : ℝ}, 0 < d → d < 2 * (1 - a) → ∀ {ε : ℝ}, 0 ≤ ε →
      (∀ i : Fin 4, ‖sqNormVec a d i - sqNormVec a 0 i‖ ≤ ε) →
      |2 * gaussVolGram (sqVec a d) - MeasureTheory.volume.toSphere.real body₀| ≤ 256 * ε := by
    intro d hd0 hd1 ε hε hnorm
    let Td : SphericalTetrahedron :=
      ⟨sqNormVec a d, fun i => sqNormVec_norm ha0 hd0.le hd1 i,
        sqNormVec_independent ha0 hd0 hd1⟩
    have hgp : Td.gramPoint = sqVec a d := by
      have hin := sqNormVec_inner ha0 hd0.le hd1
      ext k
      fin_cases k
      · exact hin.1
      · exact hin.2.1
      · exact hin.2.2.1
      · exact hin.2.2.2.1
      · exact hin.2.2.2.2.1
      · exact hin.2.2.2.2.2
    have hvol1 := Td.volume_eq_sphereScale_mul_toSphere
    have hvol2 := Td.volume_eq_two_sphereScale_mul_gaussVolGram
    rw [hgp] at hvol2
    have hs_pos : sphereScale 3 ≠ 0 := (sphereScale_pos (d := 3) (by decide)).ne'
    have h2g : 2 * gaussVolGram (sqVec a d) =
        MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' Td.body) := by
      have hmul : sphereScale 3 * (2 * gaussVolGram (sqVec a d)) =
          sphereScale 3 * MeasureTheory.volume.toSphere.real (Subtype.val ⁻¹' Td.body) := by
        linarith [hvol1, hvol2]
      exact mul_left_cancel₀ hs_pos hmul
    rw [h2g]
    let Bd : Set ↑(Metric.sphere (0 : E4) 1) := Subtype.val ⁻¹' Td.body
    let U : Set ↑(Metric.sphere (0 : E4) 1) :=
      ⋃ i : Fin 4, {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ (sqNormVec a 0 i) (y : E4)| ≤ ε}
    have hdiff1 : Bd \ body₀ ⊆ U := by
      rintro y ⟨hy_bd, hy_n0⟩
      simp only [body₀, Set.mem_ofPred_eq, not_forall, not_le] at hy_n0
      rcases hy_n0 with ⟨i, hi_neg⟩
      have hi_nonneg : 0 ≤ inner ℝ (sqNormVec a d i) (y : E4) := hy_bd.2 i
      have hy1 : ‖(y : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
      have hsub : |inner ℝ (sqNormVec a 0 i) (y : E4)| ≤
          |inner ℝ (sqNormVec a d i - sqNormVec a 0 i) (y : E4)| := by
        rw [inner_sub_left, abs_of_neg hi_neg]
        linarith [le_abs_self (inner ℝ (sqNormVec a d i) (y : E4) - inner ℝ (sqNormVec a 0 i) (y : E4))]
      have hcs : |inner ℝ (sqNormVec a d i - sqNormVec a 0 i) (y : E4)| ≤ ε := by
        calc |inner ℝ (sqNormVec a d i - sqNormVec a 0 i) (y : E4)|
            ≤ ‖sqNormVec a d i - sqNormVec a 0 i‖ * ‖(y : E4)‖ := abs_real_inner_le_norm _ _
          _ ≤ ε * 1 := mul_le_mul (hnorm i) (by linarith [hy1]) (norm_nonneg _) hε
          _ = ε := mul_one ε
      exact Set.mem_iUnion.mpr ⟨i, le_trans hsub hcs⟩
    have hdiff2 : body₀ \ Bd ⊆ U := by
      rintro y ⟨hy_0, hy_nbd⟩
      have hy1_mem : (y : E4) ∈ Metric.sphere (0 : E4) 1 := y.2
      have hy_not : ¬ ∀ i : Fin 4, 0 ≤ inner ℝ (sqNormVec a d i) (y : E4) := fun h =>
        hy_nbd ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hy1_mem, h⟩
      push Not at hy_not
      rcases hy_not with ⟨i, hi_neg⟩
      have hi_nonneg : 0 ≤ inner ℝ (sqNormVec a 0 i) (y : E4) := hy_0 i
      have hy1 : ‖(y : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
      have hsub : |inner ℝ (sqNormVec a 0 i) (y : E4)| ≤
          |inner ℝ (sqNormVec a d i - sqNormVec a 0 i) (y : E4)| := by
        rw [inner_sub_left, abs_of_nonneg hi_nonneg]
        have : inner ℝ (sqNormVec a 0 i) (y : E4) ≤ -(inner ℝ (sqNormVec a d i) (y : E4) -
            inner ℝ (sqNormVec a 0 i) (y : E4)) := by linarith
        exact this.trans (neg_le_abs _)
      have hcs : |inner ℝ (sqNormVec a d i - sqNormVec a 0 i) (y : E4)| ≤ ε := by
        calc |inner ℝ (sqNormVec a d i - sqNormVec a 0 i) (y : E4)|
            ≤ ‖sqNormVec a d i - sqNormVec a 0 i‖ * ‖(y : E4)‖ := abs_real_inner_le_norm _ _
          _ ≤ ε * 1 := mul_le_mul (hnorm i) (by linarith [hy1]) (norm_nonneg _) hε
          _ = ε := mul_one ε
      exact Set.mem_iUnion.mpr ⟨i, le_trans hsub hcs⟩
    let ν : MeasureTheory.Measure ↑(Metric.sphere (0 : E4) 1) := MeasureTheory.volume.toSphere
    have hU_le : ν.real U ≤ 256 * ε := by
      have hterm : ∀ i : Fin 4,
          ν.real {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ (sqNormVec a 0 i) (y : E4)| ≤ ε} ≤ 64 * ε :=
        fun i => toSphere_slab_bound (sqNormVec_norm ha0 le_rfl (by linarith) i) hε
      calc ν.real U ≤ ∑ i : Fin 4,
            ν.real {y : ↑(Metric.sphere (0 : E4) 1) | |inner ℝ (sqNormVec a 0 i) (y : E4)| ≤ ε} :=
          MeasureTheory.measureReal_iUnion_fintype_le _
        _ ≤ ∑ _i : Fin 4, (64 * ε) := Finset.sum_le_sum fun i _ => hterm i
        _ = 256 * ε := by simp; ring
    have hsub1 : ν.real Bd - ν.real body₀ ≤ ν.real U := by
      have hcov : Bd ⊆ (Bd \ body₀) ∪ body₀ := fun y hy => by
        by_cases h : y ∈ body₀ <;> [exact Or.inr h; exact Or.inl ⟨hy, h⟩]
      have hle : ν.real Bd ≤ ν.real (Bd \ body₀) + ν.real body₀ :=
        (MeasureTheory.measureReal_mono hcov).trans (MeasureTheory.measureReal_union_le _ _)
      have hleU : ν.real (Bd \ body₀) ≤ ν.real U := MeasureTheory.measureReal_mono hdiff1
      linarith
    have hsub2 : ν.real body₀ - ν.real Bd ≤ ν.real U := by
      have hcov : body₀ ⊆ (body₀ \ Bd) ∪ Bd := fun y hy => by
        by_cases h : y ∈ Bd <;> [exact Or.inr h; exact Or.inl ⟨hy, h⟩]
      have hle : ν.real body₀ ≤ ν.real (body₀ \ Bd) + ν.real Bd :=
        (MeasureTheory.measureReal_mono hcov).trans (MeasureTheory.measureReal_union_le _ _)
      have hleU : ν.real (body₀ \ Bd) ≤ ν.real U := MeasureTheory.measureReal_mono hdiff2
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have ht2 : Filter.Tendsto (fun d => 2 * gaussVolGram (sqVec a d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (MeasureTheory.volume.toSphere.real body₀)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    let ε := η / 512
    have hε : 0 < ε := by positivity
    have hball : ∀ i : Fin 4, ∀ᶠ d in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖sqNormVec a d i - sqNormVec a 0 i‖ ≤ ε := fun i => by
      have hten := (Metric.tendsto_nhds.mp (sqNormVec_norm_sub_tendsto (a := a) i) ε hε).filter_mono
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      filter_upwards [hten] with d hd
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hd
      exact hd.le
    have hd_win : ∀ᶠ d in nhdsWithin (0 : ℝ) (Set.Ioi 0), d ∈ Set.Ioo 0 (2 * (1 - a)) :=
      mem_nhdsWithin.mpr ⟨Set.Iio (2 * (1 - a)), isOpen_Iio,
        Set.mem_Iio.mpr (by linarith [ha1]), fun _ h => ⟨h.2, h.1⟩⟩
    filter_upwards [hd_win, hball 0, hball 1, hball 2, hball 3] with d hd hn0 hn1 hn2 hn3
    have hnorm : ∀ i : Fin 4, ‖sqNormVec a d i - sqNormVec a 0 i‖ ≤ ε := fun i => by
      fin_cases i <;> assumption
    have hbd := hdiff_bound hd.1 hd.2 hε.le hnorm
    rw [Real.dist_eq]
    calc |2 * gaussVolGram (sqVec a d) - MeasureTheory.volume.toSphere.real body₀| ≤ 256 * ε := hbd
      _ = η / 2 := by dsimp [ε]; ring
      _ < η := by linarith
  have hhalf := ht2.const_mul (1 / 2 : ℝ)
  have hlim : (1 / 2 : ℝ) * MeasureTheory.volume.toSphere.real body₀ =
      (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (8 * Real.pi)) * (4 * Real.arccos (-a) - 2 * Real.pi) := by
    rw [hbody0]; ring
  rw [hlim] at hhalf
  refine hhalf.congr fun d => by ring

private lemma arccos_ge_sqrt_two_one_sub {u : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 1) :
    √(2 * (1 - u)) ≤ Real.arccos u := by
  set θ := Real.arccos u
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg u
  have hθpi : θ ≤ Real.pi := Real.arccos_le_pi u
  have hcos : Real.cos θ = u := Real.cos_arccos hu1 hu2
  have hhalf0 : 0 ≤ θ / 2 := by linarith
  have hhalfpi : θ / 2 ≤ Real.pi := by linarith
  have hsin_le : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le hhalf0
  have hsin0 : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 hhalfpi
  have hid : 1 - u = 2 * Real.sin (θ / 2) ^ 2 := by
    have hc := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring, hcos] at hc
    linarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hsq : 2 * (1 - u) ≤ θ ^ 2 := by nlinarith
  exact Real.sqrt_le_iff.mpr ⟨hθ0, hsq⟩

private lemma symUnitAdj_sqVec_entries (a t : ℝ) :
    let s2 := Sphere3.squareSuspensionPolarDet a (2 * a - 1 + t)
    symUnitAdj (sqVec a t) 0 0 = s2 ∧
    symUnitAdj (sqVec a t) 1 1 = s2 ∧
    symUnitAdj (sqVec a t) 2 2 = s2 ∧
    symUnitAdj (sqVec a t) 3 3 = s2 ∧
    symUnitAdj (sqVec a t) 1 3 = s2 - (4 * a + t) * t * (2 * (1 - a) - t) ∧
    symUnitAdj (sqVec a t) 0 2 = s2 - (4 * a + t) * t * (2 * (1 - a) - t) := by
  dsimp [symUnitAdj, sqVec, Sphere3.squareSuspensionPolarDet]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

private lemma gaussVolFDeriv_sqVec_d_lb {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1 - a) :
    (1 / 2 : ℝ) * √(2 * a * (1 - a)) * √t ≤
      gaussVolFDeriv (sqVec a t) ![0, 1, 0, 0, 1, 0] := by
  have hx := sqVec_mem_gramOpen ha0 ha1 ht0 (by linarith)
  have hsum : gaussVolFDeriv (sqVec a t) ![0, 1, 0, 0, 1, 0] =
      gaussVolFDeriv (sqVec a t) (Pi.single 1 1) +
        gaussVolFDeriv (sqVec a t) (Pi.single 4 1) := by
    have hv : (![0, 1, 0, 0, 1, 0] : Fin 6 → ℝ) = Pi.single 1 1 + Pi.single 4 1 := by
      ext k; fin_cases k <;> simp [Pi.single_apply]
    rw [hv, map_add]
  rw [hsum, gaussVolFDeriv_coord _ 1, gaussVolFDeriv_coord _ 4]
  have hopp1 : oppIdx 1 = (1, 3) := rfl
  have hopp4 : oppIdx 4 = (0, 2) := rfl
  rw [hopp1, hopp4]
  dsimp only
  set s2 := Sphere3.squareSuspensionPolarDet a (2 * a - 1 + t)
  have hadj := symUnitAdj_sqVec_entries a t
  dsimp only at hadj
  have hs2_pos : 0 < s2 := Sphere3.squareSuspensionPolarDet_pos a t ha0 ha1 ht0 (by linarith)
  have hs2_le4 : s2 ≤ 4 := by
    have hfac := Sphere3.squareSuspensionPolarDet_factor a (2 * a - 1 + t)
    dsimp [s2]; rw [hfac]
    have h1 : 0 ≤ 1 - (2 * a - 1 + t) := by linarith
    have h2 : 1 - (2 * a - 1 + t) ≤ 2 := by linarith
    have h3 : 0 ≤ 1 + (2 * a - 1 + t) - 2 * a ^ 2 := by nlinarith
    have h4 : 1 + (2 * a - 1 + t) - 2 * a ^ 2 ≤ 2 := by nlinarith
    nlinarith
  have hjac := symUnitAdj_jacobi (sqVec a t) 1
  dsimp [pairIdx, oppIdx] at hjac
  have hdet_pos : 0 < (symUnitMat (sqVec a t)).det := hx.2.2
  have hb_lt1 : |2 * a - 1 + t| < 1 := by
    have := gramOpen_offdiag_abs_lt_one hx 1
    simpa [sqVec] using this
  have h1mb2_pos : 0 < 1 - (2 * a - 1 + t) ^ 2 := by nlinarith [abs_lt.mp hb_lt1]
  have hb_sq_nonneg : 0 ≤ (2 * a - 1 + t) ^ 2 := sq_nonneg _
  have hsqrt_b_le1 : √(1 - (2 * a - 1 + t) ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hsqrt_b_pos : 0 < √(1 - (2 * a - 1 + t) ^ 2) := Real.sqrt_pos.mpr h1mb2_pos
  have hinv_ge1 : 1 ≤ (√(1 - (2 * a - 1 + t) ^ 2))⁻¹ :=
    (one_le_inv₀ hsqrt_b_pos).mpr hsqrt_b_le1
  have hrat_sq : (symUnitAdj (sqVec a t) 1 3) ^ 2 ≤ s2 ^ 2 := by
    rw [hadj.2.1, hadj.2.2.2.1] at hjac
    have hsym_mat : symUnitMat (sqVec a t) 0 2 = 2 * a - 1 + t := by rfl
    rw [hsym_mat] at hjac
    nlinarith
  have hu_mem : -1 ≤ symUnitAdj (sqVec a t) 1 3 / s2 ∧ symUnitAdj (sqVec a t) 1 3 / s2 ≤ 1 := by
    have habs : |symUnitAdj (sqVec a t) 1 3 / s2| ≤ 1 := by
      rw [abs_le] at *; constructor <;>
        [exact le_div_iff₀ hs2_pos |>.mpr (by nlinarith);
         exact div_le_iff₀ hs2_pos |>.mpr (by nlinarith)]
    exact abs_le.mp habs
  have hsqrt_s2 : √(s2 * s2) = s2 := Real.sqrt_mul_self hs2_pos.le
  have h1mu : a * (1 - a) * t ≤ 1 - symUnitAdj (sqVec a t) 1 3 / s2 := by
    rw [hadj.2.2.2.2.1]
    have heq : 1 - (s2 - (4 * a + t) * t * (2 * (1 - a) - t)) / s2 =
        (4 * a + t) * t * (2 * (1 - a) - t) / s2 := by
      field_simp [hs2_pos.ne']; ring
    rw [heq, le_div_iff₀ hs2_pos]
    have hnum_ge : 4 * a * (1 - a) * t ≤ (4 * a + t) * t * (2 * (1 - a) - t) := by
      have h4a : 4 * a * t ≤ (4 * a + t) * t := by nlinarith
      have h21a : 1 - a ≤ 2 * (1 - a) - t := by linarith
      calc 4 * a * (1 - a) * t = (4 * a * t) * (1 - a) := by ring
        _ ≤ ((4 * a + t) * t) * (2 * (1 - a) - t) :=
            mul_le_mul h4a h21a (by linarith) (by positivity)
    calc a * (1 - a) * t * s2 ≤ a * (1 - a) * t * 4 :=
          mul_le_mul_of_nonneg_left hs2_le4 (by positivity)
      _ = 4 * a * (1 - a) * t := by ring
      _ ≤ (4 * a + t) * t * (2 * (1 - a) - t) := hnum_ge
  have harc_ge : √(2 * a * (1 - a)) * √t ≤ Real.arccos (symUnitAdj (sqVec a t) 1 3 / s2) := by
    calc √(2 * a * (1 - a)) * √t = √(2 * a * (1 - a) * t) := by
          rw [← Real.sqrt_mul (by positivity)]
      _ ≤ √(2 * (1 - symUnitAdj (sqVec a t) 1 3 / s2)) := by
          apply Real.sqrt_le_sqrt; linarith
      _ ≤ Real.arccos (symUnitAdj (sqVec a t) 1 3 / s2) :=
          arccos_ge_sqrt_two_one_sub hu_mem.1 hu_mem.2
  have hx1_eq : sqVec a t 1 = 2 * a - 1 + t := rfl
  have hx4_eq : sqVec a t 4 = 2 * a - 1 + t := rfl
  rw [hx1_eq, hx4_eq, hadj.1, hadj.2.1, hadj.2.2.1, hadj.2.2.2.1, hsqrt_s2,
    hadj.2.2.2.2.2, ← hadj.2.2.2.2.1]
  have hterm : (1 / 4 : ℝ) * √(2 * a * (1 - a)) * √t ≤
      1 / 4 * Real.arccos (symUnitAdj (sqVec a t) 1 3 / s2) / √(1 - (2 * a - 1 + t) ^ 2) := by
    rw [div_eq_mul_inv]
    have h1 : 0 ≤ (1 / 4 : ℝ) * Real.arccos (symUnitAdj (sqVec a t) 1 3 / s2) := by
      have := Real.arccos_nonneg (symUnitAdj (sqVec a t) 1 3 / s2)
      positivity
    calc (1 / 4 : ℝ) * √(2 * a * (1 - a)) * √t
        = ((1 / 4 : ℝ) * (√(2 * a * (1 - a)) * √t)) * 1 := by ring
      _ ≤ ((1 / 4 : ℝ) * Real.arccos (symUnitAdj (sqVec a t) 1 3 / s2)) *
            (√(1 - (2 * a - 1 + t) ^ 2))⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_left harc_ge (by positivity)) hinv_ge1
            (by positivity) (by positivity)
  linarith

private lemma gaussVolFDeriv_sqVec_a_bound {a d a_lo a_hi : ℝ}
    (halo : 0 < a_lo) (ha_lo : a_lo ≤ a) (ha_hi : a ≤ a_hi) (hahi : a_hi < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1 - a_hi) :
    |gaussVolFDeriv (sqVec a d) ![1, 2, 1, 1, 2, 1]| ≤
      2 * Real.pi / √(min (1 - a_hi) ((1 - a_hi) * (2 * a_lo))) := by
  let c := min (1 - a_hi) ((1 - a_hi) * (2 * a_lo))
  have hc_pos : 0 < c := lt_min (by linarith) (mul_pos (by linarith) (by linarith))
  have hv : (![1, 2, 1, 1, 2, 1] : Fin 6 → ℝ) =
      ∑ k : Fin 6, (![1, 2, 1, 1, 2, 1] : Fin 6 → ℝ) k • Pi.single k (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : gaussVolFDeriv (sqVec a d) ![1, 2, 1, 1, 2, 1] =
      ∑ k : Fin 6, (![1, 2, 1, 1, 2, 1] : Fin 6 → ℝ) k *
        gaussVolFDeriv (sqVec a d) (Pi.single k 1) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, smul_eq_mul]
  have hterm : ∀ k : Fin 6,
      |gaussVolFDeriv (sqVec a d) (Pi.single k 1)| ≤ Real.pi / 4 / √c := by
    intro k
    rw [gaussVolFDeriv_coord _ k]
    have hck : c ≤ 1 - sqVec a d k ^ 2 := by
      have ha_sq : 1 - a_hi ≤ 1 - a ^ 2 := by nlinarith
      have hb_sq : (1 - a_hi) * (2 * a_lo) ≤ 1 - (2 * a - 1 + d) ^ 2 := by
        have h1mb : 1 - a_hi ≤ 1 - (2 * a - 1 + d) := by linarith
        have h1pb : 2 * a_lo ≤ 1 + (2 * a - 1 + d) := by linarith
        nlinarith
      fin_cases k <;> simp [sqVec]
      all_goals first
        | exact (min_le_left _ _).trans ha_sq
        | exact (min_le_right _ _).trans hb_sq
    have hsqrt_le : √c ≤ √(1 - sqVec a d k ^ 2) := Real.sqrt_le_sqrt hck
    have hsqrt_pos : 0 < √(1 - sqVec a d k ^ 2) := lt_of_lt_of_le (Real.sqrt_pos.mpr hc_pos) hsqrt_le
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) (Real.arccos_nonneg _)) hsqrt_pos.le)]
    calc 1 / 4 * Real.arccos _ / √(1 - sqVec a d k ^ 2)
        ≤ (Real.pi / 4) / √(1 - sqVec a d k ^ 2) := by
          gcongr; linarith [Real.arccos_le_pi
            (symUnitAdj (sqVec a d) (oppIdx k).1 (oppIdx k).2 /
              √(symUnitAdj (sqVec a d) (oppIdx k).1 (oppIdx k).1 *
                symUnitAdj (sqVec a d) (oppIdx k).2 (oppIdx k).2))]
      _ ≤ (Real.pi / 4) / √c := by
          gcongr
  rw [hsum]
  calc |∑ k : Fin 6, (![1, 2, 1, 1, 2, 1] : Fin 6 → ℝ) k *
        gaussVolFDeriv (sqVec a d) (Pi.single k 1)|
      ≤ ∑ k : Fin 6, |![1, 2, 1, 1, 2, 1] k * gaussVolFDeriv (sqVec a d) (Pi.single k 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin 6, |![1, 2, 1, 1, 2, 1] k| * |gaussVolFDeriv (sqVec a d) (Pi.single k 1)| := by
        simp [abs_mul]
    _ ≤ ∑ k : Fin 6, |![1, 2, 1, 1, 2, 1] k| * (Real.pi / 4 / √c) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (hterm k) (abs_nonneg _)
    _ = (∑ k : Fin 6, |![1, 2, 1, 1, 2, 1] k|) * (Real.pi / 4 / √c) := by
        rw [Finset.sum_mul]
    _ = 2 * Real.pi / √c := by
        have h8 : ∑ k : Fin 6, |(![1, 2, 1, 1, 2, 1] : Fin 6 → ℝ) k| = 8 := by
          rw [Fin.sum_univ_six]; norm_num
        rw [h8]
        ring

private lemma sqVec_area_diff_bound {alo a0 ahi d ad totalStdArea CA ca : ℝ}
    (halo0 : 0 < alo) (halo : alo < a0) (ha0hi : a0 < ahi) (hahi1 : ahi < 1)
    (hd0 : 0 < d) (hd_box : d ≤ 1 - ahi)
    (had_mem : ad ∈ Set.Icc alo ahi) (had_area : stdAreaGram (sqVec ad d) = totalStdArea)
    (harea0 : stdAreaGram (sqVec a0 0) = totalStdArea)
    (hCA : CA = 4 / (2 * a0 * √(2 * alo * (1 - ahi) ^ 2))) (hca : ca = 2 * (1 - ahi)) :
    |ad - a0| ≤ (CA / ca) * d ^ 2 := by
  have ha0_pos : 0 < a0 := halo0.trans halo
  have ha0_lt1 : a0 < 1 := ha0hi.trans hahi1
  have hca_pos : 0 < ca := by rw [hca]; linarith
  have hc_det_pos : 0 < 2 * alo * (1 - ahi) ^ 2 := by
    have : 0 < 1 - ahi := sub_pos.mpr hahi1
    positivity
  have ha0_d_diff : |stdAreaGram (sqVec a0 d) - totalStdArea| ≤ CA * d ^ 2 := by
    have hcont_d0 : ContinuousOn (fun t => stdAreaGram (sqVec a0 t)) (Set.Icc 0 d) :=
      (stdAreaGram_sqVec_continuousOn_d ha0_pos ha0_lt1 (by linarith)).mono
        (Set.Icc_subset_Icc_right hd_box)
    have hderiv_d0 : ∀ t ∈ Set.Ioo 0 d,
        HasDerivAt (fun t => stdAreaGram (sqVec a0 t)) (stdAreaFDeriv (sqVec a0 t) ![0, 1, 0, 0, 1, 0]) t := by
      intro t ht
      have hmem : sqVec a0 t ∈ gramOpen :=
        sqVec_mem_gramOpen ha0_pos ha0_lt1 ht.1 (by linarith [ht.2])
      exact HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_stdAreaGram hmem) (sqVec_hasDerivAt_d a0 t)
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope _ _ hd0 hcont_d0 hderiv_d0
    rw [stdAreaFDeriv_sqVec_d] at hslope
    have hD_lb : 2 * alo * (1 - ahi) ^ 2 ≤ Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ) := by
      have hfac := Sphere3.squareSuspensionPolarDet_factor a0 (2 * a0 - 1 + ξ)
      rw [hfac]
      have hf1 : 1 - ahi ≤ 1 - (2 * a0 - 1 + ξ) := by linarith [hξ.2]
      have hf2 : 2 * alo * (1 - ahi) ≤ 1 + (2 * a0 - 1 + ξ) - 2 * a0 ^ 2 := by
        have hpol : 1 + (2 * a0 - 1 + ξ) - 2 * a0 ^ 2 = 2 * a0 * (1 - a0) + ξ := by ring
        rw [hpol]
        have hprod : 2 * alo * (1 - ahi) ≤ 2 * a0 * (1 - a0) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
        linarith [hξ.1]
      have hf2_nonneg : 0 ≤ 1 + (2 * a0 - 1 + ξ) - 2 * a0 ^ 2 :=
        le_trans (mul_nonneg (by linarith) (by linarith)) hf2
      calc 2 * alo * (1 - ahi) ^ 2 = (2 * alo * (1 - ahi)) * (1 - ahi) := by ring
        _ ≤ (1 + (2 * a0 - 1 + ξ) - 2 * a0 ^ 2) * (1 - (2 * a0 - 1 + ξ)) :=
            mul_le_mul hf2 hf1 (by linarith) hf2_nonneg
        _ = (1 - (2 * a0 - 1 + ξ)) * (1 + (2 * a0 - 1 + ξ) - 2 * a0 ^ 2) := by ring
    have hsqrt_lb : √(2 * alo * (1 - ahi) ^ 2) ≤ √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ)) :=
      Real.sqrt_le_sqrt hD_lb
    have hsqrt_pos : 0 < √(2 * alo * (1 - ahi) ^ 2) := Real.sqrt_pos.mpr hc_det_pos
    have hslope_nonneg : 0 ≤ 4 * ξ / ((2 * a0 + ξ) * √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ))) := by
      have := hξ.1; positivity
    have hslope_le : 4 * ξ / ((2 * a0 + ξ) * √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ))) ≤
        CA * d := by
      have hnum_le : 4 * ξ ≤ 4 * d := by linarith [hξ.2]
      have hden_ge : 2 * a0 * √(2 * alo * (1 - ahi) ^ 2) ≤
          (2 * a0 + ξ) * √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ)) :=
        mul_le_mul (by linarith [hξ.1]) hsqrt_lb hsqrt_pos.le (by linarith [hξ.1])
      calc 4 * ξ / ((2 * a0 + ξ) * √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ)))
          ≤ 4 * d / (2 * a0 * √(2 * alo * (1 - ahi) ^ 2)) :=
            div_le_div₀ (by linarith [hξ.2]) hnum_le (mul_pos (by linarith) hsqrt_pos) hden_ge
        _ = CA * d := by rw [hCA]; ring
    have heq : stdAreaGram (sqVec a0 d) - totalStdArea =
        (4 * ξ / ((2 * a0 + ξ) * √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ)))) * d := by
      rw [← harea0, hslope]
      field_simp [hd0.ne']
      ring
    rw [heq, abs_of_nonneg (mul_nonneg hslope_nonneg hd0.le)]
    calc 4 * ξ / ((2 * a0 + ξ) * √(Sphere3.squareSuspensionPolarDet a0 (2 * a0 - 1 + ξ))) * d
        ≤ (CA * d) * d := mul_le_mul_of_nonneg_right hslope_le hd0.le
      _ = CA * d ^ 2 := by ring
  by_cases heq : ad = a0
  · rw [heq, sub_self, abs_zero]
    have hCA0 : 0 ≤ CA := by rw [hCA]; positivity
    positivity
  · have hcont_a : ContinuousOn (fun x => stdAreaGram (sqVec x d)) (Set.Icc alo ahi) :=
      stdAreaGram_sqVec_continuousOn_a hd0.le halo0 hahi1 hd_box
    have hderiv_a_lb : ∀ x ∈ Set.Icc alo ahi,
        HasDerivAt (fun y => stdAreaGram (sqVec y d)) (stdAreaFDeriv (sqVec x d) ![1, 2, 1, 1, 2, 1]) x ∧
        ca ≤ stdAreaFDeriv (sqVec x d) ![1, 2, 1, 1, 2, 1] := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le halo0 hx.1
      have hx1 : x < 1 := lt_of_le_of_lt hx.2 hahi1
      have hmem : sqVec x d ∈ gramOpen := sqVec_mem_gramOpen hx0 hx1 hd0 (by linarith [hx.2])
      have hd_at : HasDerivAt (fun y => stdAreaGram (sqVec y d))
          (stdAreaFDeriv (sqVec x d) ![1, 2, 1, 1, 2, 1]) x :=
        HasFDerivAt.comp_hasDerivAt x (hasFDerivAt_stdAreaGram hmem) (sqVec_hasDerivAt_a x d)
      refine ⟨hd_at, ?_⟩
      rw [stdAreaFDeriv_sqVec_a]
      set D := Sphere3.squareSuspensionPolarDet x (2 * x - 1 + d)
      have hD_pos : 0 < D := Sphere3.squareSuspensionPolarDet_pos x d hx0 hx1 hd0 (by linarith [hx.2])
      have hD_le4 : D ≤ 4 := by
        have hfac := Sphere3.squareSuspensionPolarDet_factor x (2 * x - 1 + d)
        dsimp [D]; rw [hfac]
        have h1 : 0 ≤ 1 - (2 * x - 1 + d) := by linarith [hx.2]
        have h2 : 1 - (2 * x - 1 + d) ≤ 2 := by linarith
        have h3_eq : 1 + (2 * x - 1 + d) - 2 * x ^ 2 = 2 * x * (1 - x) + d := by ring
        have h3 : 0 ≤ 1 + (2 * x - 1 + d) - 2 * x ^ 2 := by rw [h3_eq]; positivity
        have h4_eq : 1 + (2 * x - 1 + d) - 2 * x ^ 2 = 1 / 2 + d - 2 * (x - 1 / 2) ^ 2 := by ring
        have h4 : 1 + (2 * x - 1 + d) - 2 * x ^ 2 ≤ 2 := by
          rw [h4_eq]
          linarith [sq_nonneg (x - 1 / 2), halo0.trans (halo.trans ha0hi)]
        calc (1 - (2 * x - 1 + d)) * (1 + (2 * x - 1 + d) - 2 * x ^ 2) ≤ 2 * 2 :=
              mul_le_mul h2 h4 h3 (by norm_num)
          _ = 4 := by norm_num
      have hsqrt_le2 : √D ≤ 2 := by
        rw [Real.sqrt_le_iff]; refine ⟨by norm_num, by linarith⟩
      have hterm2_nonneg : 0 ≤ 8 * d / ((2 * x + d) * √D) := by positivity
      have hnum_ge : 1 - ahi ≤ 2 * (1 - x) - d := by linarith [hx.2]
      have hden_le : (1 + x) * √D ≤ 4 := by
        calc (1 + x) * √D ≤ 2 * 2 := mul_le_mul (by linarith) hsqrt_le2 (Real.sqrt_nonneg D) (by norm_num)
          _ = 4 := by norm_num
      have hterm1 : ca ≤ 8 * (2 * (1 - x) - d) / ((1 + x) * √D) := by
        rw [hca]
        calc 2 * (1 - ahi) = 8 * (1 - ahi) / 4 := by ring
          _ ≤ 8 * (2 * (1 - x) - d) / ((1 + x) * √D) := by
            gcongr
            linarith
      linarith
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · have hcont_sub : ContinuousOn (fun y => stdAreaGram (sqVec y d)) (Set.Icc ad a0) :=
        hcont_a.mono (Set.Icc_subset_Icc had_mem.1 ha0hi.le)
      obtain ⟨η, hη, hsl⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont_sub
        fun y hy => (hderiv_a_lb y (Set.Icc_subset_Icc had_mem.1 ha0hi.le (Set.Ioo_subset_Icc_self hy))).1
      have hη_lb := (hderiv_a_lb η (Set.Icc_subset_Icc had_mem.1 ha0hi.le (Set.Ioo_subset_Icc_self hη))).2
      have hdiff_eq : stdAreaGram (sqVec a0 d) - totalStdArea =
          stdAreaFDeriv (sqVec η d) ![1, 2, 1, 1, 2, 1] * (a0 - ad) := by
        rw [← had_area, hsl]; field_simp [(sub_pos.mpr hlt).ne']
      have habs_a : |ad - a0| = a0 - ad := by rw [abs_of_neg (by linarith)]; ring
      have hprod : ca * |ad - a0| ≤ |stdAreaGram (sqVec a0 d) - totalStdArea| := by
        rw [habs_a, hdiff_eq, abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
        exact mul_le_mul_of_nonneg_right hη_lb (by linarith)
      have := hprod.trans ha0_d_diff
      rw [show (CA / ca) * d ^ 2 = (CA * d ^ 2) / ca by ring, le_div_iff₀ hca_pos]
      linarith
    · have hcont_sub : ContinuousOn (fun y => stdAreaGram (sqVec y d)) (Set.Icc a0 ad) :=
        hcont_a.mono (Set.Icc_subset_Icc halo.le had_mem.2)
      obtain ⟨η, hη, hsl⟩ := exists_hasDerivAt_eq_slope _ _ hgt hcont_sub
        fun y hy => (hderiv_a_lb y (Set.Icc_subset_Icc halo.le had_mem.2 (Set.Ioo_subset_Icc_self hy))).1
      have hη_lb := (hderiv_a_lb η (Set.Icc_subset_Icc halo.le had_mem.2 (Set.Ioo_subset_Icc_self hη))).2
      have hdiff_eq : totalStdArea - stdAreaGram (sqVec a0 d) =
          stdAreaFDeriv (sqVec η d) ![1, 2, 1, 1, 2, 1] * (ad - a0) := by
        rw [← had_area, hsl]; field_simp [(sub_pos.mpr hgt).ne']
      have habs_a : |ad - a0| = ad - a0 := abs_of_pos (by linarith)
      have hprod : ca * |ad - a0| ≤ |stdAreaGram (sqVec a0 d) - totalStdArea| := by
        rw [habs_a, abs_sub_comm, hdiff_eq, abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
        exact mul_le_mul_of_nonneg_right hη_lb (by linarith)
      have := hprod.trans ha0_d_diff
      rw [show (CA / ca) * d ^ 2 = (CA * d ^ 2) / ca by ring, le_div_iff₀ hca_pos]
      linarith

private lemma sqVec_vol_diff_a_bound {alo a0 ahi d ad CV : ℝ}
    (halo0 : 0 < alo) (halo : alo < a0) (ha0hi : a0 < ahi) (hahi1 : ahi < 1)
    (hd0 : 0 < d) (hd_box : d ≤ 1 - ahi) (had_mem : ad ∈ Set.Icc alo ahi)
    (hCV : CV = 2 * Real.pi / √(min (1 - ahi) ((1 - ahi) * (2 * alo)))) :
    |gaussVolGram (sqVec ad d) - gaussVolGram (sqVec a0 d)| ≤ CV * |ad - a0| := by
  by_cases heq : ad = a0
  · simp [heq]
  · have hderiv_v : ∀ x ∈ Set.Icc alo ahi,
        HasDerivAt (fun y => gaussVolGram (sqVec y d)) (gaussVolFDeriv (sqVec x d) ![1, 2, 1, 1, 2, 1]) x := by
      intro x hx
      have hmem : sqVec x d ∈ gramOpen :=
        sqVec_mem_gramOpen (lt_of_lt_of_le halo0 hx.1) (lt_of_le_of_lt hx.2 hahi1) hd0
          (by linarith [hx.2])
      exact HasFDerivAt.comp_hasDerivAt x (hasFDerivAt_gaussVolGram hmem) (sqVec_hasDerivAt_a x d)
    have hcont_v : ContinuousOn (fun y => gaussVolGram (sqVec y d)) (Set.Icc alo ahi) := fun x hx =>
      (hderiv_v x hx).continuousAt.continuousWithinAt
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · obtain ⟨η, hη, hsl⟩ := exists_hasDerivAt_eq_slope _ _ hlt
        (hcont_v.mono (Set.Icc_subset_Icc had_mem.1 ha0hi.le))
        fun y hy => hderiv_v y (Set.Icc_subset_Icc had_mem.1 ha0hi.le (Set.Ioo_subset_Icc_self hy))
      have hη_mem := Set.Icc_subset_Icc had_mem.1 ha0hi.le (Set.Ioo_subset_Icc_self hη)
      have hbd := gaussVolFDeriv_sqVec_a_bound halo0 hη_mem.1 hη_mem.2 hahi1 hd0 hd_box
      rw [← hCV] at hbd
      have hdif : gaussVolGram (sqVec a0 d) - gaussVolGram (sqVec ad d) =
          gaussVolFDeriv (sqVec η d) ![1, 2, 1, 1, 2, 1] * (a0 - ad) := by
        rw [hsl]; field_simp [(sub_pos.mpr hlt).ne']
      rw [abs_sub_comm, hdif, abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hbd (abs_nonneg _)
    · obtain ⟨η, hη, hsl⟩ := exists_hasDerivAt_eq_slope _ _ hgt
        (hcont_v.mono (Set.Icc_subset_Icc halo.le had_mem.2))
        fun y hy => hderiv_v y (Set.Icc_subset_Icc halo.le had_mem.2 (Set.Ioo_subset_Icc_self hy))
      have hη_mem := Set.Icc_subset_Icc halo.le had_mem.2 (Set.Ioo_subset_Icc_self hη)
      have hbd := gaussVolFDeriv_sqVec_a_bound halo0 hη_mem.1 hη_mem.2 hahi1 hd0 hd_box
      rw [← hCV] at hbd
      have hdif : gaussVolGram (sqVec ad d) - gaussVolGram (sqVec a0 d) =
          gaussVolFDeriv (sqVec η d) ![1, 2, 1, 1, 2, 1] * (ad - a0) := by
        rw [hsl]; field_simp [(sub_pos.mpr hgt).ne']
      rw [hdif, abs_mul]
      exact mul_le_mul_of_nonneg_right hbd (abs_nonneg _)

private lemma sqVec_vol_gain_d {a0 d alpha : ℝ}
    (ha0 : 0 < a0) (ha1 : a0 < 1) (hd0 : 0 < d) (hd1 : d ≤ 1 - a0)
    (halpha : alpha = (1 / 3 : ℝ) * √(2 * a0 * (1 - a0))) :
    let Vdeg : ℝ :=
      (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
        (8 * Real.pi)) * (4 * Real.arccos (-a0) - 2 * Real.pi)
    alpha * d * √d ≤ gaussVolGram (sqVec a0 d) - Vdeg := by
  intro Vdeg
  let g : ℝ → ℝ := fun t => gaussVolGram (sqVec a0 t) - alpha * t * √t
  have hg_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) (2 * (1 - a0)), t ≤ 1 - a0 → 0 ≤ deriv g t := by
    intro t ht ht1
    have hmem : sqVec a0 t ∈ gramOpen := sqVec_mem_gramOpen ha0 ha1 ht.1 ht.2
    have hf := HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_gaussVolGram hmem) (sqVec_hasDerivAt_d a0 t)
    have hsqrt_d : HasDerivAt (fun x : ℝ => x * √x) ((3 / 2 : ℝ) * √t) t := by
      have hmul := (hasDerivAt_id t).mul (Real.hasDerivAt_sqrt ht.1.ne')
      refine hmul.congr_deriv ?_
      have hs_ne : √t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
      have hsq : √t ^ 2 = t := Real.sq_sqrt ht.1.le
      dsimp only [id_eq]
      field_simp [hs_ne]
      rw [hsq]
      ring
    have hsub := hf.sub (hsqrt_d.const_mul alpha)
    have hg_at : HasDerivAt g (gaussVolFDeriv (sqVec a0 t) ![0, 1, 0, 0, 1, 0] -
        alpha * ((3 / 2 : ℝ) * √t)) t := by
      refine hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
      dsimp [g]; ring
    rw [hg_at.deriv]
    have hlb := gaussVolFDeriv_sqVec_d_lb ha0 ha1 ht.1 ht1
    have hal : alpha * ((3 / 2 : ℝ) * √t) = (1 / 2 : ℝ) * √(2 * a0 * (1 - a0)) * √t := by
      rw [halpha]; ring
    linarith
  have hmono_eps : ∀ ε ∈ Set.Ioo 0 d, g ε ≤ g d := by
    intro ε hε
    have hcont_g : ContinuousOn g (Set.Icc ε d) := by
      refine ContinuousOn.sub ?_ ?_
      · intro t ht
        have hmem : sqVec a0 t ∈ gramOpen :=
          sqVec_mem_gramOpen ha0 ha1 (lt_of_lt_of_le hε.1 ht.1) (by linarith [ht.2])
        exact (HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_gaussVolGram hmem) (sqVec_hasDerivAt_d a0 t))
          |>.continuousAt.continuousWithinAt
      · exact ((continuousOn_const.mul continuousOn_id).mul
          (Real.continuous_sqrt.continuousOn)).mono (Set.subset_univ _)
    have hdiff_g : DifferentiableOn ℝ g (interior (Set.Icc ε d)) := by
      intro t ht
      rw [interior_Icc] at ht
      have hmem : sqVec a0 t ∈ gramOpen :=
        sqVec_mem_gramOpen ha0 ha1 (lt_trans hε.1 ht.1) (by linarith [ht.2])
      exact (HasFDerivAt.comp_hasDerivAt t (hasFDerivAt_gaussVolGram hmem) (sqVec_hasDerivAt_d a0 t)
        |>.sub (((hasDerivAt_id t).mul (Real.hasDerivAt_sqrt (lt_trans hε.1 ht.1).ne')).const_mul alpha
          |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp [mul_assoc]))).differentiableAt.differentiableWithinAt
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc ε d) hcont_g hdiff_g fun t ht => by
      rw [interior_Icc] at ht
      exact hg_deriv t ⟨lt_trans hε.1 ht.1, by linarith [ht.2]⟩ (by linarith [ht.2])
    exact hmono ⟨le_rfl, hε.2.le⟩ ⟨hε.2.le, le_rfl⟩ hε.2.le
  have htend_g : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds Vdeg) := by
    have ht1 := tendsto_gaussVolGram_sqVec_zero ha0 ha1
    have ht2 : Filter.Tendsto (fun t : ℝ => alpha * t * √t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : Continuous (fun t : ℝ => alpha * t * √t) :=
        (continuous_const.mul continuous_id).mul Real.continuous_sqrt
      have hten0 := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      have h0 : alpha * (0 : ℝ) * √0 = 0 := by simp
      rwa [h0] at hten0
    have hsub := ht1.sub ht2
    rw [sub_zero] at hsub
    exact hsub
  have hev_g : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), g ε ≤ g d := by
    have hIoo : Set.Ioo (0 : ℝ) d ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio d, isOpen_Iio, Set.mem_Iio.mpr hd0, fun _ h => ⟨h.2, h.1⟩⟩
    filter_upwards [hIoo] with ε hε
    exact hmono_eps ε hε
  have hVdeg_le : Vdeg ≤ g d := le_of_tendsto htend_g hev_g
  dsimp [g] at hVdeg_le
  linarith

/-- For every `totalStdArea ∈ (0, 4π)`, there exists a nondegenerate spherical tetrahedron of
total area `faceScale * totalStdArea` whose volume strictly exceeds that of the equal-area
degenerate square suspension limit. -/
theorem exists_tetrahedron_strictly_larger_volume_than_degenerate
    (totalStdArea : ℝ) (hA0 : 0 < totalStdArea) (hA4pi : totalStdArea < 4 * Real.pi) :
    ∃ T : SphericalTetrahedron,
      T.area = faceScale * totalStdArea ∧
      sphereScale 3 *
          (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi)) *
          (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) <
        T.volume := by
  let φ0 : ℝ := totalStdArea / 16
  let φlo : ℝ := φ0 / 2
  let φhi : ℝ := (φ0 + Real.pi / 4) / 2
  have hφ0_pos : 0 < φ0 := by dsimp [φ0]; linarith
  have hφ0_lt : φ0 < Real.pi / 4 := by dsimp [φ0]; linarith
  have hφlo_pos : 0 < φlo := by dsimp [φlo]; linarith
  have hφlo_lt : φlo < φ0 := by dsimp [φlo]; linarith
  have hφhi_gt : φ0 < φhi := by dsimp [φhi]; linarith
  have hφhi_lt : φhi < Real.pi / 4 := by dsimp [φhi]; linarith
  let a0 := Real.tan φ0 ^ 2
  let alo := Real.tan φlo ^ 2
  let ahi := Real.tan φhi ^ 2
  have hz0 := stdAreaGram_sqVec_zero hφ0_pos hφ0_lt
  have hzlo := stdAreaGram_sqVec_zero hφlo_pos (lt_trans hφlo_lt hφ0_lt)
  have hzhi := stdAreaGram_sqVec_zero (lt_trans hφ0_pos hφhi_gt) hφhi_lt
  dsimp only at hz0 hzlo hzhi
  change 0 < a0 ∧ a0 < 1 ∧ stdAreaGram (sqVec a0 0) = 16 * φ0 at hz0
  change 0 < alo ∧ alo < 1 ∧ stdAreaGram (sqVec alo 0) = 16 * φlo at hzlo
  change 0 < ahi ∧ ahi < 1 ∧ stdAreaGram (sqVec ahi 0) = 16 * φhi at hzhi
  have htan_mono : ∀ x y, 0 < x → x < y → y < Real.pi / 4 → Real.tan x < Real.tan y :=
    fun x y hx0 hxy hy1 =>
      Real.strictMonoOn_tan ⟨by linarith [Real.pi_pos], by linarith⟩
        ⟨by linarith [Real.pi_pos], by linarith⟩ hxy
  have htan_lo_pos : 0 < Real.tan φlo := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hφlo_pos (by linarith))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  have htan0_pos : 0 < Real.tan φ0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hφ0_pos (by linarith))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  have halo_lt0 : alo < a0 := by
    have hlt := htan_mono φlo φ0 hφlo_pos hφlo_lt (by linarith)
    change Real.tan φlo ^ 2 < Real.tan φ0 ^ 2
    exact sq_lt_sq' (by linarith) hlt
  have ha0_lthi : a0 < ahi := by
    have hlt := htan_mono φ0 φhi hφ0_pos hφhi_gt hφhi_lt
    change Real.tan φ0 ^ 2 < Real.tan φhi ^ 2
    exact sq_lt_sq' (by linarith) hlt
  have harea0 : stdAreaGram (sqVec a0 0) = totalStdArea := by
    rw [hz0.2.2]; dsimp [φ0]; ring
  have harealo : stdAreaGram (sqVec alo 0) < totalStdArea := by
    rw [hzlo.2.2]; dsimp [φlo, φ0]; linarith
  have hareahi : totalStdArea < stdAreaGram (sqVec ahi 0) := by
    rw [hzhi.2.2]; dsimp [φhi, φ0]; linarith
  let dbox : ℝ := 1 - ahi
  have hdbox_pos : 0 < dbox := by dsimp [dbox]; linarith [hzhi.2.1]
  have hcont_lo : ContinuousOn (fun d => stdAreaGram (sqVec alo d)) (Set.Icc 0 dbox) :=
    stdAreaGram_sqVec_continuousOn_d hzlo.1 hzlo.2.1 (by dsimp [dbox]; linarith [hzlo.2.1, halo_lt0, ha0_lthi])
  have hcont_hi : ContinuousOn (fun d => stdAreaGram (sqVec ahi d)) (Set.Icc 0 dbox) :=
    stdAreaGram_sqVec_continuousOn_d hzhi.1 hzhi.2.1 (by dsimp [dbox]; linarith [hzhi.2.1])
  have hten_lo : Filter.Tendsto (fun d => stdAreaGram (sqVec alo d))
      (nhdsWithin 0 (Set.Icc 0 dbox)) (nhds (stdAreaGram (sqVec alo 0))) :=
    hcont_lo 0 ⟨le_rfl, hdbox_pos.le⟩
  have hten_hi : Filter.Tendsto (fun d => stdAreaGram (sqVec ahi d))
      (nhdsWithin 0 (Set.Icc 0 dbox)) (nhds (stdAreaGram (sqVec ahi 0))) :=
    hcont_hi 0 ⟨le_rfl, hdbox_pos.le⟩
  have hev_lo : ∀ᶠ d in nhdsWithin (0 : ℝ) (Set.Icc 0 dbox),
      stdAreaGram (sqVec alo d) < totalStdArea := hten_lo (Iio_mem_nhds harealo)
  have hev_hi : ∀ᶠ d in nhdsWithin (0 : ℝ) (Set.Icc 0 dbox),
      totalStdArea < stdAreaGram (sqVec ahi d) := hten_hi (Ioi_mem_nhds hareahi)
  obtain ⟨U1, hU1_open, h0U1, hU1_sub⟩ := mem_nhdsWithin.mp hev_lo
  obtain ⟨U2, hU2_open, h0U2, hU2_sub⟩ := mem_nhdsWithin.mp hev_hi
  obtain ⟨δ1, hδ1_pos, hδ1_sub⟩ := Metric.isOpen_iff.mp hU1_open 0 h0U1
  obtain ⟨δ2, hδ2_pos, hδ2_sub⟩ := Metric.isOpen_iff.mp hU2_open 0 h0U2
  let d1 : ℝ := min (dbox / 2) (min (δ1 / 2) (δ2 / 2))
  have hd1_pos : 0 < d1 := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hd1_le_dbox : d1 ≤ dbox := (min_le_left _ _).trans (by linarith)
  have hc_det_pos : 0 < 2 * alo * (1 - ahi) ^ 2 := by
    have := hzlo.1; have := hzhi.2.1; positivity
  let CA : ℝ := 4 / (2 * a0 * √(2 * alo * (1 - ahi) ^ 2))
  let ca : ℝ := 2 * (1 - ahi)
  let CV : ℝ := 2 * Real.pi / √(min (1 - ahi) ((1 - ahi) * (2 * alo)))
  have hCV_nonneg : 0 ≤ CV := by positivity
  let alpha : ℝ := (1 / 3 : ℝ) * √(2 * a0 * (1 - a0))
  have halpha_pos : 0 < alpha := by
    have := hz0.1; have := hz0.2.1; positivity
  let C : ℝ := CV * (CA / ca)
  have hC_nonneg : 0 ≤ C := by
    have hCA0 : 0 ≤ CA := by positivity
    have hca0 : 0 ≤ ca := by dsimp [ca]; linarith [hzhi.2.1]
    positivity
  let s : ℝ := min (√d1 / 2) (alpha / (2 * (C + 1)))
  have hs_pos : 0 < s := lt_min (by positivity) (by positivity)
  have hs_lt : s < alpha / (C + 1) := by
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  let d : ℝ := s ^ 2
  have hd_pos : 0 < d := sq_pos_of_pos hs_pos
  have hd_le_d1 : d ≤ d1 := by
    have hs_le : s ≤ √d1 / 2 := min_le_left _ _
    have hsq : s ^ 2 ≤ (√d1 / 2) ^ 2 :=
      sq_le_sq' (by linarith [hs_pos]) hs_le
    rw [div_pow, Real.sq_sqrt hd1_pos.le] at hsq
    linarith
  have hd_le_dbox : d ≤ dbox := hd_le_d1.trans hd1_le_dbox
  have hd_mem_Icc : d ∈ Set.Icc (0 : ℝ) dbox := ⟨hd_pos.le, hd_le_dbox⟩
  have hd_ball1 : d ∈ Metric.ball (0 : ℝ) δ1 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd_pos]
    have hd1_le : d1 ≤ δ1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hd_ball2 : d ∈ Metric.ball (0 : ℝ) δ2 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hd_pos]
    have hd1_le : d1 ≤ δ2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hlo_d : stdAreaGram (sqVec alo d) < totalStdArea := hU1_sub ⟨hδ1_sub hd_ball1, hd_mem_Icc⟩
  have hhi_d : totalStdArea < stdAreaGram (sqVec ahi d) := hU2_sub ⟨hδ2_sub hd_ball2, hd_mem_Icc⟩
  have hcont_a : ContinuousOn (fun x => stdAreaGram (sqVec x d)) (Set.Icc alo ahi) :=
    stdAreaGram_sqVec_continuousOn_a hd_pos.le hzlo.1 hzhi.2.1 hd_le_dbox
  have hivt := intermediate_value_Icc (le_trans halo_lt0.le ha0_lthi.le) hcont_a
  obtain ⟨ad, had_mem, had_area⟩ := hivt ⟨hlo_d.le, hhi_d.le⟩
  have had0 : 0 < ad := lt_of_lt_of_le hzlo.1 had_mem.1
  have had1 : ad < 1 := lt_of_le_of_lt had_mem.2 hzhi.2.1
  have had_gram : sqVec ad d ∈ gramOpen :=
    sqVec_mem_gramOpen had0 had1 hd_pos (by dsimp [dbox] at hd_le_dbox; linarith [had_mem.2, hzhi.2.1])
  have ha_diff : |ad - a0| ≤ (CA / ca) * d ^ 2 :=
    sqVec_area_diff_bound hzlo.1 halo_lt0 ha0_lthi hzhi.2.1 hd_pos hd_le_dbox
      had_mem had_area harea0 rfl rfl
  have hV_bound : |gaussVolGram (sqVec ad d) - gaussVolGram (sqVec a0 d)| ≤ CV * |ad - a0| :=
    sqVec_vol_diff_a_bound hzlo.1 halo_lt0 ha0_lthi hzhi.2.1 hd_pos hd_le_dbox had_mem rfl
  have hvol_a_diff : |gaussVolGram (sqVec ad d) - gaussVolGram (sqVec a0 d)| ≤ C * s ^ 4 := by
    calc |gaussVolGram (sqVec ad d) - gaussVolGram (sqVec a0 d)|
        ≤ CV * |ad - a0| := hV_bound
      _ ≤ CV * ((CA / ca) * d ^ 2) := mul_le_mul_of_nonneg_left ha_diff hCV_nonneg
      _ = C * s ^ 4 := by dsimp [C, d]; ring
  let Vdeg : ℝ :=
    (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
      (8 * Real.pi)) * (4 * Real.arccos (-a0) - 2 * Real.pi)
  have hvol_t_gain : alpha * s ^ 3 ≤ gaussVolGram (sqVec a0 d) - Vdeg := by
    have hgain_d := sqVec_vol_gain_d hz0.1 hz0.2.1 hd_pos
      (by dsimp [dbox] at hd_le_dbox; linarith [ha0_lthi]) rfl
    have hds : alpha * d * √d = alpha * s ^ 3 := by
      dsimp [d]; rw [Real.sqrt_sq hs_pos.le]; ring
    have hgain_d' : alpha * d * √d ≤ gaussVolGram (sqVec a0 d) - Vdeg := hgain_d
    linarith [hgain_d', hds]
  have hgain : 0 < gaussVolGram (sqVec ad d) - Vdeg := by
    refine Sphere3.positive_gain_from_cubic_quartic_bounds alpha C s
      (gaussVolGram (sqVec ad d) - Vdeg) halpha_pos hC_nonneg hs_pos hs_lt ?_
    have h1 := abs_le.mp hvol_a_diff
    linarith [h1.1, hvol_t_gain]
  let T : SphericalTetrahedron := tetOf (sqVec ad d) had_gram
  dsimp only at had_area
  refine ⟨T, ?_, ?_⟩
  · rw [area_eq_faceScale_mul_stdArea, stdArea_eq_stdAreaGram, gramPoint_tetOf, had_area]
  · rw [volume_eq_two_sphereScale_mul_gaussVolGram, gramPoint_tetOf]
    have hss : 0 < sphereScale 3 := sphereScale_pos (d := 3) (by decide)
    have hmul : 2 * sphereScale 3 * Vdeg =
        sphereScale 3 *
          (MeasureTheory.volume.toSphere.real (Set.univ : Set ↑(Metric.sphere (0 : E4) 1)) /
            (4 * Real.pi)) *
          (4 * Real.arccos (-Real.tan (totalStdArea / 16) ^ 2) - 2 * Real.pi) := by
      dsimp [Vdeg, a0, φ0]
      ring
    rw [← hmul]
    exact mul_lt_mul_of_pos_left (sub_pos.mp hgain) (mul_pos two_pos hss)

end SphericalTetrahedron
