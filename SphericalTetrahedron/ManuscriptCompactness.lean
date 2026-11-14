module

public import SphericalTetrahedron.ManuscriptBoundaryPerturbation
public import SphericalTetrahedron.ManuscriptCompactnessBridge

@[expose] public section

/-!
# Compactness and Existence of a Fixed-Area Maximizer

This module completes the compactness step of the global isoperimetric proof: for any spherical
tetrahedron `T`, there exists a (nondegenerate) spherical tetrahedron `M` of the same surface area
maximizing spherical volume among all spherical tetrahedra of area `T.area`.

It relies on:
- `SphericalTetrahedron.ManuscriptCompactnessBridge`
  (`fixed_area_maximizer_of_manuscript_compactification`),
- `SphericalTetrahedron.ManuscriptBoundaryPerturbation`
  (`degenerate_limit_volume_le_square`, `exists_tetrahedron_strictly_larger_volume_than_degenerate`,
  `toSphere_slab_bound`, `hausdorffMeasure2_circle_null`, `measure_sphere_two_section`).
-/

open MeasureTheory Filter Topology Metric
open scoped EuclideanGeometry RealInnerProductSpace Pointwise ENNReal NNReal

noncomputable section

namespace SphericalTetrahedron

private abbrev S3 := ↑(Metric.sphere (0 : E4) 1)

private abbrev NormalTuple := Fin 4 → S3

private def normalOf (S : SphericalTetrahedron) : NormalTuple :=
  fun i => ⟨S.normal i, Metric.mem_sphere.mpr (by rw [dist_zero_right]; exact S.unit i)⟩

private def bodyOf (u : NormalTuple) : Set S3 :=
  {y | ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) (y : E4)}

private def volumeOf (u : NormalTuple) : ℝ :=
  sphereScale 3 * MeasureTheory.volume.toSphere.real (bodyOf u)

private lemma volumeOf_normalOf (S : SphericalTetrahedron) :
    volumeOf (normalOf S) = S.volume := by
  rw [volumeOf, S.volume_eq_sphereScale_mul_toSphere]
  congr 2
  ext y
  have hy : ‖(y : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
  simp [bodyOf, normalOf, SphericalTetrahedron.body, hy]

private lemma volumeOf_eq_measure3 (u : NormalTuple) :
    volumeOf u =
      measure 3 {x : E4 | x ∈ Metric.sphere 0 1 ∧ ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x} := by
  let B : Set E4 := {x : E4 | x ∈ Metric.sphere 0 1 ∧ ∀ i : Fin 4, 0 ≤ inner ℝ (u i : E4) x}
  have hB_eq : B = Metric.sphere (0 : E4) 1 ∩ ⋂ i : Fin 4, {x : E4 | 0 ≤ inner ℝ (u i : E4) x} := by
    ext x
    simp [B]
  have hB_meas : MeasurableSet B := by
    rw [hB_eq]
    refine (Metric.isClosed_sphere.inter ?_).measurableSet
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_const.inner continuous_id)
  have hscale := hausdorffMeasure_real_eq_scale_mul_toSphere (d := 3) (by decide)
    (B := B) (fun _ hx => hx.1) hB_meas
  norm_num at hscale
  change _ = (MeasureTheory.Measure.hausdorffMeasure (3 : ℝ) B).toReal
  rw [hscale, volumeOf]
  congr 2
  ext y
  simp [B, bodyOf, y.2]

/-- Every nondegenerate spherical tetrahedron has strictly positive volume. -/
theorem tetrahedron_volume_pos (T : SphericalTetrahedron) : 0 < T.volume := by
  have hmeas := measure_three_eq_four_sphereScale_mul_ballCone T.body_subset_sphere
    T.body_measurableSet
  change T.volume = _ at hmeas
  let C : Set E4 := {x : E4 | x ∈ Metric.ball (0 : E4) 1 ∧ ∀ i : Fin 4, 0 < inner ℝ (T.normal i) x}
  have hC_eq : C = Metric.ball (0 : E4) 1 ∩ ⋂ i : Fin 4, {x : E4 | 0 < inner ℝ (T.normal i) x} := by
    ext x
    simp [C]
  have hC_open : IsOpen C := by
    rw [hC_eq]
    refine Metric.isOpen_ball.inter ?_
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.inner continuous_id)
  let c0 : E4 := (1 / (2 * (‖T.normalDualAxis‖ + 1))) • T.normalDualAxis
  have hc0_mem : c0 ∈ C := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
      have hden : 0 < 2 * (‖T.normalDualAxis‖ + 1) := by positivity
      calc (1 / (2 * (‖T.normalDualAxis‖ + 1))) * ‖T.normalDualAxis‖
          = ‖T.normalDualAxis‖ / (2 * (‖T.normalDualAxis‖ + 1)) := by ring
        _ < 1 := (div_lt_one hden).mpr (by linarith [norm_nonneg T.normalDualAxis])
    · intro i
      rw [real_inner_smul_right, T.normalDualAxis_inner i, mul_one]
      positivity
  have hC_sub : C ⊆ Set.Ioo (0 : ℝ) 1 • T.body := by
    intro x hx
    have hx_ne : x ≠ 0 := by
      intro h0
      have h00 := hx.2 0
      rw [h0, inner_zero_right] at h00
      exact lt_irrefl 0 h00
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    have hx_lt1 : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx.1
    let y : E4 := (‖x‖⁻¹) • x
    have hy_mem : y ∈ T.body := by
      refine ⟨?_, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ hx_pos.ne']
      · intro i
        rw [real_inner_smul_right]
        exact mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (hx.2 i).le
    refine ⟨‖x‖, ⟨hx_pos, hx_lt1⟩, y, hy_mem, ?_⟩
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hx_pos.ne', one_smul]
  have hcone_sub : Set.Ioo (0 : ℝ) 1 • T.body ⊆ Metric.ball (0 : E4) 1 := by
    rintro _ ⟨t, ht, y, hy, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1.le, hy.1, mul_one]
    exact ht.2
  have hC_pos : 0 < MeasureTheory.volume C := hC_open.measure_pos MeasureTheory.volume ⟨c0, hc0_mem⟩
  have hcone_pos : 0 < MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 • T.body) :=
    lt_of_lt_of_le hC_pos (measure_mono hC_sub)
  have hcone_ne_top : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 • T.body) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hcone_sub) measure_ball_lt_top).ne
  have hreal_pos : 0 < MeasureTheory.volume.real (Set.Ioo (0 : ℝ) 1 • T.body) :=
    ENNReal.toReal_pos hcone_pos.ne' hcone_ne_top
  have hss_pos : 0 < sphereScale 3 := sphereScale_pos (d := 3) (by decide)
  rw [hmeas]
  positivity

private lemma bodyOf_diff_bound {u v : NormalTuple} {ε : ℝ} (hε : 0 ≤ ε)
    (hnorm : ∀ i : Fin 4, ‖(u i : E4) - (v i : E4)‖ ≤ ε) :
    |MeasureTheory.volume.toSphere.real (bodyOf u) -
        MeasureTheory.volume.toSphere.real (bodyOf v)| ≤
      256 * ε := by
  let ν : MeasureTheory.Measure S3 := MeasureTheory.volume.toSphere
  let U : Set S3 := ⋃ i : Fin 4, {y : S3 | |inner ℝ (v i : E4) (y : E4)| ≤ ε}
  have hdiff1 : bodyOf u \ bodyOf v ⊆ U := by
    rintro y ⟨hyu, hyv⟩
    simp only [bodyOf, Set.mem_ofPred_eq, not_forall, not_le] at hyv
    rcases hyv with ⟨i, hi_neg⟩
    have hi_nonneg : 0 ≤ inner ℝ (u i : E4) (y : E4) := hyu i
    have hy1 : ‖(y : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
    have hsub : |inner ℝ (v i : E4) (y : E4)| ≤
        |inner ℝ ((u i : E4) - (v i : E4)) (y : E4)| := by
      rw [inner_sub_left, abs_of_neg hi_neg]
      linarith [le_abs_self (inner ℝ (u i : E4) (y : E4) - inner ℝ (v i : E4) (y : E4))]
    have hcs : |inner ℝ ((u i : E4) - (v i : E4)) (y : E4)| ≤ ε := by
      calc |inner ℝ ((u i : E4) - (v i : E4)) (y : E4)|
          ≤ ‖(u i : E4) - (v i : E4)‖ * ‖(y : E4)‖ := abs_real_inner_le_norm _ _
        _ ≤ ε * 1 := mul_le_mul (hnorm i) (by linarith [hy1]) (norm_nonneg _) hε
        _ = ε := mul_one ε
    exact Set.mem_iUnion.mpr ⟨i, le_trans hsub hcs⟩
  have hdiff2 : bodyOf v \ bodyOf u ⊆ U := by
    rintro y ⟨hyv, hyu⟩
    simp only [bodyOf, Set.mem_ofPred_eq, not_forall, not_le] at hyu
    rcases hyu with ⟨i, hi_neg⟩
    have hi_nonneg : 0 ≤ inner ℝ (v i : E4) (y : E4) := hyv i
    have hy1 : ‖(y : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
    have hsub : |inner ℝ (v i : E4) (y : E4)| ≤
        |inner ℝ ((u i : E4) - (v i : E4)) (y : E4)| := by
      rw [inner_sub_left, abs_of_nonneg hi_nonneg]
      have : inner ℝ (v i : E4) (y : E4) ≤ -(inner ℝ (u i : E4) (y : E4) -
          inner ℝ (v i : E4) (y : E4)) := by linarith
      exact this.trans (neg_le_abs _)
    have hcs : |inner ℝ ((u i : E4) - (v i : E4)) (y : E4)| ≤ ε := by
      calc |inner ℝ ((u i : E4) - (v i : E4)) (y : E4)|
          ≤ ‖(u i : E4) - (v i : E4)‖ * ‖(y : E4)‖ := abs_real_inner_le_norm _ _
        _ ≤ ε * 1 := mul_le_mul (hnorm i) (by linarith [hy1]) (norm_nonneg _) hε
        _ = ε := mul_one ε
    exact Set.mem_iUnion.mpr ⟨i, le_trans hsub hcs⟩
  have hU_le : ν.real U ≤ 256 * ε := by
    have hterm : ∀ i : Fin 4,
        ν.real {y : S3 | |inner ℝ (v i : E4) (y : E4)| ≤ ε} ≤ 64 * ε := fun i =>
      toSphere_slab_bound (by simpa [Metric.mem_sphere, dist_zero_right] using (v i).2) hε
    calc ν.real U ≤ ∑ i : Fin 4,
          ν.real {y : S3 | |inner ℝ (v i : E4) (y : E4)| ≤ ε} :=
        MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin 4, (64 * ε) := Finset.sum_le_sum fun i _ => hterm i
      _ = 256 * ε := by simp; ring
  have hsub1 : ν.real (bodyOf u) - ν.real (bodyOf v) ≤ ν.real U := by
    have hcov : bodyOf u ⊆ (bodyOf u \ bodyOf v) ∪ bodyOf v := fun y hy => by
      by_cases h : y ∈ bodyOf v <;> [exact Or.inr h; exact Or.inl ⟨hy, h⟩]
    have hle : ν.real (bodyOf u) ≤ ν.real (bodyOf u \ bodyOf v) + ν.real (bodyOf v) :=
      (MeasureTheory.measureReal_mono hcov).trans (MeasureTheory.measureReal_union_le _ _)
    have hleU : ν.real (bodyOf u \ bodyOf v) ≤ ν.real U := MeasureTheory.measureReal_mono hdiff1
    linarith
  have hsub2 : ν.real (bodyOf v) - ν.real (bodyOf u) ≤ ν.real U := by
    have hcov : bodyOf v ⊆ (bodyOf v \ bodyOf u) ∪ bodyOf u := fun y hy => by
      by_cases h : y ∈ bodyOf u <;> [exact Or.inr h; exact Or.inl ⟨hy, h⟩]
    have hle : ν.real (bodyOf v) ≤ ν.real (bodyOf v \ bodyOf u) + ν.real (bodyOf u) :=
      (MeasureTheory.measureReal_mono hcov).trans (MeasureTheory.measureReal_union_le _ _)
    have hleU : ν.real (bodyOf v \ bodyOf u) ≤ ν.real U := MeasureTheory.measureReal_mono hdiff2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma continuous_volumeOf : Continuous volumeOf := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let η := ε / (sphereScale 3 * 256 + 1)
  have hss_pos : 0 < sphereScale 3 := sphereScale_pos (d := 3) (by decide)
  have hη_pos : 0 < η := by positivity
  have hcoord : ∀ i : Fin 4, ∀ᶠ v in nhds u, ‖(v i : E4) - (u i : E4)‖ < η := fun i => by
    have hci : ContinuousAt (fun v : NormalTuple => (v i : E4)) u :=
      (continuous_subtype_val.comp (continuous_apply i)).continuousAt
    exact (Metric.tendsto_nhds.mp hci.tendsto η hη_pos).mono fun _ hv => by
      simpa [Real.dist_eq, dist_eq_norm] using hv
  have hall : ∀ᶠ v in nhds u, ∀ i : Fin 4, ‖(v i : E4) - (u i : E4)‖ < η :=
    eventually_all.mpr hcoord
  filter_upwards [hall] with v hv
  have hbd := bodyOf_diff_bound hη_pos.le fun i => (hv i).le
  rw [Real.dist_eq, volumeOf, volumeOf, ← mul_sub, abs_mul, abs_of_pos hss_pos]
  calc sphereScale 3 * |MeasureTheory.volume.toSphere.real (bodyOf v) -
        MeasureTheory.volume.toSphere.real (bodyOf u)|
      ≤ sphereScale 3 * (256 * η) := mul_le_mul_of_nonneg_left hbd hss_pos.le
    _ = (sphereScale 3 * 256) / (sphereScale 3 * 256 + 1) * ε := by dsimp [η]; ring
    _ < 1 * ε := by
        refine mul_lt_mul_of_pos_right ?_ hε
        rw [div_lt_one (by positivity)]
        linarith
    _ = ε := one_mul ε

private lemma circle_pair_null {a b : E4} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a ≠ b) (hab_neg : a ≠ -b) :
    MeasureTheory.Measure.hausdorffMeasure 2
        {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ a x = 0 ∧ inner ℝ b x = 0} = 0 := by
  let c := inner ℝ a b
  have hc_le : |c| ≤ 1 := by
    calc |c| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
      _ = 1 := by rw [ha, hb, mul_one]
  have hc_ne1 : c ≠ 1 := by
    intro hc1
    have hsq : ‖a - b‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, ha, hb]
      change 1 ^ 2 - 2 * c + 1 ^ 2 = 0
      rw [hc1]; norm_num
    have h0 : a - b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    exact hab (sub_eq_zero.mp h0)
  have hc_ne_neg1 : c ≠ -1 := by
    intro hc1
    have hsq : ‖a + b‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, ha, hb]
      change 1 ^ 2 + 2 * c + 1 ^ 2 = 0
      rw [hc1]; norm_num
    have h0 : a + b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    exact hab_neg (add_eq_zero_iff_eq_neg.mp h0)
  have hc_lt : -1 < c ∧ c < 1 := by
    have h := abs_le.mp hc_le
    exact ⟨lt_of_le_of_ne h.1 hc_ne_neg1.symm, lt_of_le_of_ne h.2 hc_ne1⟩
  let w : E4 := b - c • a
  have hw_sq : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    dsimp [w]
    have hba : inner ℝ b a = c := real_inner_comm a b
    have hca : ‖c • a‖ ^ 2 = c ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, ha, mul_one, sq_abs]
    rw [norm_sub_sq_real, hb, inner_smul_right, hca, hba]
    ring
  have hw_pos : 0 < ‖w‖ := by
    have h1mc2 : 0 < 1 - c ^ 2 := by nlinarith [hc_lt.1, hc_lt.2]
    have hsq_pos : 0 < ‖w‖ ^ 2 := by linarith [hw_sq]
    by_contra! hle
    have h0 : ‖w‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0, zero_pow (by decide)] at hsq_pos
    exact lt_irrefl 0 hsq_pos
  let w' : E4 := ‖w‖⁻¹ • w
  have hw' : ‖w'‖ = 1 := by
    dsimp [w']
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hw_pos.le), inv_mul_cancel₀ hw_pos.ne']
  have haw' : inner ℝ a w' = 0 := by
    dsimp [w', w]
    rw [inner_smul_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ha, one_pow]
    change ‖w‖⁻¹ * (c - c * 1) = 0
    ring
  have hsub : {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ a x = 0 ∧ inner ℝ b x = 0} ⊆
      {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ a x = 0 ∧ inner ℝ w' x = 0} := by
    rintro x ⟨hx, hax, hbx⟩
    refine ⟨hx, hax, ?_⟩
    dsimp [w', w]
    rw [inner_smul_left, inner_sub_left, inner_smul_left, hax, hbx]
    simp
  exact measure_mono_null hsub (hausdorffMeasure2_circle_null a w' ha hw' haw')

private lemma measure2_sphere_section_ne_top {a : E4} (ha : ‖a‖ = 1) :
    MeasureTheory.Measure.hausdorffMeasure 2 {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ a x = 0} ≠ ⊤ := by
  intro htop
  have h0 : SphericalTetrahedron.measure 2 {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ a x = 0} = 0 := by
    unfold SphericalTetrahedron.measure
    rw [htop, ENNReal.toReal_top]
  have hval := measure_sphere_two_section a ha
  have hpos : 0 < 4 * Real.pi * faceScale :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) faceScale_pos
  linarith

private lemma measure2_facet_eq_openFacet (u : NormalTuple)
    (hz0 : ∃ z₀ : E4, ∀ i : Fin 4, 0 < inner ℝ (u i : E4) z₀) (v : S3) (hv : v ∈ Finset.image u Finset.univ) :
    let V := Finset.image u Finset.univ
    measure 2 {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧ ∀ w ∈ V, 0 ≤ inner ℝ (w : E4) x} =
      measure 2 {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
        ∀ w ∈ V, w ≠ v → 0 < inner ℝ (w : E4) x} := by
  intro V
  rcases hz0 with ⟨z₀, hz₀⟩
  let A : Set E4 :=
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧ ∀ w ∈ V, 0 ≤ inner ℝ (w : E4) x}
  let B : Set E4 :=
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧ ∀ w ∈ V, w ≠ v → 0 < inner ℝ (w : E4) x}
  have hBA : B ⊆ A := by
    rintro x ⟨hx, hvx, hpos⟩
    refine ⟨hx, hvx, fun w hw => ?_⟩
    by_cases hwv : w = v
    · rw [hwv, hvx]
    · exact (hpos w hw hwv).le
  have hdiff_null : MeasureTheory.Measure.hausdorffMeasure 2 (A \ B) = 0 := by
    have hsub : A \ B ⊆ ⋃ w ∈ V.erase v,
        {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧ inner ℝ (w : E4) x = 0} := by
      rintro x ⟨⟨hx, hvx, hnn⟩, hxB⟩
      simp only [B, Set.mem_setOf_eq, not_and, not_forall, not_lt] at hxB
      obtain ⟨w, hwV, hw_ne, hle⟩ := hxB hx hvx
      exact Set.mem_iUnion₂.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne, hwV⟩,
        hx, hvx, le_antisymm hle (hnn w hwV)⟩
    have hunion : MeasureTheory.Measure.hausdorffMeasure 2
        (⋃ w ∈ V.erase v,
          {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧ inner ℝ (w : E4) x = 0}) = 0 := by
      refine (MeasureTheory.measure_biUnion_null_iff (V.erase v).countable_toSet).mpr fun w hw => ?_
      have hw' : w ∈ V.erase v := Finset.mem_coe.mp hw
      rw [Finset.mem_erase] at hw'
      have hv_norm : ‖(v : E4)‖ = 1 := by simp [Metric.mem_sphere, dist_zero_right]
      have hw_norm : ‖(w : E4)‖ = 1 := by simp [Metric.mem_sphere, dist_zero_right]
      have hvw_ne : (v : E4) ≠ (w : E4) := fun heq => hw'.1 (Subtype.ext heq.symm)
      have hv_pos : 0 < inner ℝ (v : E4) z₀ := by
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
        rw [← hi]; exact hz₀ i
      have hw_pos : 0 < inner ℝ (w : E4) z₀ := by
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hw'.2
        rw [← hj]; exact hz₀ j
      have hvw_neg : (v : E4) ≠ -(w : E4) := by
        intro heq
        have hsum : inner ℝ (v : E4) z₀ + inner ℝ (w : E4) z₀ = 0 := by
          rw [heq, inner_neg_left]; ring
        linarith
      exact circle_pair_null hv_norm hw_norm hvw_ne hvw_neg
    exact measure_mono_null hsub hunion
  have hle1 : MeasureTheory.Measure.hausdorffMeasure 2 B ≤ MeasureTheory.Measure.hausdorffMeasure 2 A :=
    measure_mono hBA
  have hle2 : MeasureTheory.Measure.hausdorffMeasure 2 A ≤ MeasureTheory.Measure.hausdorffMeasure 2 B := by
    have hcov : A ⊆ B ∪ (A \ B) := fun x hx => by
      by_cases hxB : x ∈ B <;> [exact Or.inl hxB; exact Or.inr ⟨hx, hxB⟩]
    calc MeasureTheory.Measure.hausdorffMeasure 2 A
        ≤ MeasureTheory.Measure.hausdorffMeasure 2 (B ∪ (A \ B)) := measure_mono hcov
      _ ≤ MeasureTheory.Measure.hausdorffMeasure 2 B +
            MeasureTheory.Measure.hausdorffMeasure 2 (A \ B) := measure_union_le B (A \ B)
      _ = MeasureTheory.Measure.hausdorffMeasure 2 B := by rw [hdiff_null, add_zero]
  change measure 2 A = measure 2 B
  simp only [measure, le_antisymm hle2 hle1]

private noncomputable def tangProj (v : E4) (y : E4) : E4 :=
  ‖y - inner ℝ v y • v‖⁻¹ • (y - inner ℝ v y • v)

private lemma tangProj_lipschitz {v : E4} (hv : ‖v‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    LipschitzOnWith ⟨(√(1 - ε ^ 2))⁻¹, by positivity⟩ (tangProj v)
      {y : E4 | ‖y‖ = 1 ∧ |inner ℝ v y| ≤ ε} := by
  have h1me_pos : 0 < 1 - ε ^ 2 := by nlinarith
  have hc_pos : 0 < √(1 - ε ^ 2) := Real.sqrt_pos.mpr h1me_pos
  refine lipschitzOnWith_iff_dist_le_mul.mpr ?_
  intro y₁ hy₁ y₂ hy₂
  let w₁ : E4 := y₁ - inner ℝ v y₁ • v
  let w₂ : E4 := y₂ - inner ℝ v y₂ • v
  have hw₁_orth : inner ℝ v w₁ = 0 := by
    dsimp [w₁]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one, sub_self]
  have hw₂_orth : inner ℝ v w₂ = 0 := by
    dsimp [w₂]
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow, mul_one, sub_self]
  have hw₁_sq : ‖w₁‖ ^ 2 = 1 - inner ℝ v y₁ ^ 2 := by
    have hpy : y₁ = w₁ + inner ℝ v y₁ • v := by dsimp [w₁]; abel
    have hnorm : ‖y₁‖ ^ 2 = ‖w₁‖ ^ 2 + inner ℝ v y₁ ^ 2 := by
      conv_lhs => rw [hpy]
      rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm v w₁, hw₁_orth,
        norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
      ring
    rw [hy₁.1, one_pow] at hnorm
    linarith
  have hw₂_sq : ‖w₂‖ ^ 2 = 1 - inner ℝ v y₂ ^ 2 := by
    have hpy : y₂ = w₂ + inner ℝ v y₂ • v := by dsimp [w₂]; abel
    have hnorm : ‖y₂‖ ^ 2 = ‖w₂‖ ^ 2 + inner ℝ v y₂ ^ 2 := by
      conv_lhs => rw [hpy]
      rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm v w₂, hw₂_orth,
        norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
      ring
    rw [hy₂.1, one_pow] at hnorm
    linarith
  have hw₁_ge : 1 - ε ^ 2 ≤ ‖w₁‖ ^ 2 := by
    have : inner ℝ v y₁ ^ 2 ≤ ε ^ 2 := sq_le_sq' (by linarith [abs_le.mp hy₁.2]) (abs_le.mp hy₁.2).2
    linarith
  have hw₂_ge : 1 - ε ^ 2 ≤ ‖w₂‖ ^ 2 := by
    have : inner ℝ v y₂ ^ 2 ≤ ε ^ 2 := sq_le_sq' (by linarith [abs_le.mp hy₂.2]) (abs_le.mp hy₂.2).2
    linarith
  have hw₁_pos : 0 < ‖w₁‖ := by
    have : 0 < ‖w₁‖ ^ 2 := by linarith
    by_contra! hle
    have h0 := le_antisymm hle (norm_nonneg _)
    rw [h0, zero_pow (by decide)] at this
    exact lt_irrefl 0 this
  have hw₂_pos : 0 < ‖w₂‖ := by
    have : 0 < ‖w₂‖ ^ 2 := by linarith
    by_contra! hle
    have h0 := le_antisymm hle (norm_nonneg _)
    rw [h0, zero_pow (by decide)] at this
    exact lt_irrefl 0 this
  have hw_diff : ‖w₁ - w₂‖ ^ 2 ≤ ‖y₁ - y₂‖ ^ 2 := by
    have hdec : y₁ - y₂ = (w₁ - w₂) + (inner ℝ v y₁ - inner ℝ v y₂) • v := by
      dsimp [w₁, w₂]; module
    have horth : inner ℝ (w₁ - w₂) ((inner ℝ v y₁ - inner ℝ v y₂) • v) = 0 := by
      rw [inner_smul_right, inner_sub_left, real_inner_comm v w₁, real_inner_comm v w₂,
        hw₁_orth, hw₂_orth]
      simp
    rw [hdec, norm_add_sq_real, horth]
    linarith [sq_nonneg ‖(inner ℝ v y₁ - inner ℝ v y₂) • v‖]
  have hid : ‖w₁‖ * ‖w₂‖ * ‖tangProj v y₁ - tangProj v y₂‖ ^ 2 =
      ‖w₁ - w₂‖ ^ 2 - (‖w₁‖ - ‖w₂‖) ^ 2 := by
    have hnu1 : ‖tangProj v y₁‖ = 1 := by
      change ‖‖w₁‖⁻¹ • w₁‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hw₁_pos.le), inv_mul_cancel₀ hw₁_pos.ne']
    have hnu2 : ‖tangProj v y₂‖ = 1 := by
      change ‖‖w₂‖⁻¹ • w₂‖ = 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hw₂_pos.le), inv_mul_cancel₀ hw₂_pos.ne']
    have hin : inner ℝ (tangProj v y₁) (tangProj v y₂) = (‖w₁‖ * ‖w₂‖)⁻¹ * inner ℝ w₁ w₂ := by
      change inner ℝ (‖w₁‖⁻¹ • w₁) (‖w₂‖⁻¹ • w₂) = _
      rw [inner_smul_left, inner_smul_right]
      simp only [conj_trivial]
      field_simp [hw₁_pos.ne', hw₂_pos.ne']
    rw [norm_sub_sq_real (tangProj v y₁) (tangProj v y₂), hnu1, hnu2, hin]
    rw [norm_sub_sq_real w₁ w₂]
    field_simp [hw₁_pos.ne', hw₂_pos.ne']
    ring
  have hprod_ge : 1 - ε ^ 2 ≤ ‖w₁‖ * ‖w₂‖ := by
    have h1 : √(1 - ε ^ 2) ≤ ‖w₁‖ := (Real.sqrt_le_iff.mpr ⟨hw₁_pos.le, hw₁_ge⟩)
    have h2 : √(1 - ε ^ 2) ≤ ‖w₂‖ := (Real.sqrt_le_iff.mpr ⟨hw₂_pos.le, hw₂_ge⟩)
    calc 1 - ε ^ 2 = √(1 - ε ^ 2) * √(1 - ε ^ 2) := (Real.mul_self_sqrt h1me_pos.le).symm
      _ ≤ ‖w₁‖ * ‖w₂‖ := mul_le_mul h1 h2 hc_pos.le hw₁_pos.le
  have hsq_bound : (1 - ε ^ 2) * dist (tangProj v y₁) (tangProj v y₂) ^ 2 ≤ dist y₁ y₂ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm]
    calc (1 - ε ^ 2) * ‖tangProj v y₁ - tangProj v y₂‖ ^ 2
        ≤ (‖w₁‖ * ‖w₂‖) * ‖tangProj v y₁ - tangProj v y₂‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hprod_ge (sq_nonneg _)
      _ = ‖w₁ - w₂‖ ^ 2 - (‖w₁‖ - ‖w₂‖) ^ 2 := hid
      _ ≤ ‖w₁ - w₂‖ ^ 2 := sub_le_self _ (sq_nonneg _)
      _ ≤ ‖y₁ - y₂‖ ^ 2 := hw_diff
  have hdiv : dist (tangProj v y₁) (tangProj v y₂) ^ 2 ≤ ((√(1 - ε ^ 2))⁻¹ * dist y₁ y₂) ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt h1me_pos.le, inv_mul_eq_div]
    exact (le_div_iff₀' h1me_pos).mpr hsq_bound
  change dist (tangProj v y₁) (tangProj v y₂) ≤ (√(1 - ε ^ 2))⁻¹ * dist y₁ y₂
  exact le_of_sq_le_sq hdiv (by positivity)

private lemma measure2_K_le_scaled_area (u : NormalTuple) (S : SphericalTetrahedron)
    {δ ε η : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr_le : min (δ / 4) ε ≤ ε)
    (hη_pos : 0 < η) (hη_half : η ≤ 1 / 2)
    (hη_r : η ≤ min (δ / 4) ε / 4) (hη_d : η ≤ δ / 4)
    (hnorm : ∀ i : Fin 4, ‖S.normal i - (u i : E4)‖ ≤ η) :
    let V := Finset.image u Finset.univ
    let K_set : S3 → Set E4 := fun v =>
      {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
        ∀ w ∈ V, w ≠ v → δ ≤ inner ℝ (w : E4) x}
    ∑ v ∈ V, measure 2 (K_set v) ≤ (1 - ε ^ 2)⁻¹ * S.area := by
  intro V K_set
  let r : ℝ := min (δ / 4) ε
  have hr_pos : 0 < r := lt_min (by linarith) hε0
  have h1me_pos : 0 < 1 - ε ^ 2 := by nlinarith
  have hK_cov : ∀ v ∈ V,
      K_set v ⊆ tangProj (v : E4) ''
        (⋃ (i : Fin 4) (_ : u i = v),
          (S.face i ∩ {y : E4 | ‖y‖ = 1 ∧ |inner ℝ (v : E4) y| ≤ ε})) := by
    intro v hv x hx
    let Iv : Finset (Fin 4) := Finset.univ.filter fun i => u i = v
    have hIv : Iv.Nonempty := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hv_norm : ‖(v : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using v.2
    have hx_norm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx.1
    have hIv_pos : ∀ i ∈ Iv, 1 / 2 ≤ inner ℝ (S.normal i) (v : E4) := by
      intro i hi
      have hui : (u i : E4) = (v : E4) := congrArg Subtype.val (Finset.mem_filter.mp hi).2
      have hsub : |inner ℝ (S.normal i - (v : E4)) (v : E4)| ≤ η := by
        calc |inner ℝ (S.normal i - (v : E4)) (v : E4)|
            ≤ ‖S.normal i - (v : E4)‖ * ‖(v : E4)‖ := abs_real_inner_le_norm _ _
          _ ≤ η * 1 := mul_le_mul (by simpa [hui] using hnorm i) (by linarith [hv_norm])
              (norm_nonneg _) hη_pos.le
          _ = η := mul_one η
      have hvv : inner ℝ (v : E4) (v : E4) = 1 := by rw [real_inner_self_eq_norm_sq, hv_norm, one_pow]
      rw [inner_sub_left, hvv] at hsub
      linarith [(abs_le.mp hsub).1]
    have hIv_x : ∀ i ∈ Iv, |inner ℝ (S.normal i) x| ≤ η := by
      intro i hi
      have hui : (u i : E4) = (v : E4) := congrArg Subtype.val (Finset.mem_filter.mp hi).2
      have hvx : inner ℝ (v : E4) x = 0 := hx.2.1
      calc |inner ℝ (S.normal i) x| = |inner ℝ (S.normal i - (v : E4)) x| := by
            rw [inner_sub_left, hvx, sub_zero]
        _ ≤ ‖S.normal i - (v : E4)‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ η * 1 := mul_le_mul (by simpa [hui] using hnorm i) (by linarith [hx_norm])
            (norm_nonneg _) hη_pos.le
        _ = η := mul_one η
    let f : Fin 4 → ℝ := fun i => -inner ℝ (S.normal i) x / inner ℝ (S.normal i) (v : E4)
    obtain ⟨i_star, hi_star, hmax⟩ := Finset.exists_mem_eq_sup' hIv f
    set t_star : ℝ := Iv.sup' hIv f
    have ht_star_eq : t_star = f i_star := hmax
    have ht_le : |t_star| ≤ r := by
      have hi_bd : |f i_star| ≤ r := by
        dsimp [f]
        have hden : 1 / 2 ≤ inner ℝ (S.normal i_star) (v : E4) := hIv_pos i_star hi_star
        have hden_pos : 0 < inner ℝ (S.normal i_star) (v : E4) := by linarith
        have hnum : |inner ℝ (S.normal i_star) x| ≤ η := hIv_x i_star hi_star
        rw [abs_div, abs_neg, abs_of_pos (a := inner ℝ (S.normal i_star) (v : E4)) hden_pos]
        calc |inner ℝ (S.normal i_star) x| / inner ℝ (S.normal i_star) (v : E4)
            ≤ η / (1 / 2) := div_le_div₀ hη_pos.le hnum (by norm_num) hden
          _ = 2 * η := by ring
          _ ≤ r := by linarith [hη_r]
      rwa [ht_star_eq]
    let z : E4 := x + t_star • (v : E4)
    have hz_sq : ‖z‖ ^ 2 = 1 + t_star ^ 2 := by
      dsimp [z]
      rw [norm_add_sq_real, hx_norm, one_pow, inner_smul_right, real_inner_comm (v : E4) x,
        hx.2.1, mul_zero, mul_zero, add_zero, norm_smul, Real.norm_eq_abs, hv_norm, mul_one, sq_abs]
    have hz_ge1 : 1 ≤ ‖z‖ := by
      have hsq : 1 ^ 2 ≤ ‖z‖ ^ 2 := by linarith [sq_nonneg t_star]
      exact le_of_sq_le_sq hsq (norm_nonneg z)
    have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz_ge1
    let y : E4 := ‖z‖⁻¹ • z
    have hy_norm : ‖y‖ = 1 := by
      dsimp [y]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hz_pos.le), inv_mul_cancel₀ hz_pos.ne']
    have hz_nonneg : ∀ i : Fin 4, 0 ≤ inner ℝ (S.normal i) z := by
      intro i
      by_cases hi : i ∈ Iv
      · have hge : f i ≤ t_star := Finset.le_sup' f hi
        have hden : 0 < inner ℝ (S.normal i) (v : E4) := by linarith [hIv_pos i hi]
        have hmul : -inner ℝ (S.normal i) x ≤ t_star * inner ℝ (S.normal i) (v : E4) :=
          (div_le_iff₀ hden).mp hge
        dsimp [z]
        rw [inner_add_right, inner_smul_right]
        linarith
      · have hui_ne : u i ≠ v := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        have hui_V : u i ∈ V := Finset.mem_image_of_mem u (Finset.mem_univ i)
        have hdelta : δ ≤ inner ℝ (u i : E4) x := hx.2.2 (u i) hui_V hui_ne
        have herr : |inner ℝ (S.normal i - (u i : E4)) x| ≤ η := by
          calc |inner ℝ (S.normal i - (u i : E4)) x|
              ≤ ‖S.normal i - (u i : E4)‖ * ‖x‖ := abs_real_inner_le_norm _ _
            _ ≤ η * 1 := mul_le_mul (hnorm i) (by linarith [hx_norm]) (norm_nonneg _) hη_pos.le
            _ = η := mul_one η
        have htx : |t_star * inner ℝ (S.normal i) (v : E4)| ≤ r := by
          rw [abs_mul]
          have hiv : |inner ℝ (S.normal i) (v : E4)| ≤ 1 := by
            calc |inner ℝ (S.normal i) (v : E4)|
                ≤ ‖S.normal i‖ * ‖(v : E4)‖ := abs_real_inner_le_norm _ _
              _ = 1 := by rw [S.unit i, hv_norm, mul_one]
          calc |t_star| * |inner ℝ (S.normal i) (v : E4)|
              ≤ r * 1 := mul_le_mul ht_le hiv (abs_nonneg _) hr_pos.le
            _ = r := mul_one r
        have hsum : inner ℝ (S.normal i) z =
            inner ℝ (u i : E4) x + inner ℝ (S.normal i - (u i : E4)) x +
              t_star * inner ℝ (S.normal i) (v : E4) := by
          dsimp [z]
          rw [inner_add_right, inner_smul_right, inner_sub_left]
          ring
        have hr_d : r ≤ δ / 4 := min_le_left _ _
        linarith [(abs_le.mp herr).1, (abs_le.mp htx).1]
    have histar_zero : inner ℝ (S.normal i_star) z = 0 := by
      have hden : inner ℝ (S.normal i_star) (v : E4) ≠ 0 := by
        linarith [hIv_pos i_star hi_star]
      dsimp [z]
      rw [inner_add_right, inner_smul_right, ht_star_eq]
      dsimp [f]
      field_simp [hden]
      ring
    have hy_face : y ∈ S.face i_star := by
      refine ⟨⟨hy_norm, fun i => ?_⟩, ?_⟩
      · dsimp [y]; rw [real_inner_smul_right]
        exact mul_nonneg (inv_nonneg.mpr hz_pos.le) (hz_nonneg i)
      · dsimp [y]; rw [real_inner_smul_right, histar_zero, mul_zero]
    have hy_slab : |inner ℝ (v : E4) y| ≤ ε := by
      have hvy : inner ℝ (v : E4) y = ‖z‖⁻¹ * t_star := by
        dsimp [y, z]
        rw [inner_smul_right, inner_add_right, hx.2.1, zero_add, inner_smul_right,
          real_inner_self_eq_norm_sq, hv_norm, one_pow, mul_one]
      rw [hvy, abs_mul, abs_of_pos (inv_pos.mpr hz_pos)]
      have hinv_le : ‖z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hz_ge1
      calc ‖z‖⁻¹ * |t_star| ≤ 1 * r := mul_le_mul hinv_le ht_le (abs_nonneg _) zero_le_one
        _ = r := one_mul r
        _ ≤ ε := hr_le
    have hproj_y : tangProj (v : E4) y = x := by
      have hvy : inner ℝ (v : E4) y = ‖z‖⁻¹ * t_star := by
        dsimp [y, z]
        rw [inner_smul_right, inner_add_right, hx.2.1, zero_add, inner_smul_right,
          real_inner_self_eq_norm_sq, hv_norm, one_pow, mul_one]
      have hw : y - inner ℝ (v : E4) y • (v : E4) = ‖z‖⁻¹ • x := by
        dsimp [y, z]
        rw [hvy, smul_add, smul_smul, add_sub_cancel_right]
      dsimp [tangProj]
      rw [hw, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hz_pos).le, hx_norm, mul_one, inv_inv,
        smul_smul, mul_inv_cancel₀ hz_pos.ne', one_smul]
    refine ⟨y, Set.mem_iUnion.mpr ⟨i_star, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hi_star).2,
      hy_face, hy_norm, hy_slab⟩⟩, hproj_y⟩
  have hterm : ∀ v ∈ V,
      measure 2 (K_set v) ≤
        (1 - ε ^ 2)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => u i = v), measure 2 (S.face i) := by
    intro v hv
    have hv_norm : ‖(v : E4)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using v.2
    let s_v := ⋃ (i : Fin 4) (_ : u i = v),
      (S.face i ∩ {y : E4 | ‖y‖ = 1 ∧ |inner ℝ (v : E4) y| ≤ ε})
    let K_lip : NNReal := ⟨(√(1 - ε ^ 2))⁻¹, by positivity⟩
    have hlip := tangProj_lipschitz hv_norm hε0.le hε1
    have hlip_sub : LipschitzOnWith K_lip (tangProj (v : E4)) s_v := by
      refine hlip.mono ?_
      intro y hy
      simp only [s_v, Set.mem_iUnion, Set.mem_inter_iff] at hy
      rcases hy with ⟨_, _, _, hy1, hy2⟩
      exact ⟨hy1, hy2⟩
    have himg := hlip_sub.hausdorffMeasure_image_le (d := 2) zero_le_two
    have hmono : MeasureTheory.Measure.hausdorffMeasure 2 (K_set v) ≤
        MeasureTheory.Measure.hausdorffMeasure 2 (tangProj (v : E4) '' s_v) :=
      measure_mono (hK_cov v hv)
    have hs_v_sub : s_v ⊆ ⋃ i ∈ Finset.univ.filter (fun i => u i = v), S.face i := by
      intro y hy
      simp only [s_v, Set.mem_iUnion, Set.mem_inter_iff] at hy
      rcases hy with ⟨i, hi, hyf, _⟩
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, hyf⟩
    have hsv_union : MeasureTheory.Measure.hausdorffMeasure 2 s_v ≤
        ∑ i ∈ Finset.univ.filter (fun i => u i = v),
          MeasureTheory.Measure.hausdorffMeasure 2 (S.face i) := by
      exact (measure_mono hs_v_sub).trans (MeasureTheory.measure_biUnion_finset_le _ _)
    have hface_ne_top : ∀ i : Fin 4, MeasureTheory.Measure.hausdorffMeasure 2 (S.face i) ≠ ⊤ := by
      intro i
      have hsub : S.face i ⊆ {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (S.normal i) x = 0} := by
        rintro x ⟨⟨hx1, _⟩, hix⟩
        exact ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hx1, hix⟩
      exact (lt_of_le_of_lt (measure_mono hsub)
        (lt_top_iff_ne_top.mpr (measure2_sphere_section_ne_top (S.unit i)))).ne
    have hsum_ne_top :
        (∑ i ∈ Finset.univ.filter (fun i => u i = v),
          MeasureTheory.Measure.hausdorffMeasure 2 (S.face i)) ≠ ⊤ :=
      ENNReal.sum_lt_top.mpr (fun i _ => lt_top_iff_ne_top.mpr (hface_ne_top i)) |>.ne
    have hK_coe : (K_lip : ℝ≥0∞) ^ (2 : ℝ) = ENNReal.ofReal ((1 - ε ^ 2)⁻¹) := by
      have hsq : ((K_lip : ℝ) ^ (2 : ℕ)) = (1 - ε ^ 2)⁻¹ := by
        change ((√(1 - ε ^ 2))⁻¹) ^ 2 = (1 - ε ^ 2)⁻¹
        rw [inv_pow, Real.sq_sqrt h1me_pos.le]
      rw [← ENNReal.coe_rpow_of_nonneg _ zero_le_two]
      change (((K_lip ^ (2 : ℝ)) : NNReal) : ℝ≥0∞) = _
      rw [NNReal.rpow_two, ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr h1me_pos.le)]
      congr 1
      ext
      simpa using hsq
    have hbound_enn : MeasureTheory.Measure.hausdorffMeasure 2 (K_set v) ≤
        ENNReal.ofReal ((1 - ε ^ 2)⁻¹) *
          ∑ i ∈ Finset.univ.filter (fun i => u i = v),
            MeasureTheory.Measure.hausdorffMeasure 2 (S.face i) := by
      rw [← hK_coe]
      exact (hmono.trans himg).trans (mul_le_mul_right hsv_union _)
    have hfin_rhs : ENNReal.ofReal ((1 - ε ^ 2)⁻¹) *
        (∑ i ∈ Finset.univ.filter (fun i => u i = v),
          MeasureTheory.Measure.hausdorffMeasure 2 (S.face i)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum_ne_top
    have htoReal := ENNReal.toReal_mono hfin_rhs hbound_enn
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr h1me_pos.le),
      ENNReal.toReal_sum (fun i _ => hface_ne_top i)] at htoReal
    simpa [measure] using htoReal
  calc ∑ v ∈ V, measure 2 (K_set v)
      ≤ ∑ v ∈ V, (1 - ε ^ 2)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i => u i = v), measure 2 (S.face i) :=
        Finset.sum_le_sum hterm
    _ = (1 - ε ^ 2)⁻¹ *
          ∑ v ∈ V, ∑ i ∈ Finset.univ.filter (fun i => u i = v), measure 2 (S.face i) := by
        rw [Finset.mul_sum]
    _ = (1 - ε ^ 2)⁻¹ * ∑ i : Fin 4, measure 2 (S.face i) := by
        congr 1
        exact Finset.sum_fiberwise_of_maps_to
          (fun i _ => Finset.mem_image_of_mem u (Finset.mem_univ i)) _
    _ = (1 - ε ^ 2)⁻¹ * S.area := rfl

private lemma iUnion_K_m_eq_openF (V : Finset S3) (v : S3) :
    (⋃ m : ℕ, {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
      ∀ w ∈ V, w ≠ v → (1 : ℝ) / (m + 1 : ℝ) ≤ inner ℝ (w : E4) x}) =
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
      ∀ w ∈ V, w ≠ v → 0 < inner ℝ (w : E4) x} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hx1, hx2, hx3⟩
    have hpos : (0 : ℝ) < (1 : ℝ) / (m + 1 : ℝ) := one_div_pos.mpr (Nat.cast_add_one_pos m)
    exact ⟨hx1, hx2, fun w hw hwv => lt_of_lt_of_le hpos (hx3 w hw hwv)⟩
  · rintro ⟨hx1, hx2, hx3⟩
    by_cases hne : (V.erase v).Nonempty
    · have hpos_min : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ V.erase v, δ ≤ inner ℝ (w : E4) x := by
        let m0 := (V.erase v).inf' hne fun w => inner ℝ (w : E4) x
        obtain ⟨w0, hw0, hm0⟩ := Finset.exists_mem_eq_inf' hne fun w => inner ℝ (w : E4) x
        refine ⟨m0, ?_, fun w hw => ?_⟩
        · dsimp [m0]
          rw [hm0]
          have hw0' := Finset.mem_erase.mp hw0
          exact hx3 w0 hw0'.2 hw0'.1
        · exact Finset.inf'_le _ hw
      rcases hpos_min with ⟨δ, hδ, hle⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      exact ⟨m, hx1, hx2, fun w hw hwv =>
        hm.le.trans (hle w (Finset.mem_erase.mpr ⟨hwv, hw⟩))⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨0, hx1, hx2, fun w hw hwv => ?_⟩
      have : w ∈ V.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
      rw [hne] at this
      exact False.elim (Finset.notMem_empty w this)

private lemma area_sum_le_of_tendsto_strict_interior (T : SphericalTetrahedron) (u : NormalTuple)
    (hz0 : ∃ z₀ : E4, ∀ i : Fin 4, 0 < inner ℝ (u i : E4) z₀)
    {s : ℕ → SphericalTetrahedron} (hs_area : ∀ n, (s n).area = T.area)
    (hs_lim : Filter.Tendsto (fun n => normalOf (s n)) Filter.atTop (nhds u)) :
    let V := Finset.image u Finset.univ
    ∑ v ∈ V, measure 2
        {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
          ∀ w ∈ V, 0 ≤ inner ℝ (w : E4) x} ≤
      T.area := by
  intro V
  let openF : S3 → Set E4 := fun v =>
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
      ∀ w ∈ V, w ≠ v → 0 < inner ℝ (w : E4) x}
  let K_m : ℕ → S3 → Set E4 := fun m v =>
    {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
      ∀ w ∈ V, w ≠ v → (1 : ℝ) / (m + 1 : ℝ) ≤ inner ℝ (w : E4) x}
  have heq_open : ∑ v ∈ V, measure 2
        {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0 ∧
          ∀ w ∈ V, 0 ≤ inner ℝ (w : E4) x} =
      ∑ v ∈ V, measure 2 (openF v) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    exact measure2_facet_eq_openFacet u hz0 v hv
  have hK_bound : ∀ m : ℕ, ∑ v ∈ V, measure 2 (K_m m v) ≤ T.area := by
    intro m
    let δ : ℝ := (1 : ℝ) / (m + 1 : ℝ)
    have hδ : 0 < δ := by positivity
    have hε_tend : Filter.Tendsto (fun ε : ℝ => (1 - ε ^ 2)⁻¹ * T.area)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds T.area) := by
      have hne : (1 : ℝ) - (0 : ℝ) ^ 2 ≠ 0 := by norm_num
      have hc : ContinuousAt (fun ε : ℝ => (1 - ε ^ 2)⁻¹ * T.area) 0 :=
        ((continuousAt_const.sub (continuousAt_id.pow 2)).inv₀ hne).mul continuousAt_const
      have hten0 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      have h0 : (1 - (0 : ℝ) ^ 2)⁻¹ * T.area = T.area := by norm_num
      rwa [h0] at hten0
    have hle_eps : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∑ v ∈ V, measure 2 (K_m m v) ≤ (1 - ε ^ 2)⁻¹ * T.area := by
      have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, Set.mem_Iio.mpr one_pos, fun _ h => ⟨h.2, h.1⟩⟩
      filter_upwards [hIoo] with ε hε
      let r := min (δ / 4) ε
      let η := min (1 / 2 : ℝ) (min (r / 4) (δ / 4))
      have hη_pos : 0 < η := by
        have hr_pos : 0 < r := lt_min (by linarith) hε.1
        exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))
      have hcoord : ∀ i : Fin 4, ∀ᶠ n in Filter.atTop,
          ‖(s n).normal i - (u i : E4)‖ ≤ η := fun i => by
        have hci : Filter.Tendsto (fun n => (s n).normal i) Filter.atTop (nhds (u i : E4)) :=
          (continuous_subtype_val.continuousAt.tendsto).comp (tendsto_pi_nhds.mp hs_lim i)
        exact (Metric.tendsto_nhds.mp hci η hη_pos).mono fun _ hn => by
          simpa [Real.dist_eq, dist_eq_norm] using hn.le
      obtain ⟨n, hn⟩ := (eventually_all.mpr hcoord).exists
      have hbd := measure2_K_le_scaled_area u (s n) hδ hε.1 hε.2 (min_le_right _ _)
        hη_pos (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans (min_le_right _ _)) hn
      rw [hs_area n] at hbd
      exact hbd
    exact ge_of_tendsto hε_tend hle_eps
  have hK_tend : Filter.Tendsto (fun m : ℕ => ∑ v ∈ V, measure 2 (K_m m v))
      Filter.atTop (nhds (∑ v ∈ V, measure 2 (openF v))) := by
    refine tendsto_finsetSum V fun v _ => ?_
    have hmono : Monotone (fun m => K_m m v) := by
      intro m₁ m₂ hm x hx
      refine ⟨hx.1, hx.2.1, fun w hw hwv => ?_⟩
      have hdiv : (1 : ℝ) / (m₂ + 1 : ℝ) ≤ (1 : ℝ) / (m₁ + 1 : ℝ) :=
        one_div_le_one_div_of_le (Nat.cast_add_one_pos m₁) (by exact_mod_cast Nat.add_le_add_right hm 1)
      exact hdiv.trans (hx.2.2 w hw hwv)
    have hunion : ⋃ m : ℕ, K_m m v = openF v := iUnion_K_m_eq_openF V v
    let μ2 : MeasureTheory.Measure E4 := MeasureTheory.Measure.hausdorffMeasure 2
    have hten : Filter.Tendsto (fun m => μ2 (K_m m v)) Filter.atTop (nhds (μ2 (openF v))) := by
      rw [← hunion]
      exact MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ2) hmono
    have hv_norm : ‖(v : E4)‖ = 1 := by simp [Metric.mem_sphere, dist_zero_right]
    have hopen_ne_top : μ2 (openF v) ≠ ⊤ := by
      have hsub : openF v ⊆ {x : E4 | x ∈ Metric.sphere 0 1 ∧ inner ℝ (v : E4) x = 0} :=
        fun _ hx => ⟨hx.1, hx.2.1⟩
      exact (lt_of_le_of_lt (measure_mono hsub)
        (lt_top_iff_ne_top.mpr (measure2_sphere_section_ne_top hv_norm))).ne
    exact (ENNReal.continuousAt_toReal hopen_ne_top).tendsto.comp hten
  rw [heq_open]
  exact le_of_tendsto hK_tend (Filter.Eventually.of_forall hK_bound)

/-- Existence of a nondegenerate volume maximizer among all spherical tetrahedra of the same
surface area as `T`. -/
theorem fixed_area_maximizer_exists_manuscript (T : SphericalTetrahedron) :
    ∃ M : SphericalTetrahedron,
      M.area = T.area ∧ ∀ S : SphericalTetrahedron, S.area = T.area → S.volume ≤ M.volume := by
  have : CompactSpace S3 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E4) 1)
  let F : Set NormalTuple := {u | ∃ S : SphericalTetrahedron, S.area = T.area ∧ normalOf S = u}
  let K : Set NormalTuple := closure F
  let good : NormalTuple → Prop := fun u => LinearIndependent ℝ (fun i : Fin 4 => (u i : E4))
  refine fixed_area_maximizer_of_manuscript_compactification T K volumeOf good
    isClosed_closure.isCompact ⟨normalOf T, subset_closure ⟨T, rfl, rfl⟩⟩
    continuous_volumeOf.continuousOn ?_ ?_ ?_
  · intro u hu hnot_good
    by_cases hz0 : ∃ z₀ : E4, ∀ i : Fin 4, 0 < inner ℝ (u i : E4) z₀
    · obtain ⟨s, hs_mem, hs_lim⟩ := mem_closure_iff_seq_limit.mp hu
      choose S hS_area hS_norm using hs_mem
      have hs_lim' : Filter.Tendsto (fun n => normalOf (S n)) Filter.atTop (nhds u) := by
        simpa [hS_norm] using hs_lim
      have harea_le := area_sum_le_of_tendsto_strict_interior T u hz0 hS_area hs_lim'
      rw [area_eq_faceScale_mul_stdArea] at harea_le
      have hA0 : 0 < T.stdArea := by
        have h0 := stdFaceArea_pos T 0
        have h1 := stdFaceArea_pos T 1
        have h2 := stdFaceArea_pos T 2
        have h3 := stdFaceArea_pos T 3
        change 0 < ∑ i : Fin 4, stdFaceArea T i
        rw [Fin.sum_univ_four]
        linarith
      have hA4pi : T.stdArea < 4 * Real.pi := stdArea_lt_four_pi T
      have hdeg := degenerate_limit_volume_le_square u hnot_good T.stdArea hA0 hA4pi harea_le
      obtain ⟨M, hM_area, hM_vol⟩ :=
        exists_tetrahedron_strictly_larger_volume_than_degenerate T.stdArea hA0 hA4pi
      rw [← area_eq_faceScale_mul_stdArea T] at hM_area
      refine ⟨normalOf M, subset_closure ⟨M, hM_area, rfl⟩, ?_⟩
      rw [volumeOf_normalOf M, volumeOf_eq_measure3]
      exact lt_of_le_of_lt hdeg hM_vol
    · have hzero : volumeOf u = 0 := by
        have hsub : bodyOf u ⊆ ⋃ i : Fin 4, {y : S3 | |inner ℝ (u i : E4) (y : E4)| ≤ 0} := by
          intro y hy
          have hy_not : ¬ ∀ i : Fin 4, 0 < inner ℝ (u i : E4) (y : E4) := fun h => hz0 ⟨y, h⟩
          push Not at hy_not
          rcases hy_not with ⟨i, hi_le⟩
          exact Set.mem_iUnion.mpr ⟨i, by simp [le_antisymm hi_le (hy i)]⟩
        have hle : MeasureTheory.volume.toSphere.real (bodyOf u) ≤ 0 := by
          calc MeasureTheory.volume.toSphere.real (bodyOf u)
              ≤ MeasureTheory.volume.toSphere.real
                  (⋃ i : Fin 4, {y : S3 | |inner ℝ (u i : E4) (y : E4)| ≤ 0}) :=
                MeasureTheory.measureReal_mono hsub
            _ ≤ ∑ i : Fin 4,
                  MeasureTheory.volume.toSphere.real {y : S3 | |inner ℝ (u i : E4) (y : E4)| ≤ 0} :=
                MeasureTheory.measureReal_iUnion_fintype_le _
            _ ≤ ∑ _i : Fin 4, (64 * (0 : ℝ)) :=
                Finset.sum_le_sum fun i _ =>
                  toSphere_slab_bound (by simpa [Metric.mem_sphere, dist_zero_right] using (u i).2) le_rfl
            _ = 0 := by norm_num
        have heq0 : MeasureTheory.volume.toSphere.real (bodyOf u) = 0 :=
          le_antisymm hle ENNReal.toReal_nonneg
        simp [volumeOf, heq0]
      refine ⟨normalOf T, subset_closure ⟨T, rfl, rfl⟩, ?_⟩
      rw [hzero, volumeOf_normalOf]
      exact tetrahedron_volume_pos T
  · intro u hu hgood
    obtain ⟨s, hs_mem, hs_lim⟩ := mem_closure_iff_seq_limit.mp hu
    choose S hS_area hS_norm using hs_mem
    let M : SphericalTetrahedron :=
      ⟨fun i => (u i : E4), fun i => by simpa [Metric.mem_sphere, dist_zero_right] using (u i).2,
        hgood⟩
    have hM_norm : normalOf M = u := by
      ext i
      rfl
    have hs_lim' : Filter.Tendsto (fun n => normalOf (S n)) Filter.atTop (nhds u) := by
      simpa [hS_norm] using hs_lim
    have hgram_lim : Filter.Tendsto (fun n => (S n).gramPoint) Filter.atTop (nhds M.gramPoint) := by
      have ht_pair : ∀ i j : Fin 4,
          Filter.Tendsto (fun n => inner ℝ ((S n).normal i) ((S n).normal j)) Filter.atTop
            (nhds (inner ℝ (M.normal i) (M.normal j))) := fun i j => by
        have hp1 : Filter.Tendsto (fun n => (S n).normal i) Filter.atTop (nhds (M.normal i)) :=
          (continuous_subtype_val.continuousAt.tendsto).comp (tendsto_pi_nhds.mp hs_lim' i)
        have hp2 : Filter.Tendsto (fun n => (S n).normal j) Filter.atTop (nhds (M.normal j)) :=
          (continuous_subtype_val.continuousAt.tendsto).comp (tendsto_pi_nhds.mp hs_lim' j)
        exact (continuous_inner (𝕜 := ℝ) (E := E4)).continuousAt.tendsto.comp (hp1.prodMk_nhds hp2)
      rw [tendsto_pi_nhds]
      intro k
      fin_cases k
      · simpa [gramPoint] using ht_pair 0 1
      · simpa [gramPoint] using ht_pair 0 2
      · simpa [gramPoint] using ht_pair 0 3
      · simpa [gramPoint] using ht_pair 1 2
      · simpa [gramPoint] using ht_pair 1 3
      · simpa [gramPoint] using ht_pair 2 3
    have hstd_lim : Filter.Tendsto (fun n => stdAreaGram ((S n).gramPoint)) Filter.atTop
        (nhds (stdAreaGram M.gramPoint)) :=
      (hasFDerivAt_stdAreaGram (gramPoint_mem_gramOpen M)).continuousAt.tendsto.comp hgram_lim
    have harea_lim : Filter.Tendsto (fun n => (S n).area) Filter.atTop (nhds M.area) := by
      have hmul := hstd_lim.const_mul faceScale
      rw [area_eq_faceScale_mul_stdArea M, stdArea_eq_stdAreaGram M]
      refine hmul.congr fun n => ?_
      rw [area_eq_faceScale_mul_stdArea (S n), stdArea_eq_stdAreaGram (S n)]
    have hT_lim : Filter.Tendsto (fun _ : ℕ => T.area) Filter.atTop (nhds M.area) :=
      harea_lim.congr (fun n => hS_area n)
    refine ⟨M, (tendsto_const_nhds_iff.mp hT_lim).symm, ?_⟩
    rw [← hM_norm, volumeOf_normalOf]
  · intro S hS
    exact ⟨normalOf S, subset_closure ⟨S, hS, rfl⟩, (volumeOf_normalOf S).symm⟩

end SphericalTetrahedron
