module

public import Sphere3.ManuscriptPsiIntegral
public import Sphere3.StationarityKernelAngleInequality
public import SphericalTetrahedron.StationaryKernelStrictConcavity
public import SphericalTetrahedron.ManuscriptKernelInverse

@[expose] public section

/-!
# Global analytic properties of `stationaryKernel` and `manuscriptKernelInverse`

This module establishes the global mapping and monotonicity properties of
`stationaryKernel` (`Φ`) on `(-1, 1)` and its inverse `g = manuscriptKernelInverse`
on `(0, 2)`:

1. `stationaryKernel x = Sphere3.manuscriptPhi x`, mapping `(-1, 1)` onto `(0, 2)`
   with endpoint limits `0` at `-1⁺` and `2` at `1⁻`.
2. Global derivative bound `stationaryKernelFirstDerivative x > 1 / 3` on `(-1, 1)`.
3. Smoothness and strict convexity of `g := manuscriptKernelInverse` on `(0, 2)`:
   `HasDerivAt g (stationaryKernelFirstDerivative (g s))⁻¹ s` and
   `StrictMonoOn (deriv g) (Ioo 0 2)`.
4. Strict concavity of `L(s) := Real.arccos (g s)` on `(0, 2)`, yielding
   `MonotoneOn (fun x => L (x + z) - L (x + y))` whenever `z ≤ y`.
-/

noncomputable section

namespace SphericalTetrahedron

open Filter Set
open scoped Topology

theorem stationaryKernel_eq_manuscriptPhi (x : ℝ) :
    stationaryKernel x = Sphere3.manuscriptPhi x := by
  unfold stationaryKernel Sphere3.manuscriptPhi Sphere3.manuscriptPsi
  ring

theorem stationaryKernel_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < stationaryKernel x := by
  rw [stationaryKernel_eq_manuscriptPhi]
  exact Sphere3.manuscriptPhi_pos hx

theorem stationaryKernel_lt_two {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    stationaryKernel x < 2 := by
  set θ : ℝ := Real.arccos x
  have hθ0 : 0 < θ := Real.arccos_pos.mpr hx.2
  have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr hx.1
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hcos : Real.cos θ = x := Real.cos_arccos hx.1.le hx.2.le
  have htrig := Sphere3.angle_mul_one_add_cos_lt_two_sin θ hθ0 hθpi
  rw [stationaryKernel_eq_manuscriptPhi, ← hcos, Sphere3.manuscriptPhi_cos hθ0 hθpi]
  exact (div_lt_iff₀ hsin).mpr (by simpa [hcos] using htrig)

theorem stationaryKernel_mapsTo :
    Set.MapsTo stationaryKernel (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (0 : ℝ) 2) :=
  fun _ hx => ⟨stationaryKernel_pos hx, stationaryKernel_lt_two hx⟩

theorem stationaryKernel_tendsto_zero :
    Tendsto stationaryKernel (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝[>] (-1 : ℝ) :=
    Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1)
  have hrewrite :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        stationaryKernel x =
          (Real.sqrt (1 + x) / Real.sqrt (1 - x)) * Real.arccos x := by
    intro x hx
    have h1px : 0 < 1 + x := by linarith [hx.1]
    have h1mx : 0 < 1 - x := by linarith [hx.2]
    have hs1 : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr h1px
    have hsqrt_prod :
        Real.sqrt (1 - x ^ 2) = Real.sqrt (1 + x) * Real.sqrt (1 - x) := by
      rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring, Real.sqrt_mul h1px.le]
    have hsq : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1px.le
    unfold stationaryKernel
    rw [hsqrt_prod]
    field_simp [hs1.ne', (Real.sqrt_pos.mpr h1mx).ne']
    rw [hsq]
    ring
  have hlim_fn :
      Tendsto (fun x : ℝ => (Real.sqrt (1 + x) / Real.sqrt (1 - x)) * Real.arccos x)
        (𝓝 (-1 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.sqrt (1 + x)) (𝓝 (-1 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ => Real.sqrt (1 + x)) := by fun_prop
      simpa using (hc.continuousAt (x := (-1 : ℝ))).tendsto
    have h2 : Tendsto (fun x : ℝ => Real.sqrt (1 - x)) (𝓝 (-1 : ℝ)) (𝓝 (Real.sqrt 2)) := by
      have hc : Continuous (fun x : ℝ => Real.sqrt (1 - x)) := by fun_prop
      simpa [show (1 : ℝ) - (-1 : ℝ) = 2 by norm_num] using
        (hc.continuousAt (x := (-1 : ℝ))).tendsto
    have h3 : Tendsto Real.arccos (𝓝 (-1 : ℝ)) (𝓝 Real.pi) := by
      simpa [Real.arccos_neg_one] using (Real.continuous_arccos.continuousAt (x := (-1 : ℝ))).tendsto
    have hsq2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    simpa using (h1.div h2 hsq2).mul h3
  exact (hlim_fn.mono_left nhdsWithin_le_nhds).congr'
    (eventually_of_mem hmem fun x hx => (hrewrite x hx).symm)

theorem stationaryKernel_tendsto_two :
    Tendsto stationaryKernel (𝓝[<] (1 : ℝ)) (𝓝 2) := by
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)
  have hlower : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 1 + x ≤ stationaryKernel x := by
    intro x hx
    set θ : ℝ := Real.arccos x
    have hθ0 : 0 < θ := Real.arccos_pos.mpr hx.2
    have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr hx.1
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
    have hlt : Real.sin θ < θ := Real.sin_lt hθ0
    have hcos : Real.cos θ = x := Real.cos_arccos hx.1.le hx.2.le
    rw [stationaryKernel_eq_manuscriptPhi, ← hcos, Sphere3.manuscriptPhi_cos hθ0 hθpi]
    rw [le_div_iff₀ hsin]
    have h1p : 0 < 1 + Real.cos θ := by linarith [hx.1, hcos]
    nlinarith [hlt, h1p]
  have hupper : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, stationaryKernel x ≤ 2 :=
    fun _ hx => (stationaryKernel_lt_two hx).le
  have hlim_low : Tendsto (fun x : ℝ => 1 + x) (𝓝[<] (1 : ℝ)) (𝓝 2) := by
    have hc : Continuous (fun x : ℝ => (1 : ℝ) + x) := by fun_prop
    simpa [one_add_one_eq_two] using (hc.continuousAt (x := (1 : ℝ))).mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_low tendsto_const_nhds
    (eventually_of_mem hmem hlower) (eventually_of_mem hmem hupper)

theorem stationaryKernel_image_Ioo :
    stationaryKernel '' Set.Ioo (-1 : ℝ) 1 = Set.Ioo (0 : ℝ) 2 := by
  apply Set.Subset.antisymm
  · exact stationaryKernel_mapsTo.image_subset
  · intro s hs
    have hev1 : ∀ᶠ x in 𝓝[>] (-1 : ℝ), x ∈ Set.Ioo (-1 : ℝ) 1 ∧ stationaryKernel x < s :=
      Filter.eventually_and.mpr
        ⟨Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1),
          stationaryKernel_tendsto_zero (gt_mem_nhds hs.1)⟩
    have hev2 : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Set.Ioo (-1 : ℝ) 1 ∧ s < stationaryKernel y :=
      Filter.eventually_and.mpr
        ⟨Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1),
          stationaryKernel_tendsto_two (lt_mem_nhds hs.2)⟩
    obtain ⟨a, ha_mem, ha_lt⟩ := hev1.exists
    obtain ⟨b, hb_mem, hb_gt⟩ := hev2.exists
    have hab : a ≤ b := by
      by_contra hlt
      have hba : b < a := lt_of_not_ge hlt
      have hmono := stationaryKernel_strictMonoOn hb_mem ha_mem hba
      linarith
    have hcont : ContinuousOn stationaryKernel (Set.Icc a b) := by
      intro x hx
      have hx_mem : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_of_lt_of_le ha_mem.1 hx.1, lt_of_le_of_lt hx.2 hb_mem.2⟩
      exact (stationaryKernel_hasDerivAt x hx_mem).continuousAt.continuousWithinAt
    obtain ⟨x, hx_icc, hx_eq⟩ :=
      intermediate_value_Icc hab hcont ⟨ha_lt.le, hb_gt.le⟩
    exact ⟨x, ⟨lt_of_lt_of_le ha_mem.1 hx_icc.1, lt_of_le_of_lt hx_icc.2 hb_mem.2⟩, hx_eq⟩

theorem manuscriptKernelInverse_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    manuscriptKernelInverse s ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hs_im : s ∈ stationaryKernel '' Set.Ioo (-1 : ℝ) 1 := by
    rw [stationaryKernel_image_Ioo]; exact hs
  obtain ⟨x, hx, rfl⟩ := hs_im
  rwa [manuscriptKernelInverse_stationaryKernel x hx]

theorem stationaryKernel_manuscriptKernelInverse {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    stationaryKernel (manuscriptKernelInverse s) = s := by
  have hs_im : s ∈ stationaryKernel '' Set.Ioo (-1 : ℝ) 1 := by
    rw [stationaryKernel_image_Ioo]; exact hs
  obtain ⟨x, hx, rfl⟩ := hs_im
  rw [manuscriptKernelInverse_stationaryKernel x hx]

theorem manuscriptKernelInverse_strictMonoOn :
    StrictMonoOn manuscriptKernelInverse (Set.Ioo (0 : ℝ) 2) := by
  simpa only [stationaryKernel_image_Ioo] using manuscriptKernelInverse_strictMonoOn_image

theorem manuscriptKernelInverse_continuousAt {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    ContinuousAt manuscriptKernelInverse s := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set x : ℝ := manuscriptKernelInverse s
  have hx : x ∈ Set.Ioo (-1 : ℝ) 1 := manuscriptKernelInverse_mem_Ioo hs
  have hsx : stationaryKernel x = s := stationaryKernel_manuscriptKernelInverse hs
  set r : ℝ := min (ε / 2) (min ((x + 1) / 2) ((1 - x) / 2))
  have hr : 0 < r := by
    have : 0 < (x + 1) / 2 := by linarith [hx.1]
    have : 0 < (1 - x) / 2 := by linarith [hx.2]
    positivity
  have hx1_mem : x - r ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have : r ≤ (x + 1) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have : r ≤ (1 - x) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
  have hx2_mem : x + r ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have : r ≤ (x + 1) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    · have : r ≤ (1 - x) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
  set s1 : ℝ := stationaryKernel (x - r)
  set s2 : ℝ := stationaryKernel (x + r)
  have hs1_lt : s1 < s := by
    rw [← hsx]
    exact stationaryKernel_strictMonoOn hx1_mem hx (by linarith)
  have hs2_gt : s < s2 := by
    rw [← hsx]
    exact stationaryKernel_strictMonoOn hx hx2_mem (by linarith)
  have hs1_mem : s1 ∈ Set.Ioo (0 : ℝ) 2 := stationaryKernel_mapsTo hx1_mem
  have hs2_mem : s2 ∈ Set.Ioo (0 : ℝ) 2 := stationaryKernel_mapsTo hx2_mem
  refine ⟨min (s - s1) (s2 - s), lt_min (sub_pos.mpr hs1_lt) (sub_pos.mpr hs2_gt), ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy ⊢
  have hy_mem : y ∈ Set.Ioo (0 : ℝ) 2 := by
    have hmin1 : dist y s < s - s1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hmin2 : dist y s < s2 - s := lt_of_lt_of_le hy (min_le_right _ _)
    rw [Real.dist_eq, abs_sub_lt_iff] at hmin1 hmin2
    exact ⟨by linarith [hs1_mem.1], by linarith [hs2_mem.2]⟩
  have hy_gt_s1 : s1 < y := by
    have hmin1 : |y - s| < s - s1 := lt_of_lt_of_le hy (min_le_left _ _)
    rw [abs_sub_lt_iff] at hmin1
    linarith
  have hy_lt_s2 : y < s2 := by
    have hmin2 : |y - s| < s2 - s := lt_of_lt_of_le hy (min_le_right _ _)
    rw [abs_sub_lt_iff] at hmin2
    linarith
  have hinv_gt : x - r < manuscriptKernelInverse y := by
    rw [← manuscriptKernelInverse_stationaryKernel (x - r) hx1_mem]
    exact manuscriptKernelInverse_strictMonoOn hs1_mem hy_mem hy_gt_s1
  have hinv_lt : manuscriptKernelInverse y < x + r := by
    rw [← manuscriptKernelInverse_stationaryKernel (x + r) hx2_mem]
    exact manuscriptKernelInverse_strictMonoOn hy_mem hs2_mem hy_lt_s2
  have hr_eps : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  rw [abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

theorem manuscriptKernelInverse_continuousOn :
    ContinuousOn manuscriptKernelInverse (Set.Ioo (0 : ℝ) 2) :=
  fun _ hs => (manuscriptKernelInverse_continuousAt hs).continuousWithinAt

theorem stationaryKernel_hasDerivAt_firstDerivative {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt stationaryKernel (stationaryKernelFirstDerivative x) x := by
  simpa [stationaryKernelFirstDerivative] using stationaryKernel_hasDerivAt x hx

theorem stationaryKernelFirstDerivative_gt_third {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 : ℝ) / 3 < stationaryKernelFirstDerivative x := by
  set θ : ℝ := Real.arccos x
  have hθ0 : 0 < θ := Real.arccos_pos.mpr hx.2
  have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr hx.1
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hcos : Real.cos θ = x := Real.cos_arccos hx.1.le hx.2.le
  have hsqrt : Real.sqrt (1 - x ^ 2) = Real.sin θ := by
    rw [← Real.sin_arccos]
  let H : ℝ → ℝ := fun t => 3 * t - 4 * Real.sin t + Real.sin t * Real.cos t
  have hH_deriv : ∀ t : ℝ, HasDerivAt H (2 * (1 - Real.cos t) ^ 2) t := by
    intro t
    have h1 := ((hasDerivAt_id t).const_mul (3 : ℝ)).sub ((Real.hasDerivAt_sin t).const_mul (4 : ℝ))
    have h2 := (Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)
    convert h1.add h2 using 1
    · funext u; simp [H]
    · have hsc := Real.sin_sq_add_cos_sq t
      nlinarith [hsc]
  have hH_mono : StrictMonoOn H (Set.Icc (0 : ℝ) Real.pi) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (f' := fun t => 2 * (1 - Real.cos t) ^ 2) (convex_Icc 0 Real.pi)
      (fun t _ => (hH_deriv t).continuousAt.continuousWithinAt) ?_ ?_
    · intro t _
      exact (hH_deriv t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hcost_lt : Real.cos t < 1 := by
        simpa [Real.cos_zero] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
          ⟨ht.1.le, ht.2.le⟩ ht.1
      have : 0 < 1 - Real.cos t := sub_pos.mpr hcost_lt
      positivity
  have hH_pos : 0 < H θ := by
    have hH0 : H 0 = 0 := by simp [H]
    rw [← hH0]
    exact hH_mono ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ0.le, hθpi.le⟩ hθ0
  have hden : 0 < (1 - x) * Real.sin θ := mul_pos (by linarith [hx.2]) hsin
  unfold stationaryKernelFirstDerivative
  rw [hsqrt]
  change 1 / 3 < (θ - Real.sin θ) / ((1 - x) * Real.sin θ)
  rw [div_lt_div_iff₀ (by norm_num) hden]
  dsimp [H] at hH_pos
  nlinarith [hcos, hH_pos]

theorem stationaryKernel_secant_gt_third {x y : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hxy : x < y) :
    (y - x) / 3 < stationaryKernel y - stationaryKernel x := by
  have hcont : ContinuousOn stationaryKernel (Set.Icc x y) := by
    intro t ht
    have ht_mem : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    exact (stationaryKernel_hasDerivAt_firstDerivative ht_mem).continuousAt.continuousWithinAt
  have hdiff : ∀ t ∈ Set.Ioo x y, HasDerivAt stationaryKernel (stationaryKernelFirstDerivative t) t := by
    intro t ht
    exact stationaryKernel_hasDerivAt_firstDerivative ⟨lt_trans hx.1 ht.1, lt_trans ht.2 hy.2⟩
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope stationaryKernel stationaryKernelFirstDerivative hxy hcont hdiff
  have hξ_bound := stationaryKernelFirstDerivative_gt_third ⟨lt_trans hx.1 hξ_mem.1, lt_trans hξ_mem.2 hy.2⟩
  rw [hξ_eq] at hξ_bound
  have hden : 0 < y - x := sub_pos.mpr hxy
  rw [lt_div_iff₀ hden] at hξ_bound
  linarith

theorem manuscriptKernelInverse_hasDerivAt {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt manuscriptKernelInverse
      (stationaryKernelFirstDerivative (manuscriptKernelInverse s))⁻¹ s := by
  have hx_mem : manuscriptKernelInverse s ∈ Set.Ioo (-1 : ℝ) 1 :=
    manuscriptKernelInverse_mem_Ioo hs
  have hf'_pos : 0 < stationaryKernelFirstDerivative (manuscriptKernelInverse s) :=
    lt_trans (by norm_num) (stationaryKernelFirstDerivative_gt_third hx_mem)
  refine HasDerivAt.of_local_left_inverse
    (manuscriptKernelInverse_continuousAt hs)
    (stationaryKernel_hasDerivAt_firstDerivative hx_mem)
    hf'_pos.ne' ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
  exact stationaryKernel_manuscriptKernelInverse hy

theorem deriv_manuscriptKernelInverse {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    deriv manuscriptKernelInverse s =
      (stationaryKernelFirstDerivative (manuscriptKernelInverse s))⁻¹ :=
  (manuscriptKernelInverse_hasDerivAt hs).deriv

theorem manuscriptKernelInverse_deriv_pos {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    0 < deriv manuscriptKernelInverse s := by
  rw [deriv_manuscriptKernelInverse hs]
  exact inv_pos.mpr (lt_trans (by norm_num)
    (stationaryKernelFirstDerivative_gt_third (manuscriptKernelInverse_mem_Ioo hs)))

theorem manuscriptKernelInverse_deriv_strictMonoOn :
    StrictMonoOn (deriv manuscriptKernelInverse) (Set.Ioo (0 : ℝ) 2) := by
  intro s1 hs1 s2 hs2 hs12
  rw [deriv_manuscriptKernelInverse hs1, deriv_manuscriptKernelInverse hs2]
  have hx1_lt_hx2 : manuscriptKernelInverse s1 < manuscriptKernelInverse s2 :=
    manuscriptKernelInverse_strictMonoOn hs1 hs2 hs12
  have hf'_anti := stationaryKernel_firstDerivative_strictAnti
    (manuscriptKernelInverse_mem_Ioo hs1) (manuscriptKernelInverse_mem_Ioo hs2) hx1_lt_hx2
  have hf'_pos : 0 < stationaryKernelFirstDerivative (manuscriptKernelInverse s2) :=
    lt_trans (by norm_num)
      (stationaryKernelFirstDerivative_gt_third (manuscriptKernelInverse_mem_Ioo hs2))
  exact inv_strictAnti₀ hf'_pos hf'_anti

/-- The side length `ℓ(s) = arccos(g(s)) ∈ (0, π)` associated to inverse kernel value `s ∈ (0, 2)`. -/
def manuscriptKernelLength (s : ℝ) : ℝ :=
  Real.arccos (manuscriptKernelInverse s)

theorem manuscriptKernelLength_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    manuscriptKernelLength s ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hx := manuscriptKernelInverse_mem_Ioo hs
  exact ⟨Real.arccos_pos.mpr hx.2, Real.arccos_lt_pi.mpr hx.1⟩

theorem cos_manuscriptKernelLength {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    Real.cos (manuscriptKernelLength s) = manuscriptKernelInverse s := by
  have hx := manuscriptKernelInverse_mem_Ioo hs
  exact Real.cos_arccos hx.1.le hx.2.le

theorem manuscriptKernelLength_strictAntiOn :
    StrictAntiOn manuscriptKernelLength (Set.Ioo (0 : ℝ) 2) := by
  intro s1 hs1 s2 hs2 hs12
  unfold manuscriptKernelLength
  have hx1 := manuscriptKernelInverse_mem_Ioo hs1
  have hx2 := manuscriptKernelInverse_mem_Ioo hs2
  exact Real.strictAntiOn_arccos ⟨hx1.1.le, hx1.2.le⟩ ⟨hx2.1.le, hx2.2.le⟩
    (manuscriptKernelInverse_strictMonoOn hs1 hs2 hs12)

def lengthDenomRatio (ℓ : ℝ) : ℝ :=
  (ℓ - Real.sin ℓ) / (1 - Real.cos ℓ)

theorem lengthDenomRatio_pos {ℓ : ℝ} (hℓ : ℓ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    0 < lengthDenomRatio ℓ := by
  have h1 : 0 < ℓ - Real.sin ℓ := sub_pos.mpr (Real.sin_lt hℓ.1)
  have h2 : 0 < 1 - Real.cos ℓ := by
    have : Real.cos ℓ < 1 := by
      simpa [Real.cos_zero] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
        ⟨hℓ.1.le, hℓ.2.le⟩ hℓ.1
    linarith
  exact div_pos h1 h2

theorem lengthDenomRatio_strictMonoOn :
    StrictMonoOn lengthDenomRatio (Set.Ioo (0 : ℝ) Real.pi) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo 0 Real.pi)
    (f' := fun ℓ => ((1 - Real.cos ℓ) ^ 2 - (ℓ - Real.sin ℓ) * Real.sin ℓ) / (1 - Real.cos ℓ) ^ 2)
    ?_ ?_ ?_
  · intro ℓ hℓ
    have h1cos : 1 - Real.cos ℓ ≠ 0 := by
      have : Real.cos ℓ < 1 := by
        simpa [Real.cos_zero] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
          ⟨hℓ.1.le, hℓ.2.le⟩ hℓ.1
      linarith
    have hcont : ContinuousAt lengthDenomRatio ℓ := by
      unfold lengthDenomRatio
      fun_prop (disch := exact h1cos)
    exact hcont.continuousWithinAt
  · intro ℓ hℓ
    rw [interior_Ioo] at hℓ
    have h1cos : 1 - Real.cos ℓ ≠ 0 := by
      have : Real.cos ℓ < 1 := by
        simpa [Real.cos_zero] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
          ⟨hℓ.1.le, hℓ.2.le⟩ hℓ.1
      linarith
    have hnum := (hasDerivAt_id ℓ).sub (Real.hasDerivAt_sin ℓ)
    have hden := (Real.hasDerivAt_cos ℓ).const_sub (1 : ℝ)
    have hquot := hnum.div hden h1cos
    have hq : HasDerivAt lengthDenomRatio
        (((1 - Real.cos ℓ) ^ 2 - (ℓ - Real.sin ℓ) * Real.sin ℓ) / (1 - Real.cos ℓ) ^ 2) ℓ := by
      refine (hquot.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards with u
        simp [lengthDenomRatio]
      · simp only [Pi.sub_apply, id_eq]
        ring
    exact hq.hasDerivWithinAt
  · intro ℓ hℓ
    rw [interior_Ioo] at hℓ
    have h1cos : 0 < 1 - Real.cos ℓ := by
      have : Real.cos ℓ < 1 := by
        simpa [Real.cos_zero] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
          ⟨hℓ.1.le, hℓ.2.le⟩ hℓ.1
      linarith
    have hsin : 0 < Real.sin ℓ := Real.sin_pos_of_pos_of_lt_pi hℓ.1 hℓ.2
    have h1pcos : 0 < 1 + Real.cos ℓ := by
      have : -1 < Real.cos ℓ := by
        simpa [Real.cos_pi] using Real.strictAntiOn_cos ⟨hℓ.1.le, hℓ.2.le⟩
          ⟨Real.pi_pos.le, le_rfl⟩ hℓ.2
      linarith
    have htrig := Sphere3.angle_mul_one_add_cos_lt_two_sin ℓ hℓ.1 hℓ.2
    have hnum_pos : 0 < (1 - Real.cos ℓ) ^ 2 - (ℓ - Real.sin ℓ) * Real.sin ℓ := by
      have hsc : Real.sin ℓ ^ 2 + Real.cos ℓ ^ 2 = 1 := Real.sin_sq_add_cos_sq ℓ
      have hprod : (1 + Real.cos ℓ) * ((1 - Real.cos ℓ) ^ 2 - (ℓ - Real.sin ℓ) * Real.sin ℓ) =
          Real.sin ℓ * (2 * Real.sin ℓ - ℓ * (1 + Real.cos ℓ)) := by
        nlinarith [hsc]
      have hrhs : 0 < Real.sin ℓ * (2 * Real.sin ℓ - ℓ * (1 + Real.cos ℓ)) :=
        mul_pos hsin (by linarith)
      have hlhs : 0 < (1 + Real.cos ℓ) * ((1 - Real.cos ℓ) ^ 2 - (ℓ - Real.sin ℓ) * Real.sin ℓ) := by
        rw [hprod]; exact hrhs
      by_contra hle
      have hn := mul_nonpos_of_nonneg_of_nonpos h1pcos.le (le_of_not_gt hle)
      linarith
    have hden_pos : 0 < (1 - Real.cos ℓ) ^ 2 := sq_pos_of_pos h1cos
    exact div_pos hnum_pos hden_pos

theorem manuscriptKernelLength_hasDerivAt {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) :
    HasDerivAt manuscriptKernelLength (-(lengthDenomRatio (manuscriptKernelLength s))⁻¹) s := by
  set x : ℝ := manuscriptKernelInverse s
  set ℓ : ℝ := manuscriptKernelLength s
  have hx_mem : x ∈ Set.Ioo (-1 : ℝ) 1 := manuscriptKernelInverse_mem_Ioo hs
  have hℓ_mem : ℓ ∈ Set.Ioo (0 : ℝ) Real.pi := manuscriptKernelLength_mem_Ioo hs
  have hsin : 0 < Real.sin ℓ := Real.sin_pos_of_pos_of_lt_pi hℓ_mem.1 hℓ_mem.2
  have hcos : Real.cos ℓ = x := cos_manuscriptKernelLength hs
  have hsqrt : Real.sqrt (1 - x ^ 2) = Real.sin ℓ := by
    rw [← Real.sin_arccos]; rfl
  have harc : HasDerivAt Real.arccos (-(Real.sqrt (1 - x ^ 2))⁻¹) x := by
    simpa only [one_div] using Real.hasDerivAt_arccos hx_mem.1.ne' hx_mem.2.ne
  have hinv := manuscriptKernelInverse_hasDerivAt hs
  have hcomp := harc.comp s hinv
  have hratio : stationaryKernelFirstDerivative x = lengthDenomRatio ℓ / Real.sin ℓ := by
    have hℓ_arc : Real.arccos x = ℓ := rfl
    unfold stationaryKernelFirstDerivative lengthDenomRatio
    rw [hℓ_arc, hsqrt, ← hcos, div_div]
  have heq_deriv : -(Real.sqrt (1 - x ^ 2))⁻¹ * (stationaryKernelFirstDerivative x)⁻¹ =
      -(lengthDenomRatio ℓ)⁻¹ := by
    rw [hratio, hsqrt]
    have hden : lengthDenomRatio ℓ ≠ 0 := (lengthDenomRatio_pos hℓ_mem).ne'
    field_simp [hsin.ne', hden]
  exact (hcomp.congr_deriv heq_deriv)

theorem manuscriptKernelLength_deriv_strictAntiOn :
    StrictAntiOn (fun s => -(lengthDenomRatio (manuscriptKernelLength s))⁻¹) (Set.Ioo (0 : ℝ) 2) := by
  intro s1 hs1 s2 hs2 hs12
  have hℓ21 : manuscriptKernelLength s2 < manuscriptKernelLength s1 :=
    manuscriptKernelLength_strictAntiOn hs1 hs2 hs12
  have hℓ1_mem := manuscriptKernelLength_mem_Ioo hs1
  have hℓ2_mem := manuscriptKernelLength_mem_Ioo hs2
  have hr21 : lengthDenomRatio (manuscriptKernelLength s2) <
      lengthDenomRatio (manuscriptKernelLength s1) :=
    lengthDenomRatio_strictMonoOn hℓ2_mem hℓ1_mem hℓ21
  have hpos2 : 0 < lengthDenomRatio (manuscriptKernelLength s2) :=
    lengthDenomRatio_pos hℓ2_mem
  have hinv : (lengthDenomRatio (manuscriptKernelLength s1))⁻¹ <
      (lengthDenomRatio (manuscriptKernelLength s2))⁻¹ :=
    inv_strictAnti₀ hpos2 hr21
  linarith

theorem manuscriptKernelLength_diff_monotoneOn {y z : ℝ} (hzy : z ≤ y) :
    MonotoneOn (fun x : ℝ => manuscriptKernelLength (x + z) - manuscriptKernelLength (x + y))
      {x : ℝ | x + z ∈ Set.Ioo (0 : ℝ) 2 ∧ x + y ∈ Set.Ioo (0 : ℝ) 2} := by
  have hD_eq : {x : ℝ | x + z ∈ Set.Ioo (0 : ℝ) 2 ∧ x + y ∈ Set.Ioo (0 : ℝ) 2} = Set.Ioo (-z) (2 - y) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hz1, _⟩, ⟨_, hy2⟩⟩
      exact ⟨by linarith, by linarith⟩
    · intro hx
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [hD_eq]
  have hder : ∀ x ∈ Set.Ioo (-z) (2 - y),
      HasDerivAt (fun t : ℝ => manuscriptKernelLength (t + z) - manuscriptKernelLength (t + y))
        (-(lengthDenomRatio (manuscriptKernelLength (x + z)))⁻¹ -
         -(lengthDenomRatio (manuscriptKernelLength (x + y)))⁻¹) x := by
    intro x hx
    have hxz : x + z ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxy : x + y ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hz_comp := (manuscriptKernelLength_hasDerivAt hxz).comp x ((hasDerivAt_id x).add_const z)
    have hy_comp := (manuscriptKernelLength_hasDerivAt hxy).comp x ((hasDerivAt_id x).add_const y)
    have hsub := hz_comp.sub hy_comp
    refine (hsub.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
    · simp only [Pi.sub_apply, Function.comp_apply, id_eq]
    · simp only [mul_one]
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo (-z) (2 - y))
    (f' := fun x => -(lengthDenomRatio (manuscriptKernelLength (x + z)))⁻¹ -
      -(lengthDenomRatio (manuscriptKernelLength (x + y)))⁻¹)
    ?_ ?_ ?_
  · intro x hx
    exact (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact (hder x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    have hxz : x + z ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxy : x + y ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hanti := manuscriptKernelLength_deriv_strictAntiOn.antitoneOn hxz hxy (by linarith : x + z ≤ x + y)
    linarith

end SphericalTetrahedron
