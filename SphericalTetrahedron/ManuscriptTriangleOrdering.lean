module

public import Sphere3.ManuscriptTriangleAlgebra
public import Sphere3.ManuscriptPsiIntegral
public import Sphere3.ManuscriptTriangleDerivativeSigns
public import SphericalTetrahedron.ManuscriptRigidityBridge
public import SphericalTetrahedron.ManuscriptKernelGlobal

@[expose] public section

/-!
# Ordering, domain convexity, and directional monotonicity on `triangleDomain`

This module formalizes Step 2 of the global stationary rigidity proof:
for `g := manuscriptKernelInverse` on `(0, 2)`:
- `triangleDomain` is open, `swap12`/`swap23`-symmetric, and convex along first-coordinate slices.
- On `triangleDomain`, coordinates order the inverse Gram coefficients `z₁, z₂, z₃`
  and satisfy `1 / 3 ≤ zᵢ` (so `0 < zᵢ`).
- Along coordinate 1, `x ↦ manuscriptFaceEnergy g x b c` has derivative
  `2 * z₁ * (1 - g' (x + b) * z₂ - g' (x + c) * z₃)`.
- This yields the three strict comparison inequalities needed by
  `manuscript_ordered_four_face_rigidity`: `manuscriptFaceEnergy_strict_first`,
  `manuscriptFaceEnergy_strict_second`, and `manuscriptFaceEnergy_iso_lt`.
-/

noncomputable section

namespace SphericalTetrahedron

open Filter Set
open scoped Topology

/-- The open domain of parameter triples `(a, b, c)` whose pairwise sums lie in `(0, 2)`
and whose `g`-Gram determinant is strictly positive. -/
def triangleDomain : Set (ℝ × ℝ × ℝ) :=
  {p | p.2.1 + p.2.2 ∈ Set.Ioo (0 : ℝ) 2 ∧
       p.1 + p.2.2 ∈ Set.Ioo (0 : ℝ) 2 ∧
       p.1 + p.2.1 ∈ Set.Ioo (0 : ℝ) 2 ∧
       0 < Sphere3.triangleGramDet
         (manuscriptKernelInverse (p.2.1 + p.2.2))
         (manuscriptKernelInverse (p.1 + p.2.2))
         (manuscriptKernelInverse (p.1 + p.2.1))}

theorem triangleDomain_mem_Ioo {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    b + c ∈ Set.Ioo (0 : ℝ) 2 ∧
    a + c ∈ Set.Ioo (0 : ℝ) 2 ∧
    a + b ∈ Set.Ioo (0 : ℝ) 2 :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem triangleDomain_det_pos {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    0 < Sphere3.triangleGramDet
      (manuscriptKernelInverse (b + c))
      (manuscriptKernelInverse (a + c))
      (manuscriptKernelInverse (a + b)) :=
  h.2.2.2

theorem isOpen_triangleDomain : IsOpen triangleDomain := by
  rw [Metric.isOpen_iff]
  intro p hp
  rcases hp with ⟨hbc, hac, hab, hdet⟩
  have hg_bc : ContinuousAt (fun q : ℝ × ℝ × ℝ => manuscriptKernelInverse (q.2.1 + q.2.2)) p :=
    (manuscriptKernelInverse_continuousAt hbc).comp_of_eq (by fun_prop) rfl
  have hg_ac : ContinuousAt (fun q : ℝ × ℝ × ℝ => manuscriptKernelInverse (q.1 + q.2.2)) p :=
    (manuscriptKernelInverse_continuousAt hac).comp_of_eq (by fun_prop) rfl
  have hg_ab : ContinuousAt (fun q : ℝ × ℝ × ℝ => manuscriptKernelInverse (q.1 + q.2.1)) p :=
    (manuscriptKernelInverse_continuousAt hab).comp_of_eq (by fun_prop) rfl
  have hdet_cont : ContinuousAt
      (fun q : ℝ × ℝ × ℝ =>
        Sphere3.triangleGramDet
          (manuscriptKernelInverse (q.2.1 + q.2.2))
          (manuscriptKernelInverse (q.1 + q.2.2))
          (manuscriptKernelInverse (q.1 + q.2.1))) p := by
    unfold Sphere3.triangleGramDet
    fun_prop
  have h1 : ∀ᶠ q in 𝓝 p, q.2.1 + q.2.2 ∈ Set.Ioo (0 : ℝ) 2 :=
    ((continuous_snd.fst.add continuous_snd.snd).continuousAt.eventually
      (isOpen_Ioo.mem_nhds hbc))
  have h2 : ∀ᶠ q in 𝓝 p, q.1 + q.2.2 ∈ Set.Ioo (0 : ℝ) 2 :=
    ((continuous_fst.add continuous_snd.snd).continuousAt.eventually
      (isOpen_Ioo.mem_nhds hac))
  have h3 : ∀ᶠ q in 𝓝 p, q.1 + q.2.1 ∈ Set.Ioo (0 : ℝ) 2 :=
    ((continuous_fst.add continuous_snd.fst).continuousAt.eventually
      (isOpen_Ioo.mem_nhds hab))
  have h4 : ∀ᶠ q in 𝓝 p,
      0 < Sphere3.triangleGramDet
        (manuscriptKernelInverse (q.2.1 + q.2.2))
        (manuscriptKernelInverse (q.1 + q.2.2))
        (manuscriptKernelInverse (q.1 + q.2.1)) :=
    hdet_cont.eventually (isOpen_Ioi.mem_nhds hdet)
  have hmem : triangleDomain ∈ 𝓝 p := by
    filter_upwards [h1, h2, h3, h4] with q hq1 hq2 hq3 hq4
    exact ⟨hq1, hq2, hq3, hq4⟩
  exact Metric.mem_nhds_iff.mp hmem

theorem triangleDomain_swap12 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    (b, a, c) ∈ triangleDomain := by
  rcases h with ⟨hbc, hac, hab, hdet⟩
  refine ⟨hac, hbc, by simpa [add_comm] using hab, ?_⟩
  have hdet_eq :
      Sphere3.triangleGramDet
        (manuscriptKernelInverse (a + c))
        (manuscriptKernelInverse (b + c))
        (manuscriptKernelInverse (b + a)) =
      Sphere3.triangleGramDet
        (manuscriptKernelInverse (b + c))
        (manuscriptKernelInverse (a + c))
        (manuscriptKernelInverse (a + b)) := by
    rw [add_comm b a]
    unfold Sphere3.triangleGramDet
    ring
  rwa [hdet_eq]

theorem triangleDomain_swap23 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    (a, c, b) ∈ triangleDomain := by
  rcases h with ⟨hbc, hac, hab, hdet⟩
  refine ⟨by simpa [add_comm] using hbc, hab, hac, ?_⟩
  have hdet_eq :
      Sphere3.triangleGramDet
        (manuscriptKernelInverse (c + b))
        (manuscriptKernelInverse (a + b))
        (manuscriptKernelInverse (a + c)) =
      Sphere3.triangleGramDet
        (manuscriptKernelInverse (b + c))
        (manuscriptKernelInverse (a + c))
        (manuscriptKernelInverse (a + b)) := by
    rw [add_comm c b]
    unfold Sphere3.triangleGramDet
    ring
  rwa [hdet_eq]

theorem triangleDomain_cos_pos_iff {a b c : ℝ}
    (hbc : b + c ∈ Set.Ioo (0 : ℝ) 2)
    (hac : a + c ∈ Set.Ioo (0 : ℝ) 2)
    (hab : a + b ∈ Set.Ioo (0 : ℝ) 2) :
    (a, b, c) ∈ triangleDomain ↔
      manuscriptKernelLength (b + c) < manuscriptKernelLength (a + c) + manuscriptKernelLength (a + b) ∧
      manuscriptKernelLength (a + c) < manuscriptKernelLength (b + c) + manuscriptKernelLength (a + b) ∧
      manuscriptKernelLength (a + b) < manuscriptKernelLength (b + c) + manuscriptKernelLength (a + c) ∧
      manuscriptKernelLength (b + c) + manuscriptKernelLength (a + c) + manuscriptKernelLength (a + b) <
        2 * Real.pi := by
  set ℓ₁ : ℝ := manuscriptKernelLength (b + c)
  set ℓ₂ : ℝ := manuscriptKernelLength (a + c)
  set ℓ₃ : ℝ := manuscriptKernelLength (a + b)
  have h1 := manuscriptKernelLength_mem_Ioo hbc
  have h2 := manuscriptKernelLength_mem_Ioo hac
  have h3 := manuscriptKernelLength_mem_Ioo hab
  have hc1 := cos_manuscriptKernelLength hbc
  have hc2 := cos_manuscriptKernelLength hac
  have hc3 := cos_manuscriptKernelLength hab
  have hiff := Sphere3.triangleGramDet_cos_pos_iff h1.1 h1.2 h2.1 h2.2 h3.1 h3.2
  rw [hc1, hc2, hc3] at hiff
  constructor
  · intro hmem
    exact hiff.mp hmem.2.2.2
  · intro htri
    exact ⟨hbc, hac, hab, hiff.mpr htri⟩

private theorem triangleDomain_segment_first_ordered {x₁ x₂ x b c : ℝ}
    (hcb : c ≤ b) (hx₁ : (x₁, b, c) ∈ triangleDomain) (hx₂ : (x₂, b, c) ∈ triangleDomain)
    (hx_lo : x₁ ≤ x) (hx_hi : x ≤ x₂) :
    (x, b, c) ∈ triangleDomain := by
  rcases hx₁ with ⟨hbc, hx₁c, hx₁b, hx₁_det⟩
  rcases hx₂ with ⟨_, hx₂c, hx₂b, hx₂_det⟩
  have hxc : x + c ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hx₁c.1], by linarith [hx₂c.2]⟩
  have hxb : x + b ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [hx₁b.1], by linarith [hx₂b.2]⟩
  have htri₁ := (triangleDomain_cos_pos_iff hbc hx₁c hx₁b).mp ⟨hbc, hx₁c, hx₁b, hx₁_det⟩
  have htri₂ := (triangleDomain_cos_pos_iff hbc hx₂c hx₂b).mp ⟨hbc, hx₂c, hx₂b, hx₂_det⟩
  have h1_pos : 0 < manuscriptKernelLength (b + c) := (manuscriptKernelLength_mem_Ioo hbc).1
  have hL_x₁c : manuscriptKernelLength (x + c) ≤ manuscriptKernelLength (x₁ + c) :=
    manuscriptKernelLength_strictAntiOn.antitoneOn hx₁c hxc (by linarith)
  have hL_x₁b : manuscriptKernelLength (x + b) ≤ manuscriptKernelLength (x₁ + b) :=
    manuscriptKernelLength_strictAntiOn.antitoneOn hx₁b hxb (by linarith)
  have hL_x₂c : manuscriptKernelLength (x₂ + c) ≤ manuscriptKernelLength (x + c) :=
    manuscriptKernelLength_strictAntiOn.antitoneOn hxc hx₂c (by linarith)
  have hL_x₂b : manuscriptKernelLength (x₂ + b) ≤ manuscriptKernelLength (x + b) :=
    manuscriptKernelLength_strictAntiOn.antitoneOn hxb hx₂b (by linarith)
  have hL_cb : manuscriptKernelLength (x + b) ≤ manuscriptKernelLength (x + c) :=
    manuscriptKernelLength_strictAntiOn.antitoneOn hxc hxb (by linarith)
  have hdiff_mono := manuscriptKernelLength_diff_monotoneOn hcb
    ⟨hxc, hxb⟩ ⟨hx₂c, hx₂b⟩ hx_hi
  refine (triangleDomain_cos_pos_iff hbc hxc hxb).mpr ⟨?_, ?_, ?_, ?_⟩
  · linarith [htri₂.1]
  · linarith [htri₂.2.1]
  · linarith [h1_pos, hL_cb]
  · linarith [htri₁.2.2.2]

theorem triangleDomain_segment_first {x₁ x₂ x b c : ℝ}
    (hx₁ : (x₁, b, c) ∈ triangleDomain) (hx₂ : (x₂, b, c) ∈ triangleDomain)
    (hx_lo : x₁ ≤ x) (hx_hi : x ≤ x₂) :
    (x, b, c) ∈ triangleDomain := by
  rcases le_total c b with hcb | hbc
  · exact triangleDomain_segment_first_ordered hcb hx₁ hx₂ hx_lo hx_hi
  · exact triangleDomain_swap23
      (triangleDomain_segment_first_ordered hbc
        (triangleDomain_swap23 hx₁) (triangleDomain_swap23 hx₂) hx_lo hx_hi)

/-- Helper abbreviation for the three inverse-Gram coefficients at `(a, b, c)` under `g`. -/
def triZ₁ (a b c : ℝ) : ℝ :=
  Sphere3.triangleGramInverse₁
    (manuscriptKernelInverse (b + c))
    (manuscriptKernelInverse (a + c))
    (manuscriptKernelInverse (a + b)) a b c

/-- Second inverse-Gram coefficient at `(a, b, c)` under `g`. -/
def triZ₂ (a b c : ℝ) : ℝ :=
  Sphere3.triangleGramInverse₂
    (manuscriptKernelInverse (b + c))
    (manuscriptKernelInverse (a + c))
    (manuscriptKernelInverse (a + b)) a b c

/-- Third inverse-Gram coefficient at `(a, b, c)` under `g`. -/
def triZ₃ (a b c : ℝ) : ℝ :=
  Sphere3.triangleGramInverse₃
    (manuscriptKernelInverse (b + c))
    (manuscriptKernelInverse (a + c))
    (manuscriptKernelInverse (a + b)) a b c

theorem triZ₁_swap12 (a b c : ℝ) : triZ₁ b a c = triZ₂ a b c := by
  unfold triZ₁ triZ₂ Sphere3.triangleGramInverse₁ Sphere3.triangleGramInverse₂ Sphere3.triangleGramDet
  rw [add_comm b a]
  ring

theorem triZ₂_swap12 (a b c : ℝ) : triZ₂ b a c = triZ₁ a b c := by
  unfold triZ₁ triZ₂ Sphere3.triangleGramInverse₁ Sphere3.triangleGramInverse₂ Sphere3.triangleGramDet
  rw [add_comm b a]
  ring

theorem triZ₃_swap12 (a b c : ℝ) : triZ₃ b a c = triZ₃ a b c := by
  unfold triZ₃ Sphere3.triangleGramInverse₃ Sphere3.triangleGramDet
  rw [add_comm b a]
  ring

theorem triZ₂_swap23 (a b c : ℝ) : triZ₂ a c b = triZ₃ a b c := by
  unfold triZ₂ triZ₃ Sphere3.triangleGramInverse₂ Sphere3.triangleGramInverse₃ Sphere3.triangleGramDet
  rw [add_comm c b]
  ring

theorem triZ₃_swap23 (a b c : ℝ) : triZ₃ a c b = triZ₂ a b c := by
  unfold triZ₂ triZ₃ Sphere3.triangleGramInverse₂ Sphere3.triangleGramInverse₃ Sphere3.triangleGramDet
  rw [add_comm c b]
  ring

theorem triZ₁_swap23 (a b c : ℝ) : triZ₁ a c b = triZ₁ a b c := by
  unfold triZ₁ Sphere3.triangleGramInverse₁ Sphere3.triangleGramDet
  rw [add_comm c b]
  ring

theorem triZ₁_continuousAt_second {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    ContinuousAt (fun s : ℝ => triZ₁ a s c) b := by
  rcases h with ⟨hbc, hac, hab, hdet⟩
  have hg_bc : ContinuousAt (fun s : ℝ => manuscriptKernelInverse (s + c)) b :=
    (manuscriptKernelInverse_continuousAt hbc).comp_of_eq (by fun_prop) rfl
  have hg_ab : ContinuousAt (fun s : ℝ => manuscriptKernelInverse (a + s)) b :=
    (manuscriptKernelInverse_continuousAt hab).comp_of_eq (by fun_prop) rfl
  have hdet_ne :
      Sphere3.triangleGramDet
        (manuscriptKernelInverse (b + c))
        (manuscriptKernelInverse (a + c))
        (manuscriptKernelInverse (a + b)) ≠ 0 := hdet.ne'
  unfold triZ₁ Sphere3.triangleGramInverse₁ Sphere3.triangleGramDet
  fun_prop (disch := exact hdet_ne)

theorem triZ_lt_12 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) (hba : b < a) :
    triZ₁ a b c < triZ₂ a b c := by
  rcases h with ⟨hbc, hac, hab, hdet⟩
  set ℓ₁ : ℝ := manuscriptKernelLength (b + c)
  set ℓ₂ : ℝ := manuscriptKernelLength (a + c)
  set ℓ₃ : ℝ := manuscriptKernelLength (a + b)
  have h1 := manuscriptKernelLength_mem_Ioo hbc
  have h2 := manuscriptKernelLength_mem_Ioo hac
  have h3 := manuscriptKernelLength_mem_Ioo hab
  have hc1 := cos_manuscriptKernelLength hbc
  have hc2 := cos_manuscriptKernelLength hac
  have hc3 := cos_manuscriptKernelLength hab
  have htri := (triangleDomain_cos_pos_iff hbc hac hab).mp ⟨hbc, hac, hab, hdet⟩
  have h2lt1 : ℓ₂ < ℓ₁ := manuscriptKernelLength_strictAntiOn hbc hac (by linarith)
  have hdet_cos : 0 < Sphere3.triangleGramDet (Real.cos ℓ₁) (Real.cos ℓ₂) (Real.cos ℓ₃) := by
    rw [hc1, hc2, hc3]; exact hdet
  have hlt := Sphere3.triangle_gram_inverse_lt h1.1 h1.2 h2.1 h2.2 h3.1 h3.2
    h2lt1 htri.2.2.2 (by linarith [htri.1]) htri.2.2.1 hdet_cos
  have hphi₁ : Sphere3.manuscriptPhi (manuscriptKernelInverse (b + c)) = b + c := by
    rw [← stationaryKernel_eq_manuscriptPhi]; exact stationaryKernel_manuscriptKernelInverse hbc
  have hphi₂ : Sphere3.manuscriptPhi (manuscriptKernelInverse (a + c)) = a + c := by
    rw [← stationaryKernel_eq_manuscriptPhi]; exact stationaryKernel_manuscriptKernelInverse hac
  have hphi₃ : Sphere3.manuscriptPhi (manuscriptKernelInverse (a + b)) = a + b := by
    rw [← stationaryKernel_eq_manuscriptPhi]; exact stationaryKernel_manuscriptKernelInverse hab
  dsimp only at hlt
  rw [hc1, hc2, hc3, hphi₁, hphi₂, hphi₃] at hlt
  have ha_eq : ((a + c) + (a + b) - (b + c)) / 2 = a := by ring
  have hb_eq : ((b + c) + (a + b) - (a + c)) / 2 = b := by ring
  have hc_eq : ((b + c) + (a + c) - (a + b)) / 2 = c := by ring
  rw [ha_eq, hb_eq, hc_eq] at hlt
  exact hlt

theorem triZ_le_12 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) (hba : b ≤ a) :
    triZ₁ a b c ≤ triZ₂ a b c := by
  rcases lt_or_eq_of_le hba with hlt | rfl
  · exact (triZ_lt_12 h hlt).le
  · exact le_of_eq (triZ₁_swap12 b b c)

theorem triZ_lt_23 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) (hcb : c < b) :
    triZ₂ a b c < triZ₃ a b c := by
  have h12 := triZ_lt_12 (triangleDomain_swap23 (triangleDomain_swap12 h)) hcb
  rwa [triZ₁_swap23 b a c, triZ₁_swap12 a b c, triZ₂_swap23 b a c, triZ₃_swap12 a b c] at h12

theorem triZ_le_23 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) (hcb : c ≤ b) :
    triZ₂ a b c ≤ triZ₃ a b c := by
  rcases lt_or_eq_of_le hcb with hlt | rfl
  · exact (triZ_lt_23 h hlt).le
  · exact le_of_eq (triZ₂_swap23 a c c)

theorem triZ_lt_13 {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) (hca : c < a) :
    triZ₁ a b c < triZ₃ a b c := by
  have h12 := triZ_lt_12 (triangleDomain_swap23 h) hca
  rwa [triZ₁_swap23 a b c, triZ₂_swap23 a b c] at h12

private theorem triZ_row₁ {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    triZ₁ a b c + manuscriptKernelInverse (a + b) * triZ₂ a b c +
      manuscriptKernelInverse (a + c) * triZ₃ a b c = a :=
  Sphere3.triangleGramInverse_row₁ _ _ _ a b c h.2.2.2.ne'

private theorem triZ_row₂ {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    manuscriptKernelInverse (a + b) * triZ₁ a b c + triZ₂ a b c +
      manuscriptKernelInverse (b + c) * triZ₃ a b c = b :=
  Sphere3.triangleGramInverse_row₂ _ _ _ a b c h.2.2.2.ne'

private theorem triZ_row₃ {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    manuscriptKernelInverse (a + c) * triZ₁ a b c +
      manuscriptKernelInverse (b + c) * triZ₂ a b c + triZ₃ a b c = c :=
  Sphere3.triangleGramInverse_row₃ _ _ _ a b c h.2.2.2.ne'

private theorem triZ₁_gt_third_of_lt {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) (hcb : c < b) :
    (1 : ℝ) / 3 < triZ₁ a b c := by
  rcases h with ⟨hbc, hac, hab, hdet⟩
  have hmem : (a, b, c) ∈ triangleDomain := ⟨hbc, hac, hab, hdet⟩
  have hk23 : manuscriptKernelInverse (b + c) < 1 := (manuscriptKernelInverse_mem_Ioo hbc).2
  have hkdiff : manuscriptKernelInverse (a + c) < manuscriptKernelInverse (a + b) :=
    manuscriptKernelInverse_strictMonoOn hac hab (by linarith)
  have hz23 : triZ₂ a b c ≤ triZ₃ a b c := triZ_le_23 hmem hcb.le
  have hrow₂ := triZ_row₂ hmem
  have hrow₃ := triZ_row₃ hmem
  have hrow :
      b - c =
        (1 - manuscriptKernelInverse (b + c)) * (triZ₂ a b c - triZ₃ a b c) +
          (manuscriptKernelInverse (a + b) - manuscriptKernelInverse (a + c)) * triZ₁ a b c := by
    linarith [hrow₂, hrow₃]
  have hsec0 := stationaryKernel_secant_gt_third
    (manuscriptKernelInverse_mem_Ioo hac) (manuscriptKernelInverse_mem_Ioo hab) hkdiff
  rw [stationaryKernel_manuscriptKernelInverse hac,
      stationaryKernel_manuscriptKernelInverse hab] at hsec0
  have hsec :
      (manuscriptKernelInverse (a + b) - manuscriptKernelInverse (a + c)) / 3 < b - c := by
    linarith
  exact Sphere3.triangle_smallest_inverse_coefficient_gt_third
    (manuscriptKernelInverse (b + c)) (manuscriptKernelInverse (a + b))
    (manuscriptKernelInverse (a + c)) b c (triZ₁ a b c) (triZ₂ a b c) (triZ₃ a b c)
    hk23 hkdiff hz23 hrow hsec

theorem triZ₁_ge_third {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) :
    (1 : ℝ) / 3 ≤ triZ₁ a b c := by
  rcases lt_trichotomy c b with hcb | hcb | hbc
  · exact (triZ₁_gt_third_of_lt h hcb).le
  · subst hcb
    have hlim_p : Tendsto (fun ε : ℝ => (a, c + ε, c)) (𝓝[>] (0 : ℝ)) (𝓝 (a, c, c)) := by
      have hc : Continuous (fun ε : ℝ => (a, c + ε, c)) := by fun_prop
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hev_dom : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (a, c + ε, c) ∈ triangleDomain :=
      hlim_p (isOpen_triangleDomain.mem_nhds h)
    have hev_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := self_mem_nhdsWithin
    have hev_ge : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 : ℝ) / 3 ≤ triZ₁ a (c + ε) c := by
      filter_upwards [hev_dom, hev_pos] with ε hdom hε
      exact (triZ₁_gt_third_of_lt hdom (by linarith)).le
    have htend :
        Tendsto (fun ε : ℝ => triZ₁ a (c + ε) c) (𝓝[>] (0 : ℝ)) (𝓝 (triZ₁ a c c)) := by
      have hc : ContinuousAt (fun ε : ℝ => triZ₁ a (c + ε) c) 0 :=
        (triZ₁_continuousAt_second h).comp_of_eq (by fun_prop) (by simp)
      simpa only [add_zero] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    exact ge_of_tendsto htend hev_ge
  · rw [← triZ₁_swap23 a b c]
    exact (triZ₁_gt_third_of_lt (triangleDomain_swap23 h) hbc).le

theorem triZ₁_pos {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) : 0 < triZ₁ a b c :=
  lt_of_lt_of_le (by norm_num) (triZ₁_ge_third h)

theorem triZ₂_pos {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) : 0 < triZ₂ a b c := by
  rw [← triZ₁_swap12 a b c]
  exact triZ₁_pos (triangleDomain_swap12 h)

theorem triZ₃_pos {a b c : ℝ} (h : (a, b, c) ∈ triangleDomain) : 0 < triZ₃ a b c := by
  rw [← triZ₂_swap23 a b c, ← triZ₁_swap12 a c b]
  exact triZ₁_pos (triangleDomain_swap12 (triangleDomain_swap23 h))

theorem triZ₁_lt_two_triZ₂_of_iso {b a : ℝ} (h : (b, a, a) ∈ triangleDomain) (hba : b < a) :
    triZ₁ b a a < 2 * triZ₂ b a a := by
  have hmem := h
  rcases h with ⟨haa, hba_mem, _, hdet⟩
  set x : ℝ := manuscriptKernelInverse (a + a)
  set y : ℝ := manuscriptKernelInverse (b + a)
  have hx : x ∈ Set.Ioo (-1 : ℝ) 1 := manuscriptKernelInverse_mem_Ioo haa
  have hy : y ∈ Set.Ioo (-1 : ℝ) 1 := manuscriptKernelInverse_mem_Ioo hba_mem
  have hyx : y < x := manuscriptKernelInverse_strictMonoOn hba_mem haa (by linarith)
  have hdet_fac : 0 < (1 - x) * (1 + x - 2 * y ^ 2) := by
    have heq : Sphere3.triangleGramDet x y y = (1 - x) * (1 + x - 2 * y ^ 2) := by
      unfold Sphere3.triangleGramDet; ring
    rwa [← heq]
  have hquad_pos : 0 < 1 + x - 2 * y ^ 2 := by
    have h1mx : 0 < 1 - x := by linarith [hx.2]
    exact (mul_pos_iff_of_pos_left h1mx).mp hdet_fac
  have hpsi_neg := Sphere3.triangle_iso_psi_neg hx.1 hx.2 hy.1 hy.2 hyx.le (by linarith)
  have hphi_x : (1 + x) * Sphere3.manuscriptPsi x = a + a := by
    change Sphere3.manuscriptPhi x = a + a
    rw [← stationaryKernel_eq_manuscriptPhi]
    exact stationaryKernel_manuscriptKernelInverse haa
  have hphi_y : (1 + y) * Sphere3.manuscriptPsi y = b + a := by
    change Sphere3.manuscriptPhi y = b + a
    rw [← stationaryKernel_eq_manuscriptPhi]
    exact stationaryKernel_manuscriptKernelInverse hba_mem
  have hlin_neg : 2 * (1 + x + 2 * y) * (b + a) - (3 + x + 4 * y) * (a + a) < 0 := by
    have h1 : 2 * (1 + x + 2 * y) * (1 + y) * Sphere3.manuscriptPsi y =
        2 * (1 + x + 2 * y) * (b + a) := by
      nlinarith [hphi_y]
    have h2 : (3 + x + 4 * y) * (1 + x) * Sphere3.manuscriptPsi x =
        (3 + x + 4 * y) * (a + a) := by
      nlinarith [hphi_x]
    linarith [hpsi_neg]
  have hz23 : triZ₃ b a a = triZ₂ b a a := by
    rw [← triZ₂_swap23 b a a]
  have hrow₁ := triZ_row₁ hmem
  have hrow₂ := triZ_row₂ hmem
  rw [hz23] at hrow₁ hrow₂
  have h_id :
      2 * (1 + x - 2 * y ^ 2) * (triZ₁ b a a - 2 * triZ₂ b a a) =
        2 * (1 + x + 2 * y) * (b + a) - (3 + x + 4 * y) * (a + a) := by
    linear_combination
      (2 * (1 + x + 2 * y)) * hrow₁ - (4 * (1 + y)) * hrow₂
  have hprod_neg : 2 * (1 + x - 2 * y ^ 2) * (triZ₁ b a a - 2 * triZ₂ b a a) < 0 := by
    rw [h_id]; exact hlin_neg
  have hz_neg : triZ₁ b a a - 2 * triZ₂ b a a < 0 := by
    by_contra hge
    have : 0 ≤ 2 * (1 + x - 2 * y ^ 2) * (triZ₁ b a a - 2 * triZ₂ b a a) :=
      mul_nonneg (by linarith) (le_of_not_gt hge)
    linarith
  linarith

private theorem triangleGramEnergy_eq_dot {k1 k2 k3 a b c : ℝ}
    (_hdet : Sphere3.triangleGramDet k1 k2 k3 ≠ 0) :
    Sphere3.triangleGramEnergy k1 k2 k3 a b c =
      a * Sphere3.triangleGramInverse₁ k1 k2 k3 a b c +
      b * Sphere3.triangleGramInverse₂ k1 k2 k3 a b c +
      c * Sphere3.triangleGramInverse₃ k1 k2 k3 a b c := by
  unfold Sphere3.triangleGramEnergy Sphere3.triangleGramInverse₁
    Sphere3.triangleGramInverse₂ Sphere3.triangleGramInverse₃ Sphere3.triangleGramDet at *
  field_simp [_hdet]
  ring

theorem manuscriptFaceEnergy_hasDerivAt {x b c : ℝ} (h : (x, b, c) ∈ triangleDomain) :
    HasDerivAt (fun t : ℝ => manuscriptFaceEnergy manuscriptKernelInverse t b c)
      (2 * triZ₁ x b c *
        (1 - deriv manuscriptKernelInverse (x + b) * triZ₂ x b c -
          deriv manuscriptKernelInverse (x + c) * triZ₃ x b c)) x := by
  have hmem := h
  rcases h with ⟨hbc, hxc, hxb, hdet⟩
  have hopen : ∀ᶠ t in 𝓝 x, (t, b, c) ∈ triangleDomain := by
    have hcont : ContinuousAt (fun t : ℝ => (t, b, c)) x := by fun_prop
    exact hcont.tendsto (isOpen_triangleDomain.mem_nhds hmem)
  have hg_xb : HasDerivAt manuscriptKernelInverse (deriv manuscriptKernelInverse (x + b)) (x + b) := by
    have hd := manuscriptKernelInverse_hasDerivAt hxb
    rwa [← deriv_manuscriptKernelInverse hxb] at hd
  have hg_xc : HasDerivAt manuscriptKernelInverse (deriv manuscriptKernelInverse (x + c)) (x + c) := by
    have hd := manuscriptKernelInverse_hasDerivAt hxc
    rwa [← deriv_manuscriptKernelInverse hxc] at hd
  have hk3_der :
      HasDerivAt (fun t : ℝ => manuscriptKernelInverse (t + b))
        (deriv manuscriptKernelInverse (x + b)) x := by
    have hc := hg_xb.comp x ((hasDerivAt_id x).add_const b)
    refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
    simp only [Function.comp_apply, id_eq]
  have hk2_der :
      HasDerivAt (fun t : ℝ => manuscriptKernelInverse (t + c))
        (deriv manuscriptKernelInverse (x + c)) x := by
    have hc := hg_xc.comp x ((hasDerivAt_id x).add_const c)
    refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
    simp only [Function.comp_apply, id_eq]
  have hdet_ne :
      Sphere3.triangleGramDet
        (manuscriptKernelInverse (b + c))
        (manuscriptKernelInverse (x + c))
        (manuscriptKernelInverse (x + b)) ≠ 0 := hdet.ne'
  have hk3_diff : DifferentiableAt ℝ (fun t : ℝ => manuscriptKernelInverse (t + b)) x :=
    hk3_der.differentiableAt
  have hk2_diff : DifferentiableAt ℝ (fun t : ℝ => manuscriptKernelInverse (t + c)) x :=
    hk2_der.differentiableAt
  have hz1_diff : DifferentiableAt ℝ (fun t : ℝ => triZ₁ t b c) x := by
    unfold triZ₁ Sphere3.triangleGramInverse₁ Sphere3.triangleGramDet
    fun_prop (disch := exact hdet_ne)
  have hz2_diff : DifferentiableAt ℝ (fun t : ℝ => triZ₂ t b c) x := by
    unfold triZ₂ Sphere3.triangleGramInverse₂ Sphere3.triangleGramDet
    fun_prop (disch := exact hdet_ne)
  have hz3_diff : DifferentiableAt ℝ (fun t : ℝ => triZ₃ t b c) x := by
    unfold triZ₃ Sphere3.triangleGramInverse₃ Sphere3.triangleGramDet
    fun_prop (disch := exact hdet_ne)
  have hz1_der := hz1_diff.hasDerivAt
  have hz2_der := hz2_diff.hasDerivAt
  have hz3_der := hz3_diff.hasDerivAt
  have hR1_eq : ∀ᶠ t in 𝓝 x,
      triZ₁ t b c + manuscriptKernelInverse (t + b) * triZ₂ t b c +
        manuscriptKernelInverse (t + c) * triZ₃ t b c = t := by
    filter_upwards [hopen] with t ht
    exact triZ_row₁ ht
  have hR2_eq : ∀ᶠ t in 𝓝 x,
      manuscriptKernelInverse (t + b) * triZ₁ t b c + triZ₂ t b c +
        manuscriptKernelInverse (b + c) * triZ₃ t b c = b := by
    filter_upwards [hopen] with t ht
    exact triZ_row₂ ht
  have hR3_eq : ∀ᶠ t in 𝓝 x,
      manuscriptKernelInverse (t + c) * triZ₁ t b c +
        manuscriptKernelInverse (b + c) * triZ₂ t b c + triZ₃ t b c = c := by
    filter_upwards [hopen] with t ht
    exact triZ_row₃ ht
  have hR1_der :=
    (hz1_der.add (hk3_der.mul hz2_der)).add (hk2_der.mul hz3_der)
  have hR1_val :
      deriv (fun t => triZ₁ t b c) x +
        (deriv manuscriptKernelInverse (x + b) * triZ₂ x b c +
          manuscriptKernelInverse (x + b) * deriv (fun t => triZ₂ t b c) x) +
        (deriv manuscriptKernelInverse (x + c) * triZ₃ x b c +
          manuscriptKernelInverse (x + c) * deriv (fun t => triZ₃ t b c) x) = 1 :=
    (hR1_der.congr_of_eventuallyEq
      (hR1_eq.mono fun t ht => by
        simp only [Pi.add_apply, Pi.mul_apply, id_eq]; exact ht.symm)).unique
      (hasDerivAt_id x)
  have hR2_der :=
    ((hk3_der.mul hz1_der).add hz2_der).add (hz3_der.const_mul (manuscriptKernelInverse (b + c)))
  have hR2_val :
      deriv manuscriptKernelInverse (x + b) * triZ₁ x b c +
        manuscriptKernelInverse (x + b) * deriv (fun t => triZ₁ t b c) x +
        deriv (fun t => triZ₂ t b c) x +
        manuscriptKernelInverse (b + c) * deriv (fun t => triZ₃ t b c) x = 0 :=
    (hR2_der.congr_of_eventuallyEq
      (hR2_eq.mono fun t ht => by
        simp only [Pi.add_apply, Pi.mul_apply]; exact ht.symm)).unique
      (hasDerivAt_const x b)
  have hR3_der :=
    ((hk2_der.mul hz1_der).add (hz2_der.const_mul (manuscriptKernelInverse (b + c)))).add hz3_der
  have hR3_val :
      deriv manuscriptKernelInverse (x + c) * triZ₁ x b c +
        manuscriptKernelInverse (x + c) * deriv (fun t => triZ₁ t b c) x +
        manuscriptKernelInverse (b + c) * deriv (fun t => triZ₂ t b c) x +
        deriv (fun t => triZ₃ t b c) x = 0 :=
    (hR3_der.congr_of_eventuallyEq
      (hR3_eq.mono fun t ht => by
        simp only [Pi.add_apply, Pi.mul_apply]; exact ht.symm)).unique
      (hasDerivAt_const x c)
  have hF_eq : ∀ᶠ t in 𝓝 x,
      manuscriptFaceEnergy manuscriptKernelInverse t b c =
        t * triZ₁ t b c + b * triZ₂ t b c + c * triZ₃ t b c := by
    filter_upwards [hopen] with t ht
    unfold manuscriptFaceEnergy triZ₁ triZ₂ triZ₃
    exact triangleGramEnergy_eq_dot ht.2.2.2.ne'
  have hF_der :=
    (((hasDerivAt_id x).mul hz1_der).add (hz2_der.const_mul b)).add (hz3_der.const_mul c)
  have hF_congr := hF_der.congr_of_eventuallyEq
    (hF_eq.mono fun t ht => by
      simp only [Pi.add_apply, Pi.mul_apply, id_eq]; exact ht)
  have hrow1 := triZ_row₁ hmem
  have hrow2 := triZ_row₂ hmem
  have hrow3 := triZ_row₃ hmem
  refine hF_congr.congr_deriv ?_
  have heq_alg :
      (1 * triZ₁ x b c + x * deriv (fun t => triZ₁ t b c) x) +
        b * deriv (fun t => triZ₂ t b c) x + c * deriv (fun t => triZ₃ t b c) x =
      2 * triZ₁ x b c *
        (1 - deriv manuscriptKernelInverse (x + b) * triZ₂ x b c -
          deriv manuscriptKernelInverse (x + c) * triZ₃ x b c) := by
    linear_combination
      -(deriv (fun t => triZ₁ t b c) x) * hrow1 -
      (deriv (fun t => triZ₂ t b c) x) * hrow2 -
      (deriv (fun t => triZ₃ t b c) x) * hrow3 +
      (triZ₁ x b c) * hR1_val +
      (triZ₂ x b c) * hR2_val +
      (triZ₃ x b c) * hR3_val
  simpa using heq_alg

theorem manuscriptFaceEnergy_continuousAt_first {x b c : ℝ} (h : (x, b, c) ∈ triangleDomain) :
    ContinuousAt (fun t : ℝ => manuscriptFaceEnergy manuscriptKernelInverse t b c) x :=
  (manuscriptFaceEnergy_hasDerivAt h).continuousAt

private theorem mvt_deriv_bound {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Set.Ioo (0 : ℝ) 2)
    (hs₂ : s₂ ∈ Set.Ioo (0 : ℝ) 2) (hlt : s₁ < s₂) :
    manuscriptKernelInverse s₂ - manuscriptKernelInverse s₁ <
      deriv manuscriptKernelInverse s₂ * (s₂ - s₁) := by
  have hcont : ContinuousOn manuscriptKernelInverse (Set.Icc s₁ s₂) := by
    intro u hu
    exact (manuscriptKernelInverse_continuousAt
      ⟨lt_of_lt_of_le hs₁.1 hu.1, lt_of_le_of_lt hu.2 hs₂.2⟩).continuousWithinAt
  have hdiff : ∀ u ∈ Set.Ioo s₁ s₂,
      HasDerivAt manuscriptKernelInverse (deriv manuscriptKernelInverse u) u := by
    intro u hu
    have hu_mem : u ∈ Set.Ioo (0 : ℝ) 2 := ⟨lt_trans hs₁.1 hu.1, lt_trans hu.2 hs₂.2⟩
    have hd := manuscriptKernelInverse_hasDerivAt hu_mem
    rwa [← deriv_manuscriptKernelInverse hu_mem] at hd
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    exists_hasDerivAt_eq_slope manuscriptKernelInverse (deriv manuscriptKernelInverse)
      hlt hcont hdiff
  have hξ_Ioo : ξ ∈ Set.Ioo (0 : ℝ) 2 := ⟨lt_trans hs₁.1 hξ_mem.1, lt_trans hξ_mem.2 hs₂.2⟩
  have hmono := manuscriptKernelInverse_deriv_strictMonoOn hξ_Ioo hs₂ hξ_mem.2
  rw [hξ_eq] at hmono
  have hpos : 0 < s₂ - s₁ := sub_pos.mpr hlt
  rwa [div_lt_iff₀ hpos] at hmono

theorem manuscriptFaceEnergy_strict_first {t₀ t₁ t₂ t₃ : ℝ}
    (ht32 : t₃ ≤ t₂) (ht21 : t₂ ≤ t₁) (ht10 : t₁ < t₀)
    (h1 : (t₁, t₂, t₃) ∈ triangleDomain) (h0 : (t₀, t₂, t₃) ∈ triangleDomain) :
    manuscriptFaceEnergy manuscriptKernelInverse t₀ t₂ t₃ <
      manuscriptFaceEnergy manuscriptKernelInverse t₁ t₂ t₃ := by
  let F : ℝ → ℝ := fun t => -manuscriptFaceEnergy manuscriptKernelInverse t t₂ t₃
  let F' : ℝ → ℝ := fun t =>
    -(2 * triZ₁ t t₂ t₃ *
      (1 - deriv manuscriptKernelInverse (t + t₂) * triZ₂ t t₂ t₃ -
        deriv manuscriptKernelInverse (t + t₃) * triZ₃ t t₂ t₃))
  have hmono : StrictMonoOn F (Set.Icc t₁ t₀) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := F') (convex_Icc t₁ t₀) ?_ ?_ ?_
    · intro x hx
      have hx_dom : (x, t₂, t₃) ∈ triangleDomain :=
        triangleDomain_segment_first h1 h0 hx.1 hx.2
      exact (manuscriptFaceEnergy_continuousAt_first hx_dom).neg.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_dom : (x, t₂, t₃) ∈ triangleDomain :=
        triangleDomain_segment_first h1 h0 hx.1.le hx.2.le
      exact (manuscriptFaceEnergy_hasDerivAt hx_dom).neg.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_dom : (x, t₂, t₃) ∈ triangleDomain :=
        triangleDomain_segment_first h1 h0 hx.1.le hx.2.le
      have hx_t3 : t₃ < x := by linarith [ht32, ht21, hx.1]
      have hz13 : triZ₁ x t₂ t₃ < triZ₃ x t₂ t₃ := triZ_lt_13 hx_dom hx_t3
      have hrow1 := triZ_row₁ hx_dom
      have hrow3 := triZ_row₃ hx_dom
      have hsub_row :
          (1 - manuscriptKernelInverse (x + t₃)) * (triZ₁ x t₂ t₃ - triZ₃ x t₂ t₃) +
            (manuscriptKernelInverse (x + t₂) - manuscriptKernelInverse (t₂ + t₃)) *
              triZ₂ x t₂ t₃ = x - t₃ := by
        linarith [hrow1, hrow3]
      have hk13_lt1 : manuscriptKernelInverse (x + t₃) < 1 :=
        (manuscriptKernelInverse_mem_Ioo hx_dom.2.1).2
      have hterm1_neg :
          (1 - manuscriptKernelInverse (x + t₃)) * (triZ₁ x t₂ t₃ - triZ₃ x t₂ t₃) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      have hmvt := mvt_deriv_bound h1.1 hx_dom.2.2.1 (by linarith : t₂ + t₃ < x + t₂)
      have hz2_pos : 0 < triZ₂ x t₂ t₃ := triZ₂_pos hx_dom
      have hterm2_lt :
          (manuscriptKernelInverse (x + t₂) - manuscriptKernelInverse (t₂ + t₃)) *
            triZ₂ x t₂ t₃ <
          deriv manuscriptKernelInverse (x + t₂) * triZ₂ x t₂ t₃ * (x - t₃) := by
        nlinarith [hmvt, hz2_pos]
      have hcomp_gt : 1 < deriv manuscriptKernelInverse (x + t₂) * triZ₂ x t₂ t₃ := by
        have hx_pos : 0 < x - t₃ := sub_pos.mpr hx_t3
        have hlt_mul : x - t₃ < deriv manuscriptKernelInverse (x + t₂) * triZ₂ x t₂ t₃ * (x - t₃) := by
          linarith
        exact (lt_mul_iff_one_lt_left hx_pos).mp hlt_mul
      have hneg := Sphere3.triangle_gradient_negative_of_comparison
        (triZ₁ x t₂ t₃) (triZ₃ x t₂ t₃) (triZ₂ x t₂ t₃)
        (deriv manuscriptKernelInverse (x + t₃))
        (deriv manuscriptKernelInverse (x + t₂))
        (triZ₁_pos hx_dom) (triZ₃_pos hx_dom)
        (manuscriptKernelInverse_deriv_pos hx_dom.2.1) hcomp_gt.le
      dsimp only [F']
      linarith [hneg]
  have hlt := hmono ⟨le_rfl, ht10.le⟩ ⟨ht10.le, le_rfl⟩ ht10
  dsimp only [F] at hlt
  linarith

theorem manuscriptFaceEnergy_strict_second {t₀ t₁ t₂ t₃ : ℝ}
    (ht32 : t₃ ≤ t₂) (ht21 : t₂ < t₁) (_ht10 : t₁ ≤ t₀)
    (h2 : (t₂, t₃, t₀) ∈ triangleDomain) (h1 : (t₁, t₃, t₀) ∈ triangleDomain) :
    manuscriptFaceEnergy manuscriptKernelInverse t₁ t₃ t₀ <
      manuscriptFaceEnergy manuscriptKernelInverse t₂ t₃ t₀ := by
  let F : ℝ → ℝ := fun t => -manuscriptFaceEnergy manuscriptKernelInverse t t₃ t₀
  let F' : ℝ → ℝ := fun t =>
    -(2 * triZ₁ t t₃ t₀ *
      (1 - deriv manuscriptKernelInverse (t + t₃) * triZ₂ t t₃ t₀ -
        deriv manuscriptKernelInverse (t + t₀) * triZ₃ t t₃ t₀))
  have hmono : StrictMonoOn F (Set.Icc t₂ t₁) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := F') (convex_Icc t₂ t₁) ?_ ?_ ?_
    · intro x hx
      have hx_dom : (x, t₃, t₀) ∈ triangleDomain :=
        triangleDomain_segment_first h2 h1 hx.1 hx.2
      exact (manuscriptFaceEnergy_continuousAt_first hx_dom).neg.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_dom : (x, t₃, t₀) ∈ triangleDomain :=
        triangleDomain_segment_first h2 h1 hx.1.le hx.2.le
      exact (manuscriptFaceEnergy_hasDerivAt hx_dom).neg.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_dom : (x, t₃, t₀) ∈ triangleDomain :=
        triangleDomain_segment_first h2 h1 hx.1.le hx.2.le
      have hx_t3 : t₃ < x := by linarith [ht32, hx.1]
      have hz12 : triZ₁ x t₃ t₀ < triZ₂ x t₃ t₀ := triZ_lt_12 hx_dom hx_t3
      have hrow1 := triZ_row₁ hx_dom
      have hrow2 := triZ_row₂ hx_dom
      have hsub_row :
          (1 - manuscriptKernelInverse (x + t₃)) * (triZ₁ x t₃ t₀ - triZ₂ x t₃ t₀) +
            (manuscriptKernelInverse (x + t₀) - manuscriptKernelInverse (t₃ + t₀)) *
              triZ₃ x t₃ t₀ = x - t₃ := by
        linarith [hrow1, hrow2]
      have hk12_lt1 : manuscriptKernelInverse (x + t₃) < 1 :=
        (manuscriptKernelInverse_mem_Ioo hx_dom.2.2.1).2
      have hterm1_neg :
          (1 - manuscriptKernelInverse (x + t₃)) * (triZ₁ x t₃ t₀ - triZ₂ x t₃ t₀) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      have hmvt := mvt_deriv_bound h2.1 hx_dom.2.1 (by linarith : t₃ + t₀ < x + t₀)
      have hz3_pos : 0 < triZ₃ x t₃ t₀ := triZ₃_pos hx_dom
      have hterm2_lt :
          (manuscriptKernelInverse (x + t₀) - manuscriptKernelInverse (t₃ + t₀)) *
            triZ₃ x t₃ t₀ <
          deriv manuscriptKernelInverse (x + t₀) * triZ₃ x t₃ t₀ * (x - t₃) := by
        nlinarith [hmvt, hz3_pos]
      have hcomp_gt : 1 < deriv manuscriptKernelInverse (x + t₀) * triZ₃ x t₃ t₀ := by
        have hx_pos : 0 < x - t₃ := sub_pos.mpr hx_t3
        have hlt_mul : x - t₃ < deriv manuscriptKernelInverse (x + t₀) * triZ₃ x t₃ t₀ * (x - t₃) := by
          linarith
        exact (lt_mul_iff_one_lt_left hx_pos).mp hlt_mul
      have hneg := Sphere3.triangle_gradient_negative_of_comparison
        (triZ₁ x t₃ t₀) (triZ₂ x t₃ t₀) (triZ₃ x t₃ t₀)
        (deriv manuscriptKernelInverse (x + t₃))
        (deriv manuscriptKernelInverse (x + t₀))
        (triZ₁_pos hx_dom) (triZ₂_pos hx_dom)
        (manuscriptKernelInverse_deriv_pos hx_dom.2.2.1) hcomp_gt.le
      dsimp only [F']
      exact neg_pos.mpr hneg
  have hlt := hmono ⟨le_rfl, ht21.le⟩ ⟨ht21.le, le_rfl⟩ ht21
  dsimp only [F] at hlt
  linarith

theorem manuscriptFaceEnergy_iso_lt {b a : ℝ} (hba : b < a)
    (hb : (b, a, a) ∈ triangleDomain) (ha : (a, a, a) ∈ triangleDomain) :
    manuscriptFaceEnergy manuscriptKernelInverse a a a <
      manuscriptFaceEnergy manuscriptKernelInverse b a a := by
  let F : ℝ → ℝ := fun t => -manuscriptFaceEnergy manuscriptKernelInverse t a a
  let F' : ℝ → ℝ := fun t =>
    -(2 * triZ₁ t a a *
      (1 - deriv manuscriptKernelInverse (t + a) * triZ₂ t a a -
        deriv manuscriptKernelInverse (t + a) * triZ₃ t a a))
  have hmono : StrictMonoOn F (Set.Icc b a) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (f' := F') (convex_Icc b a) ?_ ?_ ?_
    · intro x hx
      have hx_dom : (x, a, a) ∈ triangleDomain :=
        triangleDomain_segment_first hb ha hx.1 hx.2
      exact (manuscriptFaceEnergy_continuousAt_first hx_dom).neg.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_dom : (x, a, a) ∈ triangleDomain :=
        triangleDomain_segment_first hb ha hx.1.le hx.2.le
      exact (manuscriptFaceEnergy_hasDerivAt hx_dom).neg.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_dom : (x, a, a) ∈ triangleDomain :=
        triangleDomain_segment_first hb ha hx.1.le hx.2.le
      have hx_lt_a : x < a := hx.2
      have hlim_s : Tendsto (fun s : ℝ => (x, s, a)) (𝓝[>] a) (𝓝 (x, a, a)) := by
        have hc : Continuous (fun s : ℝ => (x, s, a)) := by fun_prop
        simpa using (hc.continuousAt (x := a)).tendsto.mono_left nhdsWithin_le_nhds
      have hev_dom : ∀ᶠ s in 𝓝[>] a, (x, s, a) ∈ triangleDomain :=
        hlim_s (isOpen_triangleDomain.mem_nhds hx_dom)
      have hev_gt : ∀ᶠ s in 𝓝[>] a, a < s := self_mem_nhdsWithin
      have hev_cmp :
          ∀ᶠ s in 𝓝[>] a,
            (1 : ℝ) ≤ ((manuscriptKernelInverse (x + s) - manuscriptKernelInverse (x + a)) / (s - a)) *
              triZ₁ x s a := by
        filter_upwards [hev_dom, hev_gt] with s hs_dom has
        have hz23 : triZ₂ x s a < triZ₃ x s a := triZ_lt_23 hs_dom has
        have hrow2 := triZ_row₂ hs_dom
        have hrow3 := triZ_row₃ hs_dom
        have hsub :
            (manuscriptKernelInverse (x + s) - manuscriptKernelInverse (x + a)) * triZ₁ x s a +
              (1 - manuscriptKernelInverse (s + a)) * (triZ₂ x s a - triZ₃ x s a) = s - a := by
          linarith [hrow2, hrow3]
        have hk23_lt1 : manuscriptKernelInverse (s + a) < 1 :=
          (manuscriptKernelInverse_mem_Ioo hs_dom.1).2
        have hterm2_neg :
            (1 - manuscriptKernelInverse (s + a)) * (triZ₂ x s a - triZ₃ x s a) < 0 :=
          mul_neg_of_pos_of_neg (by linarith) (by linarith)
        have hmul_gt : s - a < (manuscriptKernelInverse (x + s) - manuscriptKernelInverse (x + a)) * triZ₁ x s a := by
          linarith
        have hs_pos : 0 < s - a := sub_pos.mpr has
        have hdiv_gt :
            (1 : ℝ) < ((manuscriptKernelInverse (x + s) - manuscriptKernelInverse (x + a)) / (s - a)) *
              triZ₁ x s a := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hs_pos]
          linarith
        exact hdiv_gt.le
      have hderiv_xa :
          HasDerivAt (fun s : ℝ => manuscriptKernelInverse (x + s))
            (deriv manuscriptKernelInverse (x + a)) a := by
        have hd := manuscriptKernelInverse_hasDerivAt hx_dom.2.1
        rw [← deriv_manuscriptKernelInverse hx_dom.2.1] at hd
        have hc := hd.comp a ((hasDerivAt_id a).const_add x)
        refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv (by simp)
        simp only [Function.comp_apply]
      have htend_slope :
          Tendsto (fun s : ℝ => (manuscriptKernelInverse (x + s) - manuscriptKernelInverse (x + a)) / (s - a))
            (𝓝[>] a) (𝓝 (deriv manuscriptKernelInverse (x + a))) := by
        have ht0 := (hasDerivAt_iff_tendsto_slope.mp hderiv_xa).mono_left
          (nhdsWithin_mono a (s := Set.Ioi a) (t := {a}ᶜ) fun s hs => ne_of_gt hs)
        have hslope_eq : slope (fun s : ℝ => manuscriptKernelInverse (x + s)) a =
            fun s : ℝ => (manuscriptKernelInverse (x + s) - manuscriptKernelInverse (x + a)) / (s - a) := by
          funext s; exact slope_def_field _ _ _
        rwa [hslope_eq] at ht0
      have htend_z1 : Tendsto (fun s : ℝ => triZ₁ x s a) (𝓝[>] a) (𝓝 (triZ₁ x a a)) :=
        (triZ₁_continuousAt_second hx_dom).tendsto.mono_left nhdsWithin_le_nhds
      have hge_one : 1 ≤ deriv manuscriptKernelInverse (x + a) * triZ₁ x a a :=
        ge_of_tendsto (htend_slope.mul htend_z1) hev_cmp
      have hneg := Sphere3.triangle_isosceles_derivative_negative
        (triZ₁ x a a) (triZ₂ x a a) (deriv manuscriptKernelInverse (x + a))
        (triZ₁_pos hx_dom) (manuscriptKernelInverse_deriv_pos hx_dom.2.1)
        hge_one (triZ₁_lt_two_triZ₂_of_iso hx_dom hx_lt_a)
      have hz23 : triZ₃ x a a = triZ₂ x a a := (triZ₂_swap23 x a a).symm
      dsimp only [F']
      rw [hz23]
      linarith [hneg]
  have hlt := hmono ⟨le_rfl, hba.le⟩ ⟨hba.le, le_rfl⟩ hba
  dsimp only [F] at hlt
  linarith

end SphericalTetrahedron
