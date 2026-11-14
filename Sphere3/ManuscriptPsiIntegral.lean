module

public import Sphere3.ManuscriptEtaKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Integral representation of `Ψ` and the triangle ordering signs

This module formalizes the improper integral representation
`Ψ(x) = arccos(x) / √(1 - x²) = ∫₀^∞ (s² + 2xs + 1)⁻¹ ds` for `x ∈ (-1, 1)`,
along with the two strict integral sign inequalities of Section 3 of the
manuscript:

1. Strict inverse ordering `z₁ < z₂` for `t₁ > t₂` (`triangle_gram_inverse_lt`),
   derived via Appendix A (`(A.2)`) and `manuscriptOrderIntegrand_pos`.
2. Strict negativity of the isosceles comparison integral (`triangle_iso_psi_neg`),
   derived via `manuscriptIsoIntegrand_neg`.
3. The spherical triangle inequality characterization `det K(cos a, cos b, cos c) > 0`
   on `(0, π)³` (`triangleGramDet_cos_pos_iff`).
-/

noncomputable section

namespace Sphere3

open MeasureTheory Filter Set
open scoped Topology

/-- The kernel `Ψ(x) = arccos(x) / √(1 - x²)`. -/
def manuscriptPsi (x : ℝ) : ℝ :=
  Real.arccos x / Real.sqrt (1 - x ^ 2)

/-- The stationarity kernel expressed via `manuscriptPsi`. -/
def manuscriptPhi (x : ℝ) : ℝ :=
  (1 + x) * manuscriptPsi x

theorem manuscriptPsi_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < manuscriptPsi x := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  exact div_pos (Real.arccos_pos.mpr hx.2) (Real.sqrt_pos.mpr h1)

theorem manuscriptPhi_pos {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < manuscriptPhi x :=
  mul_pos (by linarith [hx.1]) (manuscriptPsi_pos hx)

theorem manuscriptPsi_cos {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi) :
    manuscriptPsi (Real.cos θ) = θ / Real.sin θ := by
  unfold manuscriptPsi
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have harc : Real.arccos (Real.cos θ) = θ := Real.arccos_cos hθ0.le hθpi.le
  have hsqrt : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [← Real.sin_arccos, harc]
  rw [harc, hsqrt]

theorem manuscriptPhi_cos {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi) :
    manuscriptPhi (Real.cos θ) = θ * (1 + Real.cos θ) / Real.sin θ := by
  unfold manuscriptPhi
  rw [manuscriptPsi_cos hθ0 hθpi]
  ring

private theorem arccos_eq_half_pi_sub_arctan {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.arccos x = Real.pi / 2 - Real.arctan (x / Real.sqrt (1 - x ^ 2)) := by
  set θ : ℝ := Real.arccos x
  have hθ0 : 0 < θ := Real.arccos_pos.mpr hx.2
  have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr hx.1
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hr : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h1
  have hsin : Real.sin θ = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have hcos : Real.cos θ = x := Real.cos_arccos hx.1.le hx.2.le
  have hu1 : -(Real.pi / 2) < Real.pi / 2 - θ := by linarith
  have hu2 : Real.pi / 2 - θ < Real.pi / 2 := by linarith
  have htan : Real.tan (Real.pi / 2 - θ) = x / Real.sqrt (1 - x ^ 2) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hcos, hsin]
  have hrec := Real.arctan_tan hu1 hu2
  rw [htan] at hrec
  linarith

private theorem psi_quad_pos {x s : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < s ^ 2 + 2 * x * s + 1 := by
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  nlinarith [sq_nonneg (s + x)]

private theorem psi_antideriv_hasDerivAt {x s : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (fun t : ℝ => Real.arctan ((t + x) / Real.sqrt (1 - x ^ 2)) / Real.sqrt (1 - x ^ 2))
      (1 / (s ^ 2 + 2 * x * s + 1)) s := by
  set r : ℝ := Real.sqrt (1 - x ^ 2)
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hr : 0 < r := Real.sqrt_pos.mpr h1
  have hr0 : r ≠ 0 := hr.ne'
  have hr2 : r ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1.le
  have hq0 : s ^ 2 + 2 * x * s + 1 ≠ 0 := (psi_quad_pos hx).ne'
  have hlin : HasDerivAt (fun t : ℝ => (t + x) / r) (1 / r) s := by
    simpa [div_eq_mul_inv] using (((hasDerivAt_id s).add_const x).mul_const r⁻¹)
  have harctan := hlin.arctan
  have hdiv := harctan.div_const r
  convert hdiv using 1
  have hA : 1 + ((s + x) / r) ^ 2 ≠ 0 := by positivity
  have hden : (1 + ((s + x) / r) ^ 2) * r ^ 2 = s ^ 2 + 2 * x * s + 1 := by
    field_simp [hr0]
    linear_combination hr2
  have hrat : 1 / (1 + ((s + x) / r) ^ 2) * (1 / r) / r =
      1 / ((1 + ((s + x) / r) ^ 2) * r ^ 2) := by
    field_simp [hA, hr0]
  rw [hrat, hden]

private theorem psi_antideriv_tendsto {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun t : ℝ => Real.arctan ((t + x) / Real.sqrt (1 - x ^ 2)) / Real.sqrt (1 - x ^ 2))
      atTop (𝓝 ((Real.pi / 2) / Real.sqrt (1 - x ^ 2))) := by
  set r : ℝ := Real.sqrt (1 - x ^ 2)
  have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hr : 0 < r := Real.sqrt_pos.mpr h1
  have hlin : Tendsto (fun t : ℝ => (t + x) / r) atTop atTop :=
    ((tendsto_id.atTop_add (tendsto_const_nhds (x := x))).atTop_mul_const (inv_pos.mpr hr)).congr
      (fun t => by simp [div_eq_mul_inv])
  have harc : Tendsto (fun t : ℝ => Real.arctan ((t + x) / r)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hlin
  exact harc.div_const r

theorem manuscriptPsi_quad_integrableOn {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun s : ℝ => 1 / (s ^ 2 + 2 * x * s + 1)) (Set.Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_deriv_of_nonneg'
    (fun s _ => psi_antideriv_hasDerivAt hx)
    (fun s _ => (div_pos zero_lt_one (psi_quad_pos hx)).le)
    (psi_antideriv_tendsto hx)

theorem manuscriptPsi_eq_quad_integral {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    manuscriptPsi x = ∫ s in Set.Ioi (0 : ℝ), 1 / (s ^ 2 + 2 * x * s + 1) := by
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ))
    (fun s _ => psi_antideriv_hasDerivAt hx)
    (fun s _ => (div_pos zero_lt_one (psi_quad_pos hx)).le)
    (psi_antideriv_tendsto hx)
  rw [hint]
  simp only [zero_add]
  have harc := arccos_eq_half_pi_sub_arctan hx
  unfold manuscriptPsi
  rw [harc, sub_div]

theorem eta_kernel_eq_quad {x s : ℝ} (hs : s ≠ 0) :
    1 / (2 * s * (manuscriptEta s + x)) = 1 / (s ^ 2 + 2 * x * s + 1) := by
  unfold manuscriptEta
  have h : 2 * s * ((s ^ 2 + 1) / (2 * s) + x) = s ^ 2 + 2 * x * s + 1 := by
    field_simp [hs]
    ring
  rw [h]

theorem manuscriptPsi_eta_integrableOn {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun s : ℝ => 1 / (2 * s * (manuscriptEta s + x))) (Set.Ioi (0 : ℝ)) := by
  refine (manuscriptPsi_quad_integrableOn hx).congr_fun ?_ measurableSet_Ioi
  intro s hs
  exact (eta_kernel_eq_quad (ne_of_gt hs)).symm

theorem manuscriptPsi_eq_eta_integral {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    manuscriptPsi x = ∫ s in Set.Ioi (0 : ℝ), 1 / (2 * s * (manuscriptEta s + x)) := by
  rw [manuscriptPsi_eq_quad_integral hx]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro s hs
  exact (eta_kernel_eq_quad (ne_of_gt hs)).symm

private theorem cos_phi_diff_quotient
    {p q0 : ℝ} (hp0 : 0 < p) (hppi : p < Real.pi)
    (hq0 : 0 < q0) (hqp : q0 < p) (hqpi : p + q0 < Real.pi) :
    let u := Real.cos p
    let v := Real.cos q0
    let X := Real.cos (p + q0)
    let Y := Real.cos (p - q0)
    (manuscriptPhi Y - manuscriptPhi X) / (Y - X) =
      (manuscriptPsi u - manuscriptPsi v) / (v - u) ∧
    manuscriptPhi X + manuscriptPhi Y =
      2 * ((1 - u ^ 2) * manuscriptPsi u - (1 - v ^ 2) * manuscriptPsi v) / (v - u) := by
  intro u v X Y
  have hpa : 0 < p + q0 := by linarith
  have hpb : 0 < p - q0 := by linarith
  have hpbpi : p - q0 < Real.pi := by linarith
  have hq0pi : q0 < Real.pi := by linarith
  have hsp : 0 < Real.sin p := Real.sin_pos_of_pos_of_lt_pi hp0 hppi
  have hsq : 0 < Real.sin q0 := Real.sin_pos_of_pos_of_lt_pi hq0 hq0pi
  have hsa : 0 < Real.sin (p + q0) := Real.sin_pos_of_pos_of_lt_pi hpa hqpi
  have hsb : 0 < Real.sin (p - q0) := Real.sin_pos_of_pos_of_lt_pi hpb hpbpi
  have huv : u < v := Real.strictAntiOn_cos ⟨hq0.le, hq0pi.le⟩ ⟨hp0.le, hppi.le⟩ hqp
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  have hYX : Y - X ≠ 0 := by
    have hlt : X < Y := Real.strictAntiOn_cos ⟨hpb.le, hpbpi.le⟩ ⟨hpa.le, hqpi.le⟩ (by linarith)
    exact sub_ne_zero.mpr hlt.ne'
  have hφX := manuscriptPhi_cos hpa hqpi
  have hφY := manuscriptPhi_cos hpb hpbpi
  have hψu := manuscriptPsi_cos hp0 hppi
  have hψv := manuscriptPsi_cos hq0 hq0pi
  have hca : X = u * v - Real.sin p * Real.sin q0 := by
    dsimp [X, u, v]; exact Real.cos_add p q0
  have hcb : Y = u * v + Real.sin p * Real.sin q0 := by
    dsimp [Y, u, v]; exact Real.cos_sub p q0
  have hsin_a : Real.sin (p + q0) = Real.sin p * v + u * Real.sin q0 := by
    dsimp [u, v]; exact Real.sin_add p q0
  have hsin_b : Real.sin (p - q0) = Real.sin p * v - u * Real.sin q0 := by
    dsimp [u, v]; exact Real.sin_sub p q0
  have hsp2 : Real.sin p ^ 2 = 1 - u ^ 2 := by
    dsimp [u]; linarith [Real.sin_sq_add_cos_sq p]
  have hsq2 : Real.sin q0 ^ 2 = 1 - v ^ 2 := by
    dsimp [v]; linarith [Real.sin_sq_add_cos_sq q0]
  have hp_eq : p = Real.sin p * manuscriptPsi u := by
    rw [hψu]; field_simp [hsp.ne']
  have hq_eq : q0 = Real.sin q0 * manuscriptPsi v := by
    rw [hψv]; field_simp [hsq.ne']
  have hYX_eq : Y - X = 2 * Real.sin p * Real.sin q0 := by
    rw [hcb, hca]; ring
  have hfacX : (1 + (u * v - Real.sin p * Real.sin q0)) * (v - u) =
      (Real.sin p - Real.sin q0) * (Real.sin p * v + u * Real.sin q0) := by
    have hspq : (Real.sin p - Real.sin q0) * (Real.sin p * v + u * Real.sin q0) =
        Real.sin p ^ 2 * v - u * Real.sin q0 ^ 2 - Real.sin p * Real.sin q0 * (v - u) := by ring
    rw [hspq, hsp2, hsq2]; ring
  have hfacY : (1 + (u * v + Real.sin p * Real.sin q0)) * (v - u) =
      (Real.sin p + Real.sin q0) * (Real.sin p * v - u * Real.sin q0) := by
    have hspq : (Real.sin p + Real.sin q0) * (Real.sin p * v - u * Real.sin q0) =
        Real.sin p ^ 2 * v - u * Real.sin q0 ^ 2 + Real.sin p * Real.sin q0 * (v - u) := by ring
    rw [hspq, hsp2, hsq2]; ring
  have hpq_add : p + q0 = Real.sin p * manuscriptPsi u + Real.sin q0 * manuscriptPsi v := by
    linarith [hp_eq, hq_eq]
  have hpq_sub : p - q0 = Real.sin p * manuscriptPsi u - Real.sin q0 * manuscriptPsi v := by
    linarith [hp_eq, hq_eq]
  have hφX_simp : manuscriptPhi X =
      (Real.sin p * manuscriptPsi u + Real.sin q0 * manuscriptPsi v) *
        (Real.sin p - Real.sin q0) / (v - u) := by
    rw [hφX]
    change (p + q0) * (1 + X) / Real.sin (p + q0) = _
    rw [hca, hsin_a, hpq_add]
    have hsin_a_ne : Real.sin p * v + u * Real.sin q0 ≠ 0 := by
      rw [← hsin_a]; exact hsa.ne'
    rw [div_eq_div_iff hsin_a_ne hvu, mul_assoc, hfacX]
    ring
  have hφY_simp : manuscriptPhi Y =
      (Real.sin p * manuscriptPsi u - Real.sin q0 * manuscriptPsi v) *
        (Real.sin p + Real.sin q0) / (v - u) := by
    rw [hφY]
    change (p - q0) * (1 + Y) / Real.sin (p - q0) = _
    rw [hcb, hsin_b, hpq_sub]
    have hsin_b_ne : Real.sin p * v - u * Real.sin q0 ≠ 0 := by
      rw [← hsin_b]; exact hsb.ne'
    rw [div_eq_div_iff hsin_b_ne hvu, mul_assoc, hfacY]
    ring
  constructor
  · rw [hφY_simp, hφX_simp, hYX_eq]
    have hspq : 2 * Real.sin p * Real.sin q0 ≠ 0 := by positivity
    field_simp [hvu, hspq]
    ring
  · rw [hφX_simp, hφY_simp]
    field_simp [hvu]
    have hsum_sq :
        (Real.sin p * manuscriptPsi u + Real.sin q0 * manuscriptPsi v) * (Real.sin p - Real.sin q0) +
          (Real.sin p * manuscriptPsi u - Real.sin q0 * manuscriptPsi v) * (Real.sin p + Real.sin q0) =
        2 * (manuscriptPsi u * Real.sin p ^ 2 - manuscriptPsi v * Real.sin q0 ^ 2) := by ring
    rw [hsum_sq, hsp2, hsq2]

theorem triangle_J_eq_four_psi
    {a b c : ℝ} (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc0 : 0 < c) (hcpi : c < Real.pi)
    (hba : b < a) (hsum : a + b + c < 2 * Real.pi)
    (hdiff : a - b < c) :
    let X := Real.cos a
    let Y := Real.cos b
    let Z := Real.cos c
    let u := Real.cos ((a + b) / 2)
    let v := Real.cos ((a - b) / 2)
    let w := Real.cos (c / 2)
    let m := (manuscriptPhi Y - manuscriptPhi X) / (Y - X)
    ((1 + X + Y + Z) * manuscriptPhi Z -
      (1 + Z) * (manuscriptPhi X + manuscriptPhi Y - 2 * m) -
      (X + Y) ^ 2 * m) =
      4 * (w * (w ^ 2 + u * v) * manuscriptPsi w +
        (u ^ 2 * (w ^ 2 - v ^ 2) * manuscriptPsi u +
         v ^ 2 * (u ^ 2 - w ^ 2) * manuscriptPsi v) / (v - u)) := by
  intro X Y Z u v w m
  set p : ℝ := (a + b) / 2
  set q0 : ℝ := (a - b) / 2
  set r : ℝ := c / 2
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hppi : p < Real.pi := by dsimp [p]; linarith
  have hq0 : 0 < q0 := by dsimp [q0]; linarith
  have hqp : q0 < p := by dsimp [p, q0]; linarith
  have hqpi : p + q0 < Real.pi := by dsimp [p, q0]; linarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hrpi : r < Real.pi := by dsimp [r]; linarith
  have hc_eq : c = 2 * r := by dsimp [r]; ring
  have ha_eq : a = p + q0 := by dsimp [p, q0]; ring
  have hb_eq : b = p - q0 := by dsimp [p, q0]; ring
  have hX : X = Real.cos (p + q0) := by dsimp [X]; rw [ha_eq]
  have hY : Y = Real.cos (p - q0) := by dsimp [Y]; rw [hb_eq]
  have hpair := cos_phi_diff_quotient hp0 hppi hq0 hqp hqpi
  have hm : m = (manuscriptPsi u - manuscriptPsi v) / (v - u) := by
    dsimp [m]; rw [hX, hY]; exact hpair.1
  have hsum_phi : manuscriptPhi X + manuscriptPhi Y =
      2 * ((1 - u ^ 2) * manuscriptPsi u - (1 - v ^ 2) * manuscriptPsi v) / (v - u) := by
    rw [hX, hY]; exact hpair.2
  have hφZ : manuscriptPhi Z = 2 * w * manuscriptPsi w := by
    have hZcos : Z = Real.cos (2 * r) := by dsimp [Z]; rw [hc_eq]
    have hwcos : w = Real.cos r := rfl
    rw [hZcos, hwcos, manuscriptPhi_cos (by linarith) (by linarith), manuscriptPsi_cos hr0 hrpi]
    have hsr : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 hrpi
    have hsc : 0 < Real.sin (2 * r) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hcos2 : Real.cos (2 * r) = 2 * Real.cos r ^ 2 - 1 := Real.cos_two_mul r
    have hsin2 : Real.sin (2 * r) = 2 * Real.sin r * Real.cos r := Real.sin_two_mul r
    rw [hsin2] at hsc
    rw [hcos2, hsin2]
    have hwr : Real.sin r * Real.cos r ≠ 0 := by
      intro h; apply hsc.ne'; linarith
    have hcr : Real.cos r ≠ 0 := right_ne_zero_of_mul hwr
    field_simp [hsr.ne', hcr]
    ring
  have hZ : Z = 2 * w ^ 2 - 1 := by
    have hwcos : w = Real.cos r := rfl
    rw [show Z = Real.cos (2 * r) by dsimp [Z]; rw [hc_eq], hwcos, Real.cos_two_mul]
  have hXY : X + Y = 2 * u * v := by
    rw [hX, hY, Real.cos_add, Real.cos_sub]
    dsimp [u, v]
    ring
  have huv : u < v := Real.strictAntiOn_cos ⟨hq0.le, (by linarith : q0 ≤ Real.pi)⟩
    ⟨hp0.le, hppi.le⟩ hqp
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
  rw [hm, hsum_phi, hφZ]
  have hZ1 : 1 + Z = 2 * w ^ 2 := by linarith [hZ]
  have hsumXYZ : 1 + X + Y + Z = 2 * (w ^ 2 + u * v) := by linarith [hZ, hXY]
  rw [hsumXYZ, hZ1, hXY]
  field_simp [hvu]
  ring

/-- The inverse-ordering integral is strictly positive on the admissible
spherical half-angle range `-w < u < w < v < 1`. -/
theorem manuscriptOrderIntegrand_integral_pos
    {u v w : ℝ} (huw : u < w) (hwu : -w < u) (hwv : w < v) (hv : v < 1) :
    0 < ∫ s in Set.Ioi (0 : ℝ), manuscriptOrderIntegrand u v w s := by
  have hu_mem : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hv_mem : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hv⟩
  have hw_mem : w ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hvu : v - u ≠ 0 := by linarith
  have hint : IntegrableOn (manuscriptOrderIntegrand u v w) (Set.Ioi (0 : ℝ)) := by
    have hcomb : IntegrableOn
        (fun s =>
          (-(2 * w * (w ^ 2 + u * v)) * (1 / (2 * s * (manuscriptEta s + w))) +
            -(2 * u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u)))) +
          -(2 * v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v))))
        (Set.Ioi (0 : ℝ)) :=
      (((manuscriptPsi_eta_integrableOn hw_mem).const_mul _).add
        ((manuscriptPsi_eta_integrableOn hu_mem).const_mul _)).add
        ((manuscriptPsi_eta_integrableOn hv_mem).const_mul _)
    refine hcomb.congr_fun ?_ measurableSet_Ioi
    intro s hs
    dsimp only
    have heta : 1 ≤ manuscriptEta s := manuscriptEta_ge_one s hs
    have hu0 : manuscriptEta s + u ≠ 0 := by linarith [hu_mem.1]
    have hv0 : manuscriptEta s + v ≠ 0 := by linarith [hv_mem.1]
    have hw0 : manuscriptEta s + w ≠ 0 := by linarith [hw_mem.1]
    have hid := triangle_order_integrand_identity (manuscriptEta s) u v w hvu hu0 hv0 hw0
    have hLHS :
        (-(2 * w * (w ^ 2 + u * v)) * (1 / (2 * s * (manuscriptEta s + w))) +
          -(2 * u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u)))) +
          -(2 * v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v))) =
        (-1 / (2 * s)) * (w * (w ^ 2 + u * v) / (manuscriptEta s + w) +
          (u ^ 2 * (w ^ 2 - v ^ 2) / (manuscriptEta s + u) +
           v ^ 2 * (u ^ 2 - w ^ 2) / (manuscriptEta s + v)) / (v - u)) * 2 := by
      field_simp [hs.ne', hvu, hu0, hv0, hw0]
      ring
    rw [hLHS, hid]
    unfold manuscriptOrderIntegrand
    field_simp [hs.ne', hu0, hv0, hw0]
    ring
  have hcont : ContinuousOn (manuscriptOrderIntegrand u v w) (Set.Icc (1 : ℝ) 2) := by
    intro s hs
    have hspos : 0 < s := by linarith [hs.1]
    have heta : 1 ≤ manuscriptEta s := manuscriptEta_ge_one s hspos
    have hc_eta : ContinuousAt manuscriptEta s := by
      unfold manuscriptEta
      fun_prop (disch := linarith [hspos])
    refine ContinuousAt.continuousWithinAt ?_
    unfold manuscriptOrderIntegrand
    have hden : s * (manuscriptEta s + u) * (manuscriptEta s + v) * (manuscriptEta s + w) ≠ 0 := by
      have hu0 : 0 < manuscriptEta s + u := by linarith [hu_mem.1]
      have hv0 : 0 < manuscriptEta s + v := by linarith [hv_mem.1]
      have hw0 : 0 < manuscriptEta s + w := by linarith [hw_mem.1]
      positivity
    exact ((((((hc_eta.mul_const (w - u)).mul_const (v - w)).mul
      ((hc_eta.mul_const w).sub continuousAt_const))).div
      ((((continuousAt_id.mul (hc_eta.add continuousAt_const)).mul
        (hc_eta.add continuousAt_const)).mul (hc_eta.add continuousAt_const))) hden))
  obtain ⟨s0, hs0_mem, hs0_min⟩ :=
    isCompact_Icc.exists_isMinOn ⟨(1 : ℝ), by norm_num⟩ hcont
  set m : ℝ := manuscriptOrderIntegrand u v w s0
  have hm_pos : 0 < m :=
    manuscriptOrderIntegrand_pos u v w s0 (by linarith [hs0_mem.1]) huw hwu hwv hv
  have hmono1 : ∫ s in Set.Ioc (1 : ℝ) 2, m ≤
      ∫ s in Set.Ioc (1 : ℝ) 2, manuscriptOrderIntegrand u v w s := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
    · exact integrableOn_const (by simp)
    · exact hint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
    · intro s hs
      exact hs0_min ⟨hs.1.le, hs.2⟩
  have hmono2 : ∫ s in Set.Ioc (1 : ℝ) 2, manuscriptOrderIntegrand u v w s ≤
      ∫ s in Set.Ioi (0 : ℝ), manuscriptOrderIntegrand u v w s := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (manuscriptOrderIntegrand_pos u v w s hs huw hwu hwv hv).le
    · exact (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num))).eventuallySubset
  have hm_int : ∫ _ in Set.Ioc (1 : ℝ) 2, m = m := by
    simp [integral_const]; ring
  linarith

/-- Strict inverse ordering on the spherical triangle domain: for `a > b` in
`(0, π)` satisfying the spherical triangle inequalities, `z₁ < z₂`. -/
theorem triangle_gram_inverse_lt
    {a b c : ℝ} (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc0 : 0 < c) (hcpi : c < Real.pi)
    (hba : b < a) (hsum : a + b + c < 2 * Real.pi)
    (hdiff : a - b < c) (htri : c < a + b)
    (hDet : 0 < triangleGramDet (Real.cos a) (Real.cos b) (Real.cos c)) :
    let X := Real.cos a
    let Y := Real.cos b
    let Z := Real.cos c
    let pX := manuscriptPhi X
    let pY := manuscriptPhi Y
    let pZ := manuscriptPhi Z
    triangleGramInverse₁ X Y Z ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2) ((pX + pY - pZ) / 2) <
      triangleGramInverse₂ X Y Z ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2) ((pX + pY - pZ) / 2) := by
  intro X Y Z pX pY pZ
  set p : ℝ := (a + b) / 2
  set q0 : ℝ := (a - b) / 2
  set r : ℝ := c / 2
  set u : ℝ := Real.cos p
  set v : ℝ := Real.cos q0
  set w : ℝ := Real.cos r
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hppi : p < Real.pi := by dsimp [p]; linarith
  have hq0 : 0 < q0 := by dsimp [q0]; linarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hqr : q0 < r := by dsimp [q0, r]; linarith
  have hrp : r < p := by dsimp [p, r]; linarith
  have hrpi : r < Real.pi - p := by dsimp [p, r]; linarith
  have hv1 : v < 1 := by
    dsimp [v]
    simpa [Real.cos_zero] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      ⟨hq0.le, by dsimp [q0]; linarith⟩ hq0
  have hwv : w < v :=
    Real.strictAntiOn_cos ⟨hq0.le, by dsimp [q0]; linarith⟩
      ⟨hr0.le, by dsimp [r]; linarith⟩ hqr
  have huw : u < w :=
    Real.strictAntiOn_cos ⟨hr0.le, by dsimp [r]; linarith⟩ ⟨hp0.le, hppi.le⟩ hrp
  have hwu : -w < u := by
    have hcos_neg : -u = Real.cos (Real.pi - p) := by
      dsimp [u]; rw [Real.cos_pi_sub]
    have hlt := Real.strictAntiOn_cos ⟨hr0.le, by dsimp [r]; linarith⟩
      ⟨by linarith, by linarith⟩ hrpi
    dsimp [w]
    linarith
  have hu_mem : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hv_mem : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hv1⟩
  have hw_mem : w ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hvu : v - u ≠ 0 := by linarith
  have hXltY : X < Y :=
    Real.strictAntiOn_cos ⟨hb0.le, hbpi.le⟩ ⟨ha0.le, hapi.le⟩ hba
  have hYX : Y - X ≠ 0 := sub_ne_zero.mpr hXltY.ne'
  have hJ := triangle_J_eq_four_psi ha0 hapi hb0 hbpi hc0 hcpi hba hsum hdiff
  have hcomb_int :
      w * (w ^ 2 + u * v) * manuscriptPsi w +
        (u ^ 2 * (w ^ 2 - v ^ 2) * manuscriptPsi u +
         v ^ 2 * (u ^ 2 - w ^ 2) * manuscriptPsi v) / (v - u) =
      -(1 / 2 : ℝ) * ∫ s in Set.Ioi (0 : ℝ), manuscriptOrderIntegrand u v w s := by
    rw [manuscriptPsi_eq_eta_integral hw_mem, manuscriptPsi_eq_eta_integral hu_mem,
      manuscriptPsi_eq_eta_integral hv_mem]
    have intw : IntegrableOn
        (fun s => (w * (w ^ 2 + u * v)) * (1 / (2 * s * (manuscriptEta s + w))))
        (Set.Ioi (0 : ℝ)) :=
      (manuscriptPsi_eta_integrableOn hw_mem).const_mul _
    have intu : IntegrableOn
        (fun s => (u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u))))
        (Set.Ioi (0 : ℝ)) :=
      (manuscriptPsi_eta_integrableOn hu_mem).const_mul _
    have intv : IntegrableOn
        (fun s => (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v))))
        (Set.Ioi (0 : ℝ)) :=
      (manuscriptPsi_eta_integrableOn hv_mem).const_mul _
    have hc1 := integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (w * (w ^ 2 + u * v)) (fun s => 1 / (2 * s * (manuscriptEta s + w)))
    have hc2 := integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) (fun s => 1 / (2 * s * (manuscriptEta s + u)))
    have hc3 := integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) (fun s => 1 / (2 * s * (manuscriptEta s + v)))
    simp only [smul_eq_mul] at hc1 hc2 hc3
    have hsplit :
        w * (w ^ 2 + u * v) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + w))) +
          (u ^ 2 * (w ^ 2 - v ^ 2) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + u))) +
           v ^ 2 * (u ^ 2 - w ^ 2) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + v)))) / (v - u) =
        ∫ s in Set.Ioi (0 : ℝ),
          (w * (w ^ 2 + u * v) * (1 / (2 * s * (manuscriptEta s + w))) +
            ((u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u))) +
             (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v))))) := by
      have ha :
          (u ^ 2 * (w ^ 2 - v ^ 2) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + u))) +
           v ^ 2 * (u ^ 2 - w ^ 2) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + v)))) / (v - u) =
          (u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + u))) +
          (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + v))) := by
        ring
      rw [ha, ← hc1, ← hc2, ← hc3]
      have h23 :
          (∫ s in Set.Ioi (0 : ℝ), (u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u)))) +
          (∫ s in Set.Ioi (0 : ℝ), (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v)))) =
          ∫ s in Set.Ioi (0 : ℝ),
            ((u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u))) +
             (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v)))) := by
        simpa [Pi.add_apply] using (integral_add intu intv).symm
      rw [h23]
      simpa [Pi.add_apply] using (integral_add intw (intu.add intv)).symm
    have hsm :
        -(1 / 2 : ℝ) * ∫ s in Set.Ioi (0 : ℝ), manuscriptOrderIntegrand u v w s =
        ∫ s in Set.Ioi (0 : ℝ), -(1 / 2 : ℝ) * manuscriptOrderIntegrand u v w s := by
      simpa [smul_eq_mul] using
        (integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ))) (-(1 / 2 : ℝ))
          (manuscriptOrderIntegrand u v w)).symm
    rw [hsplit, hsm]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    dsimp only
    have heta := manuscriptEta_ge_one s hs
    have hu0 : manuscriptEta s + u ≠ 0 := by linarith [hu_mem.1]
    have hv0 : manuscriptEta s + v ≠ 0 := by linarith [hv_mem.1]
    have hw0 : manuscriptEta s + w ≠ 0 := by linarith [hw_mem.1]
    have hid := triangle_order_integrand_identity (manuscriptEta s) u v w hvu hu0 hv0 hw0
    have hpt :
        w * (w ^ 2 + u * v) * (1 / (2 * s * (manuscriptEta s + w))) +
          ((u ^ 2 * (w ^ 2 - v ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + u))) +
           (v ^ 2 * (u ^ 2 - w ^ 2) / (v - u)) * (1 / (2 * s * (manuscriptEta s + v)))) =
        (1 / (2 * s)) * (w * (w ^ 2 + u * v) / (manuscriptEta s + w) +
          (u ^ 2 * (w ^ 2 - v ^ 2) / (manuscriptEta s + u) +
           v ^ 2 * (u ^ 2 - w ^ 2) / (manuscriptEta s + v)) / (v - u)) := by
      field_simp [hs.ne', hvu, hu0, hv0, hw0]
    rw [hpt, hid]
    unfold manuscriptOrderIntegrand
    field_simp [hs.ne', hu0, hv0, hw0]
    ring
  have hint_pos := manuscriptOrderIntegrand_integral_pos huw hwu hwv hv1
  have hidJ := triangle_inverse_order_J_identity X Y Z pX pY pZ hYX hDet.ne'
  have hRHS_neg :
      2 * triangleGramDet X Y Z *
        (triangleGramInverse₁ X Y Z ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2) ((pX + pY - pZ) / 2) -
         triangleGramInverse₂ X Y Z ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2) ((pX + pY - pZ) / 2)) < 0 := by
    rw [hidJ]
    dsimp [pX, pY, pZ, X, Y, Z]
    rw [hJ, hcomb_int]
    nlinarith [show 0 < Y - X by linarith]
  have hdiff_neg :
      triangleGramInverse₁ X Y Z ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2) ((pX + pY - pZ) / 2) -
        triangleGramInverse₂ X Y Z ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2) ((pX + pY - pZ) / 2) < 0 := by
    by_contra h
    have hn := mul_nonneg (by linarith : 0 ≤ 2 * triangleGramDet X Y Z) (le_of_not_gt h)
    linarith
  linarith

/-- Strict negativity of the isosceles integrand integral. -/
theorem triangle_iso_psi_neg
    {x y : ℝ} (hxlo : -1 < x) (hxhi : x < 1)
    (hylo : -1 < y) (hyhi : y < 1)
    (hxy : y ≤ x) (hquad : 2 * y ^ 2 - 1 < x) :
    2 * (1 + x + 2 * y) * (1 + y) * manuscriptPsi y -
      (3 + x + 4 * y) * (1 + x) * manuscriptPsi x < 0 := by
  have hx_mem : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hxlo, hxhi⟩
  have hy_mem : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hylo, hyhi⟩
  rw [manuscriptPsi_eq_eta_integral hy_mem, manuscriptPsi_eq_eta_integral hx_mem]
  have inty : IntegrableOn
      (fun s => (2 * (1 + x + 2 * y) * (1 + y)) * (1 / (2 * s * (manuscriptEta s + y))))
      (Set.Ioi (0 : ℝ)) :=
    (manuscriptPsi_eta_integrableOn hy_mem).const_mul _
  have intx : IntegrableOn
      (fun s => (-((3 + x + 4 * y) * (1 + x))) * (1 / (2 * s * (manuscriptEta s + x))))
      (Set.Ioi (0 : ℝ)) :=
    (manuscriptPsi_eta_integrableOn hx_mem).const_mul _
  have hrew :
      2 * (1 + x + 2 * y) * (1 + y) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + y))) -
        (3 + x + 4 * y) * (1 + x) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + x))) =
      ∫ s in Set.Ioi (0 : ℝ),
        (1 / (2 * s)) * manuscriptIsoIntegrand x y s := by
    have hcy := integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (2 * (1 + x + 2 * y) * (1 + y)) (fun s => 1 / (2 * s * (manuscriptEta s + y)))
    have hcx := integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (-((3 + x + 4 * y) * (1 + x))) (fun s => 1 / (2 * s * (manuscriptEta s + x)))
    simp only [smul_eq_mul] at hcy hcx
    have hsplit :
        2 * (1 + x + 2 * y) * (1 + y) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + y))) -
          (3 + x + 4 * y) * (1 + x) * (∫ s in Set.Ioi 0, 1 / (2 * s * (manuscriptEta s + x))) =
        ∫ s in Set.Ioi (0 : ℝ),
          ((2 * (1 + x + 2 * y) * (1 + y)) * (1 / (2 * s * (manuscriptEta s + y))) +
           (-((3 + x + 4 * y) * (1 + x))) * (1 / (2 * s * (manuscriptEta s + x)))) := by
      rw [sub_eq_add_neg, neg_mul_eq_neg_mul, ← hcy, ← hcx]
      simpa [Pi.add_apply] using (integral_add inty intx).symm
    rw [hsplit]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    dsimp only
    have heta := manuscriptEta_ge_one s hs
    have hx0 : manuscriptEta s + x ≠ 0 := by linarith
    have hy0 : manuscriptEta s + y ≠ 0 := by linarith
    have hid := triangle_iso_integrand_identity (manuscriptEta s) x y hx0 hy0
    have hid' :
        (2 * (1 + x + 2 * y) * (1 + y)) * (1 / (2 * s * (manuscriptEta s + y))) +
          (-((3 + x + 4 * y) * (1 + x))) * (1 / (2 * s * (manuscriptEta s + x))) =
        (1 / (2 * s)) *
          (2 * (1 + x + 2 * y) * (1 + y) / (manuscriptEta s + y) -
           (3 + x + 4 * y) * (1 + x) / (manuscriptEta s + x)) := by
      field_simp [hs.ne', hx0, hy0]
      ring
    rw [hid', hid]
    rfl
  rw [hrew]
  have hint_total :
      IntegrableOn (fun s : ℝ => (1 / (2 * s)) * manuscriptIsoIntegrand x y s) (Set.Ioi 0) := by
    refine (inty.add intx).congr_fun ?_ measurableSet_Ioi
    intro s hs
    have heta := manuscriptEta_ge_one s hs
    have hx0 : manuscriptEta s + x ≠ 0 := by linarith
    have hy0 : manuscriptEta s + y ≠ 0 := by linarith
    have hid := triangle_iso_integrand_identity (manuscriptEta s) x y hx0 hy0
    dsimp only [Pi.add_apply]
    have hid' :
        (2 * (1 + x + 2 * y) * (1 + y)) * (1 / (2 * s * (manuscriptEta s + y))) +
          (-((3 + x + 4 * y) * (1 + x))) * (1 / (2 * s * (manuscriptEta s + x))) =
        (1 / (2 * s)) *
          (2 * (1 + x + 2 * y) * (1 + y) / (manuscriptEta s + y) -
           (3 + x + 4 * y) * (1 + x) / (manuscriptEta s + x)) := by
      field_simp [hs.ne', hx0, hy0]
      ring
    rw [hid', hid]
    rfl
  have hcont : ContinuousOn (fun s : ℝ => (1 / (2 * s)) * manuscriptIsoIntegrand x y s)
      (Set.Icc (1 : ℝ) 2) := by
    intro s hs
    have hspos : 0 < s := by linarith [hs.1]
    have heta := manuscriptEta_ge_one s hspos
    have hc_eta : ContinuousAt manuscriptEta s := by
      unfold manuscriptEta
      fun_prop (disch := linarith [hspos])
    refine ContinuousAt.continuousWithinAt ?_
    unfold manuscriptIsoIntegrand
    have hx0 : 0 < manuscriptEta s + x := by linarith
    have hy0 : 0 < manuscriptEta s + y := by linarith
    have hden : (manuscriptEta s + x) * (manuscriptEta s + y) ≠ 0 := by positivity
    have hc_s : ContinuousAt (fun t : ℝ => (1 : ℝ) / (2 * t)) s := by
      fun_prop (disch := linarith [hspos])
    have hc_num : ContinuousAt (fun t : ℝ =>
        (manuscriptEta t - 1) * triangleIsoPolynomial x y + (x ^ 2 - 1) * (1 + y)) s :=
      ((hc_eta.sub continuousAt_const).mul_const _).add continuousAt_const
    have hc_den : ContinuousAt (fun t : ℝ => (manuscriptEta t + x) * (manuscriptEta t + y)) s :=
      (hc_eta.add continuousAt_const).mul (hc_eta.add continuousAt_const)
    exact hc_s.mul (hc_num.div hc_den hden)
  obtain ⟨s0, hs0_mem, hs0_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨(1 : ℝ), by norm_num⟩ hcont
  set M : ℝ := (1 / (2 * s0)) * manuscriptIsoIntegrand x y s0
  have hM_neg : M < 0 := by
    have hs0_pos : 0 < s0 := by linarith [hs0_mem.1]
    have hiso := manuscriptIsoIntegrand_neg x y s0 hs0_pos hxlo hxhi hylo hyhi hxy hquad
    exact mul_neg_of_pos_of_neg (by positivity) hiso
  have hmono1 :
      ∫ s in Set.Ioc (1 : ℝ) 2, (1 / (2 * s)) * manuscriptIsoIntegrand x y s ≤
        ∫ s in Set.Ioc (1 : ℝ) 2, M := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
    · exact hint_total.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
    · exact integrableOn_const (by simp)
    · intro s hs
      exact hs0_max ⟨hs.1.le, hs.2⟩
  have hmono2 :
      ∫ s in Set.Ioi (0 : ℝ), (1 / (2 * s)) * manuscriptIsoIntegrand x y s ≤
        ∫ s in Set.Ioc (1 : ℝ) 2, (1 / (2 * s)) * manuscriptIsoIntegrand x y s := by
    have hneg_all :
        0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          fun s => -((1 / (2 * s)) * manuscriptIsoIntegrand x y s) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hpos_s : 0 < 1 / (2 * s) := div_pos zero_lt_one (mul_pos two_pos hs)
      exact neg_nonneg.mpr ((mul_neg_of_pos_of_neg hpos_s
        (manuscriptIsoIntegrand_neg x y s hs hxlo hxhi hylo hyhi hxy hquad)).le)
    have hint_neg : IntegrableOn
        (fun s => -((1 / (2 * s)) * manuscriptIsoIntegrand x y s)) (Set.Ioi (0 : ℝ)) :=
      hint_total.neg
    have hsub_set : Set.Ioc (1 : ℝ) 2 ⊆ Set.Ioi (0 : ℝ) :=
      Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num))
    have hsub := setIntegral_mono_set hint_neg hneg_all hsub_set.eventuallySubset
    simp only [integral_neg] at hsub
    linarith
  have hM_int : ∫ _ in Set.Ioc (1 : ℝ) 2, M = M := by simp [integral_const]; ring
  linarith

/-- Factorization of `1 + 2 cos a cos b cos c - cos² a - cos² b - cos² c`. -/
theorem triangleGramDet_cos_factor (a b c : ℝ) :
    triangleGramDet (Real.cos a) (Real.cos b) (Real.cos c) =
      4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
        Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) := by
  unfold triangleGramDet
  have h1 : 2 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) =
      Real.cos c - Real.cos (a + b) := by
    have hs := Real.cos_sub ((a + b + c) / 2) ((a + b - c) / 2)
    have ha := Real.cos_add ((a + b + c) / 2) ((a + b - c) / 2)
    have harg1 : (a + b + c) / 2 - (a + b - c) / 2 = c := by ring
    have harg2 : (a + b + c) / 2 + (a + b - c) / 2 = a + b := by ring
    rw [harg1] at hs; rw [harg2] at ha; linarith
  have h2 : 2 * Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) =
      Real.cos (a - b) - Real.cos c := by
    have hs := Real.cos_sub ((a + c - b) / 2) ((b + c - a) / 2)
    have ha := Real.cos_add ((a + c - b) / 2) ((b + c - a) / 2)
    have harg1 : (a + c - b) / 2 - (b + c - a) / 2 = a - b := by ring
    have harg2 : (a + c - b) / 2 + (b + c - a) / 2 = c := by ring
    rw [harg1] at hs; rw [harg2] at ha; linarith
  have hprod :
      4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
        Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) =
      (Real.cos c - Real.cos (a + b)) * (Real.cos (a - b) - Real.cos c) := by
    linarith [mul_assoc (2 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2))
      (2 * Real.sin ((a + c - b) / 2)) (Real.sin ((b + c - a) / 2)),
      congrArg₂ (· * ·) h1 h2]
  rw [hprod, Real.cos_add, Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

/-- Equivalence between positive spherical Gram determinant and the spherical
triangle inequalities for side lengths in `(0, π)`. -/
theorem triangleGramDet_cos_pos_iff
    {a b c : ℝ} (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hc0 : 0 < c) (hcpi : c < Real.pi) :
    0 < triangleGramDet (Real.cos a) (Real.cos b) (Real.cos c) ↔
      a < b + c ∧ b < a + c ∧ c < a + b ∧ a + b + c < 2 * Real.pi := by
  rw [triangleGramDet_cos_factor]
  constructor
  · intro hpos
    have hsum_pos : 0 < (a + b + c) / 2 := by linarith
    have hsum_lt : (a + b + c) / 2 < 2 * Real.pi := by linarith
    have hp1 : (a + b - c) / 2 < Real.pi := by linarith
    have hp2 : (a + c - b) / 2 < Real.pi := by linarith
    have hp3 : (b + c - a) / 2 < Real.pi := by linarith
    have hn1 : -Real.pi < (a + b - c) / 2 := by linarith
    have hn2 : -Real.pi < (a + c - b) / 2 := by linarith
    have hn3 : -Real.pi < (b + c - a) / 2 := by linarith
    have neg_count :
        ∀ (hs1 : Real.sin ((a + b + c) / 2) ≤ 0), False := by
      intro hs1
      have hge : Real.pi ≤ (a + b + c) / 2 := by
        by_contra hlt
        have := Real.sin_pos_of_pos_of_lt_pi hsum_pos (lt_of_not_ge hlt)
        linarith
      have hc1 : 0 < (a + b - c) / 2 := by linarith
      have hc2 : 0 < (a + c - b) / 2 := by linarith
      have hc3 : 0 < (b + c - a) / 2 := by linarith
      have s1 := Real.sin_pos_of_pos_of_lt_pi hc1 hp1
      have s2 := Real.sin_pos_of_pos_of_lt_pi hc2 hp2
      have s3 := Real.sin_pos_of_pos_of_lt_pi hc3 hp3
      have hnonpos :
          4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) ≤ 0 := by
        rw [show 4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) =
            Real.sin ((a + b + c) / 2) * (4 * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2)) by ring]
        exact mul_nonpos_of_nonpos_of_nonneg hs1 (by positivity)
      linarith
    have hsum_pi : (a + b + c) / 2 < Real.pi := by
      by_contra hge
      have hle := le_of_not_gt hge
      have hsin_le : Real.sin ((a + b + c) / 2) ≤ 0 := by
        have hpos_sub := Real.sin_nonneg_of_nonneg_of_le_pi (x := (a + b + c) / 2 - Real.pi)
          (by linarith) (by linarith)
        have hsin_eq := Real.sin_add_pi ((a + b + c) / 2 - Real.pi)
        have harg : (a + b + c) / 2 - Real.pi + Real.pi = (a + b + c) / 2 := by ring
        rw [harg] at hsin_eq
        linarith
      exact neg_count hsin_le
    have hs0 : 0 < Real.sin ((a + b + c) / 2) := Real.sin_pos_of_pos_of_lt_pi hsum_pos hsum_pi
    have sin_neg_of_nonpos : ∀ x ∈ Set.Icc (-Real.pi) 0, Real.sin x ≤ 0 := by
      intro x hx
      have hpos_neg := Real.sin_nonneg_of_nonneg_of_le_pi (x := -x)
        (by linarith [hx.2]) (by linarith [hx.1])
      rw [← neg_neg x, Real.sin_neg]
      linarith
    have hbc_a : a < b + c := by
      by_contra hle
      have h1 : (b + c - a) / 2 ≤ 0 := by linarith
      have h2 : 0 < (a + b - c) / 2 := by linarith
      have h3 : 0 < (a + c - b) / 2 := by linarith
      have s_bc := sin_neg_of_nonpos ((b + c - a) / 2) ⟨hn3.le, h1⟩
      have s_ab := Real.sin_pos_of_pos_of_lt_pi h2 hp1
      have s_ac := Real.sin_pos_of_pos_of_lt_pi h3 hp2
      have hnonpos :
          4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) ≤ 0 := by
        rw [show 4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) =
            (4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2)) * Real.sin ((b + c - a) / 2) by ring]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) s_bc
      linarith
    have hac_b : b < a + c := by
      by_contra hle
      have h1 : (a + c - b) / 2 ≤ 0 := by linarith
      have h2 : 0 < (a + b - c) / 2 := by linarith
      have h3 : 0 < (b + c - a) / 2 := by linarith
      have s_ac := sin_neg_of_nonpos ((a + c - b) / 2) ⟨hn2.le, h1⟩
      have s_ab := Real.sin_pos_of_pos_of_lt_pi h2 hp1
      have s_bc := Real.sin_pos_of_pos_of_lt_pi h3 hp3
      have hnonpos :
          4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) ≤ 0 := by
        rw [show 4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) =
            (4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((b + c - a) / 2)) * Real.sin ((a + c - b) / 2) by ring]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) s_ac
      linarith
    have hab_c : c < a + b := by
      by_contra hle
      have h1 : (a + b - c) / 2 ≤ 0 := by linarith
      have h2 : 0 < (a + c - b) / 2 := by linarith
      have h3 : 0 < (b + c - a) / 2 := by linarith
      have s_ab := sin_neg_of_nonpos ((a + b - c) / 2) ⟨hn1.le, h1⟩
      have s_ac := Real.sin_pos_of_pos_of_lt_pi h2 hp2
      have s_bc := Real.sin_pos_of_pos_of_lt_pi h3 hp3
      have hnonpos :
          4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) ≤ 0 := by
        rw [show 4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + b - c) / 2) *
            Real.sin ((a + c - b) / 2) * Real.sin ((b + c - a) / 2) =
            (4 * Real.sin ((a + b + c) / 2) * Real.sin ((a + c - b) / 2) *
            Real.sin ((b + c - a) / 2)) * Real.sin ((a + b - c) / 2) by ring]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) s_ab
      linarith
    exact ⟨hbc_a, hac_b, hab_c, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have s0 : 0 < Real.sin ((a + b + c) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have s1 : 0 < Real.sin ((a + b - c) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have s2 : 0 < Real.sin ((a + c - b) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have s3 : 0 < Real.sin ((b + c - a) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    positivity

end Sphere3
