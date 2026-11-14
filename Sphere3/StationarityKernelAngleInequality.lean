module

public import Mathlib

@[expose] public section

/-!
# The strict angular inequality in the stationary regular Gram family

For `0 < theta < pi`:
  theta * (1 + cos theta) < 2 * sin theta.
This is a double-angle reformulation of `theta/2 < tan(theta/2)`.

Consequently, for `-1/3 < t < 1` and `theta = arccos t`, we have
  t*(t+2)*theta < (1+2*t)*sin theta.

After substituting the formula for the derivative of `stationaryKernel`,
this becomes `K(t) > (1+2*t)*K'(t)` and hence `2*a>b` for the linearized
stationarity equations. These trigonometric bounds support the linearized stationarity analysis.
-/

namespace Sphere3

/-- A strengthened form of the elementary bound `sin θ < θ`, valid on
`(0, π)` and derived from `u < tan u` for `u=θ/2`. -/
theorem angle_mul_one_add_cos_lt_two_sin
    (θ : ℝ) (hθ : 0 < θ) (hπ : θ < Real.pi) :
    θ * (1 + Real.cos θ) < 2 * Real.sin θ := by
  have hu : 0 < θ / 2 := by linarith
  have huπ : θ / 2 < Real.pi / 2 := by linarith
  have hcos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, huπ⟩
  have ht := Real.lt_tan hu huπ
  have hbase : (θ / 2) * Real.cos (θ / 2) < Real.sin (θ / 2) := by
    have hm := mul_lt_mul_of_pos_right ht hcos
    rw [Real.tan_mul_cos (ne_of_gt hcos)] at hm
    exact hm
  have hmult :
      ((θ / 2) * Real.cos (θ / 2)) * (4 * Real.cos (θ / 2)) <
        Real.sin (θ / 2) * (4 * Real.cos (θ / 2)) :=
    mul_lt_mul_of_pos_right hbase (by positivity)
  have hsin : Real.sin θ =
      2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    convert Real.sin_two_mul (θ / 2) using 1 <;> ring
  have hcos2 : Real.cos θ =
      2 * Real.cos (θ / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (θ / 2) using 1 <;> ring
  rw [hsin, hcos2]
  have h1 : θ * (1 + (2 * Real.cos (θ / 2) ^ 2 - 1)) =
      (θ / 2 * Real.cos (θ / 2)) * (4 * Real.cos (θ / 2)) := by ring
  have h2 : 2 * (2 * Real.sin (θ / 2) * Real.cos (θ / 2)) =
      Real.sin (θ / 2) * (4 * Real.cos (θ / 2)) := by ring
  linarith [hmult, h1, h2]

private theorem angular_kernel_nonresonance_of_nonneg
    (t θ s : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) (hs : 0 < s)
    (htrig : θ * (1+t) < 2*s) :
    t * (t+2) * θ < (1+2*t)*s := by
  have hr : 0 ≤ t * (t+2) :=
    mul_nonneg ht (by linarith)
  have hprod : t * (t+2) * (θ * (1+t)) ≤ t * (t+2) * (2*s) :=
    mul_le_mul_of_nonneg_left (le_of_lt htrig) hr
  have hgap : 0 < (1-t)*s := mul_pos (by linarith) hs
  have ht1pos : 0 < 1+t := by linarith
  have hbridge :
      0 < (1+t)*((1+2*t)*s-t*(t+2)*θ) := by
    nlinarith only [hprod, hgap]
  have hdelta : 0 < (1+2*t)*s-t*(t+2)*θ := by
    by_contra h
    have hnonpos : (1+2*t)*s-t*(t+2)*θ ≤ 0 := le_of_not_gt h
    have hcontra := mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt ht1pos) hnonpos
    linarith
  linarith

/-- The nonresonance inequality on the precise Gram parameter interval.
For nonnegative parameters use `tan(θ/2) > θ/2`; for negative parameters
the right-hand side `t*(t+2)*θ` is negative. -/
theorem regular_kernel_angle_nonresonance
    (t θ : ℝ) (ht : -(1/3 : ℝ) < t) (ht1 : t < 1)
    (hθ : 0 < θ) (hπ : θ < Real.pi)
    (hcos : Real.cos θ = t) :
    t * (t+2)*θ < (1+2*t)*Real.sin θ := by
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ hπ
  by_cases hnonneg : 0 ≤ t
  · apply angular_kernel_nonresonance_of_nonneg t θ (Real.sin θ)
        hnonneg ht1 hsinpos
    have htrig := angle_mul_one_add_cos_lt_two_sin θ hθ hπ
    rwa [hcos] at htrig
  · have htneg : t < 0 := lt_of_not_ge hnonneg
    have hp : 0 < t+2 := by linarith
    have hleft : t * (t+2)*θ < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos htneg hp) hθ
    have hright : 0 < (1+2*t)*Real.sin θ :=
      mul_pos (by linarith) hsinpos
    linarith

end Sphere3
