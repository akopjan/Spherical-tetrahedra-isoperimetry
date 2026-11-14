module

public import Sphere3.ManuscriptBoundaryGram

@[expose] public section

/-!
# Exact algebra used in the square-suspension boundary perturbation

These are the polynomial and rational simplifications needed to obtain
`∂δ A(a,δ) = 4δ / ((1+b) Δ)`, where `b=2a-1+δ` and
`Δ²=(1-b)(1+b-2a²)`. The analytic differentiation and perturbation steps are proved separately in
`SphericalTetrahedron.ManuscriptBoundaryPerturbation`.
-/

noncomputable section

namespace Sphere3

/-- Polar-face Gram determinant for side cosines `a,a,b`. -/
def squareSuspensionPolarDet (a b : ℝ) : ℝ :=
  1 + 2 * a ^ 2 * b - 2 * a ^ 2 - b ^ 2

/-- Factorization gives the easy positivity region for the polar face. -/
theorem squareSuspensionPolarDet_factor (a b : ℝ) :
    squareSuspensionPolarDet a b =
      (1 - b) * (1 + b - 2 * a ^ 2) := by
  unfold squareSuspensionPolarDet
  ring

/-- The expression in the arctangent denominator simplifies exactly. -/
theorem squareSuspensionPolarDenominator (a b : ℝ) :
    (1 + 2 * a + b) ^ 2 + squareSuspensionPolarDet a b =
      2 * (1 + a) ^ 2 * (1 + b) := by
  unfold squareSuspensionPolarDet
  ring

/-- Exact numerator identity behind the area derivative formula. -/
theorem squareSuspensionAreaDerivative_polynomial (a b : ℝ) :
    -8 * ((a ^ 2 - b) * (1 + 2 * a + b) -
       squareSuspensionPolarDet a b) * (1 + b) =
      4 * (1 + b - 2 * a) *
        ((1 + 2 * a + b) ^ 2 + squareSuspensionPolarDet a b) := by
  unfold squareSuspensionPolarDet
  ring

/-- Differential-algebra certificate, with square root represented by `s`.
The hypotheses are exactly the nonzero denominators of the formulas. -/
theorem squareSuspensionAreaDerivative_rational
    (a b s : ℝ)
    (hsq : s ^ 2 = squareSuspensionPolarDet a b)
    (hs : s ≠ 0) (hb : 1 + b ≠ 0)
    (hden : (1 + 2 * a + b) ^ 2 + s ^ 2 ≠ 0) :
    -8 * ((a ^ 2 - b) * (1 + 2 * a + b) - s ^ 2) /
        (s * ((1 + 2 * a + b) ^ 2 + s ^ 2)) =
      4 * (1 + b - 2 * a) / ((1 + b) * s) := by
  have hpoly := squareSuspensionAreaDerivative_polynomial a b
  rw [← hsq] at hpoly
  field_simp [hs, hb, hden]
  nlinarith [hpoly]

/-- The alternating two-eigenvalue ratio yields the edge cosine formula
`cos(ℓ_b) = 1 - 4 / (m*S)` from the manuscript. -/
theorem squareSuspensionEdgeCosine_rational
    (lambda delta m : ℝ)
    (hlambda : lambda ≠ 0) (hdelta : delta ≠ 0) (hm : m ≠ 0)
    (hS : 1 / lambda + 1 / delta + 2 / m ≠ 0) :
    (1 / lambda + 1 / delta - 2 / m) /
      (1 / lambda + 1 / delta + 2 / m) =
      1 - 4 / (m * (1 / lambda + 1 / delta + 2 / m)) := by
  set S : ℝ := 1 / lambda + 1 / delta + 2 / m
  have h1 : 1 / lambda + 1 / delta - 2 / m = S - 4 / m := by
    dsimp [S]
    ring
  rw [h1]
  field_simp [hm, hS]

end Sphere3

namespace Sphere3

/-- The polar-face Gram determinant stays strictly positive during the
nondegenerate square-suspension perturbation. -/
theorem squareSuspensionPolarDet_pos
    (a d : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hd : 0 < d) (hupper : d < 2 * (1 - a)) :
    0 < squareSuspensionPolarDet a (2 * a - 1 + d) := by
  rw [squareSuspensionPolarDet_factor]
  have hfirst : 0 < 1 - (2 * a - 1 + d) := by linarith
  have hother : 0 < 1 + (2 * a - 1 + d) - 2 * a ^ 2 := by
    have hprod : 0 < a * (1 - a) :=
      mul_pos ha (by linarith)
    nlinarith
  exact mul_pos hfirst hother

/-- The exact area-variation expression from the manuscript has
strictly positive sign. Obtaining this expression as a derivative is a
separate analytic step, not an assumption hidden here. -/
theorem squareSuspensionAreaSlope_pos
    (a d : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hd : 0 < d) (hupper : d < 2 * (1 - a)) :
    0 < 4 * d / ((2 * a + d) *
      Real.sqrt (squareSuspensionPolarDet a (2 * a - 1 + d))) := by
  have hDet := squareSuspensionPolarDet_pos a d ha ha1 hd hupper
  have hden : 0 < 2 * a + d := by linarith
  exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hd)
    (mul_pos hden (Real.sqrt_pos.2 hDet))

end Sphere3

namespace Sphere3

/-- The positive cubic term in the square-root parameter `s=√δ`
dominates a quartic error for all sufficiently small `s>0`.
This is the elementary inequality behind the fixed-area boundary
improvement, before obtaining the analytic expansion coefficients. -/
theorem positive_cubic_dominates_quartic
    (alpha C : ℝ) (ha : 0 < alpha) (hC : 0 ≤ C) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ s : ℝ, 0 < s → s < epsilon →
        C * s ^ 4 < alpha * s ^ 3 := by
  let epsilon : ℝ := alpha / (C + 1)
  have hC1 : 0 < C + 1 := by linarith
  have heps : 0 < epsilon := div_pos ha hC1
  refine ⟨epsilon, heps, ?_⟩
  intro s hs hseps
  have hbound : s * (C + 1) < alpha := by
    apply (lt_div_iff₀ hC1).mp
    exact hseps
  have hmain : C * s < alpha := by
    nlinarith
  have hpower : 0 < s ^ 3 := pow_pos hs _
  have hscaled := mul_lt_mul_of_pos_right hmain hpower
  nlinarith [hscaled]

/-- A cubic leading gain proves positivity despite a controlled quartic
error. All analytic work is explicit in `hLower`, not hidden. -/
theorem positive_gain_from_cubic_quartic_bounds
    (alpha C s gain : ℝ) (ha : 0 < alpha) (hC : 0 ≤ C)
    (hs : 0 < s) (hsmall : s < alpha / (C + 1))
    (hLower : alpha * s ^ 3 - C * s ^ 4 ≤ gain) :
    0 < gain := by
  have hC1 : 0 < C + 1 := by linarith
  have hbound : s * (C + 1) < alpha :=
    (lt_div_iff₀ hC1).mp hsmall
  have hmain : C * s < alpha := by nlinarith
  have hpower : 0 < s ^ 3 := pow_pos hs _
  have hscaled := mul_lt_mul_of_pos_right hmain hpower
  nlinarith [hscaled, hLower]

end Sphere3
