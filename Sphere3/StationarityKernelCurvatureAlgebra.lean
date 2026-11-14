module

public import Mathlib

@[expose] public section

/-!
# Polynomial certificates for curvature of the stationarity kernel

Let s = sqrt(1-x²), θ = arccos x, and
Q = (2+x)s - (1+2x)θ. The exact algebraic cancellation in the
first derivative of Q gives Q' = 2(s-θ). The stationarity kernel K
has second derivative K'' = -Q / ((1-x)*s³). Hence Q>0 means K''<0.

This module contains just the field identities and sign implication:
no transcendental inequalities are assumed silently.
-/

namespace Sphere3

/-- The derivative of the curvature gap simplifies to `2*(s-theta)`.
This is an algebraic identity under the square-root relation. -/
theorem stationary_curvature_gap_derivative_algebra
    (x theta s : ℝ) (hs : s ^ 2 = 1 - x ^ 2) (hs0 : s ≠ 0) :
    (s + (2 + x) * ((-2 * x) / (2 * s))) -
      (2 * theta + (1 + 2 * x) * (-(1 / s))) =
      2 * (s - theta) := by
  field_simp [hs0]
  nlinarith [hs]

/-- Exact rational simplification of the formal derivative of K'. -/
theorem stationary_kernel_second_derivative_algebra
    (x theta s : ℝ) (hs : s ^ 2 = 1 - x ^ 2)
    (hs0 : s ≠ 0) (hxm : 1 - x ≠ 0) :
    ((((-1 / s) - ((-2 * x) / (2 * s))) * ((1 - x) * s)) -
      ((theta - s) * (-s + (1 - x) * ((-2 * x) / (2 * s))))) /
        (((1 - x) * s) ^ 2) =
      ((1 + 2 * x) * theta - (2 + x) * s) /
        ((1 - x) * s ^ 3) := by
  field_simp [hs0, hxm]
  simp only [show s ^ 4 = (s ^ 2) ^ 2 by ring, show s ^ 3 = s * s ^ 2 by ring, hs]
  ring

/-- If the curvature gap is positive, the exact second-derivative
expression is negative. -/
theorem stationary_kernel_second_derivative_certificate_neg
    (x theta s : ℝ) (hx : x < 1) (hs : 0 < s)
    (hgap : (1 + 2 * x) * theta < (2 + x) * s) :
    ((1 + 2 * x) * theta - (2 + x) * s) /
      ((1 - x) * s ^ 3) < 0 := by
  apply div_neg_of_neg_of_pos
  · linarith
  · exact mul_pos (by linarith) (pow_pos hs 3)

end Sphere3
