module

public import Mathlib

@[expose] public section

/-!
# Polynomial certificate for the regular dual-height differential

For a regular dual Gram matrix `H=(1-t) I+t J`, write
  `H^-1=p I+q J` and let `a^2=p+q` with `a>0`.
A symmetric zero-diagonal Gram perturbation `X` has incident row
sum `si` and total edge sum `S`.

Differentiation of the inverse and square root predicts

  a * dh_i = a^2 * si
    - (1-t)*(p*q*si+q^2*S) - t*(2*p*q+4*q^2)*S.

The theorem below is the polynomial identity yielding

  dh_i = (p/a) * si + (t^2*p^2/((1+3*t)*a)) * S.

This file proves only the rational/algebraic part. The derivative
of matrix inversion and square root is a separate analytic step.
-/

namespace Sphere3

/-- Polynomial identity governing the first-order variation of each
normal-dual-axis height at the regular Gram family. -/
theorem regular_height_linearization_polynomial
    (t p q a si S : ℝ)
    (hp : (1 - t) * p = 1)
    (hq : (1 + 3 * t) * q = -t * p)
    (ha : a ^ 2 = p + q) :
    (1 + 3 * t) *
      (a ^ 2 * si - (1 - t) * (p * q * si + q ^ 2 * S) -
        t * (2 * p * q + 4 * q ^ 2) * S) =
      (1 + 3 * t) * p * si + t ^ 2 * p ^ 2 * S := by
  have hcoefficient : a ^ 2 - (1 - t) * p * q = p := by
    calc
      a ^ 2 - (1 - t) * p * q = p + q - 1 * q := by
        rw [ha, hp]
      _ = p := by ring
  have htotal :
      (1 + 3 * t) * ((1 - t) * q ^ 2 +
          t * (2 * p * q + 4 * q ^ 2)) = -t ^ 2 * p ^ 2 := by
    calc
      (1 + 3 * t) * ((1 - t) * q ^ 2 +
          t * (2 * p * q + 4 * q ^ 2)) =
          ((1 + 3 * t) * q) ^ 2 +
            2 * t * p * ((1 + 3 * t) * q) := by ring
      _ = (-t * p) ^ 2 + 2 * t * p * (-t * p) := by rw [hq]
      _ = -t ^ 2 * p ^ 2 := by ring
  calc
    (1 + 3 * t) *
        (a ^ 2 * si - (1 - t) * (p * q * si + q ^ 2 * S) -
          t * (2 * p * q + 4 * q ^ 2) * S) =
        (1 + 3 * t) * (a ^ 2 - (1 - t) * p * q) * si -
          ((1 + 3 * t) * ((1 - t) * q ^ 2 +
            t * (2 * p * q + 4 * q ^ 2))) * S := by ring
    _ = (1 + 3 * t) * p * si + t ^ 2 * p ^ 2 * S := by
      rw [hcoefficient, htotal]
      ring

end Sphere3
