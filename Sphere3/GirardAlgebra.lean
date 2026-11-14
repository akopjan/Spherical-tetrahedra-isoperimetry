module

public import Mathlib

@[expose] public section

/-!
# Algebraic conclusion of the rotation-invariant Girard counting argument

Let M denote the finite measure of the full unit two-sphere under an
arbitrary isometry-invariant two-dimensional Borel measure. Suppose a
spherical triangle with angles a,b,c has measure A. If a lune of angle
q has measure M*q/(2*pi), the six-lune multiplicity identity reads

  2*(M*a/(2*pi) + M*b/(2*pi) + M*c/(2*pi)) = M + 4*A.

This algebra forces A = M/(4*pi)*(a+b+c-pi), with no assertion
that the raw Hausdorff normalization makes M=4*pi.

Only the elementary real-algebra step is supplied here.
-/

noncomputable section

namespace Sphere3

/-- Girard's spherical excess identity from the six-lune count. -/
theorem girard_algebra_of_lune_count
    (M A a b c : Real)
    (hcount :
      2 * (M * a / (2 * Real.pi) + M * b / (2 * Real.pi) +
           M * c / (2 * Real.pi)) = M + 4 * A) :
    A = (M / (4 * Real.pi)) * (a + b + c - Real.pi) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hcount ⊢
  nlinarith [hcount]

/-- The natural common scalar is strictly positive if the full sphere
has strictly positive finite Hausdorff measure. -/
theorem girard_scalar_pos (M : Real) (hM : 0 < M) :
    0 < M / (4 * Real.pi) := by
  exact div_pos hM (by positivity)

end Sphere3
