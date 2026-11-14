module

public import SphericalTetrahedron.DualAngleBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Strict positivity of the derivative certificate for the edge kernel

For -1 < x < 1, let

  K(x) = (1+x) * arccos(x) / sqrt(1-x^2).

A direct calculus computation gives

  K'(x) = (arccos(x) - sqrt(1-x^2)) /
             ((1-x) * sqrt(1-x^2)).

The two lemmas below prove the numerator and the displayed quotient
strictly positive; the derivative identity and strict monotonicity are
completed in `StationaryKernelDerivative`.
-/

noncomputable section

namespace SphericalTetrahedron

/-- The angular gap is strictly positive on the open unit interval. -/
theorem arccos_gt_sqrt_of_mem (x : Real)
    (hx : -1 < x ∧ x < 1) :
    Real.sqrt (1 - x ^ 2) < Real.arccos x := by
  have htheta : 0 < Real.arccos x :=
    Real.arccos_pos.mpr hx.2
  have hsin : Real.sin (Real.arccos x) < Real.arccos x :=
    Real.sin_lt htheta
  simpa only [Real.sin_arccos] using hsin

/-- The exact real expression obtained after differentiating the
stationarity kernel has positive sign at every feasible edge angle. -/
theorem stationaryKernel_derivative_certificate_pos (x : Real)
    (hx : -1 < x ∧ x < 1) :
    0 < (Real.arccos x - Real.sqrt (1 - x ^ 2)) /
      ((1 - x) * Real.sqrt (1 - x ^ 2)) := by
  have hradicand : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith [hx.2])
      (show 0 < 1 + x by linarith [hx.1])]
  have hroot : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.2 hradicand
  have hden : 0 < (1 - x) * Real.sqrt (1 - x ^ 2) :=
    mul_pos (by linarith [hx.2]) hroot
  exact div_pos (sub_pos.mpr (arccos_gt_sqrt_of_mem x hx)) hden

end SphericalTetrahedron
