module

public import SphericalTetrahedron.StationaryKernelCurvature
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
# Strict concavity of the stationary angular kernel

The derivative expression is
   F(x)=(arccos x-sqrt(1-x^2))/((1-x)*sqrt(1-x^2)).
The preceding modules proved analytically the strict sign of
   F'(x)=[(1+2x) arccos x-(2+x)sqrt(1-x^2)]/((1-x)*s^3) < 0
on (-1,1).  This module differentiates F, proves it strictly
antitone, identifies F with the derivative of `stationaryKernel`,
and applies Mathlib's strict-concavity lemma.
-/

noncomputable section

namespace SphericalTetrahedron

def stationaryKernelFirstDerivative (x : ℝ) : ℝ :=
  (Real.arccos x - Real.sqrt (1 - x ^ 2)) /
    ((1 - x) * Real.sqrt (1 - x ^ 2))

def stationaryKernelSecondDerivative (x : ℝ) : ℝ :=
  ((1 + 2 * x) * Real.arccos x -
      (2 + x) * Real.sqrt (1 - x ^ 2)) /
    ((1 - x) * (Real.sqrt (1 - x ^ 2)) ^ 3)

private theorem stationaryKernelFirstDerivative_hasDerivAt
    (x : ℝ) (hx : -1 < x ∧ x < 1) :
    HasDerivAt stationaryKernelFirstDerivative
      (stationaryKernelSecondDerivative x) x := by
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith [hx.2])
      (show 0 < 1 + x by linarith [hx.1])]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hrad
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 := hs.ne'
  have hx1 : x ≠ -1 := by linarith [hx.1]
  have hx2 : x ≠ 1 := by linarith [hx.2]
  have hxm : 1 - x ≠ 0 := by linarith [hx.2]
  have hden : (1 - x) * Real.sqrt (1 - x ^ 2) ≠ 0 :=
    mul_ne_zero hxm hs0
  have hpoly : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    norm_num
  have hroot := hpoly.sqrt hrad.ne'
  have hnum := (Real.hasDerivAt_arccos hx1 hx2).sub hroot
  have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_id x).const_sub 1 using 1
    funext y; simp
  have hdenDeriv := hlin.mul hroot
  have hquot := hnum.div hdenDeriv hden
  have hsquared : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hrad.le
  have halgebra := Sphere3.stationary_kernel_second_derivative_algebra
    x (Real.arccos x) (Real.sqrt (1 - x ^ 2)) hsquared hs0 hxm
  dsimp only [stationaryKernelFirstDerivative,
    stationaryKernelSecondDerivative]
  convert hquot using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.sub_apply, neg_mul, one_mul]
    exact Eq.trans halgebra.symm (by ring)

/-- The displayed first-derivative expression is strictly decreasing on
all geometrically feasible dual scalar products. -/
theorem stationaryKernel_firstDerivative_strictAnti :
    StrictAntiOn stationaryKernelFirstDerivative (Set.Ioo (-1 : ℝ) 1) := by
  let D : Set ℝ := Set.Ioo (-1) 1
  have hD : Convex ℝ D := convex_Ioo (-1) 1
  have hopen : interior D = D := isOpen_Ioo.interior_eq
  have hcont : ContinuousOn stationaryKernelFirstDerivative D := by
    intro x hx
    exact (stationaryKernelFirstDerivative_hasDerivAt x hx).continuousAt.continuousWithinAt
  have hder : ∀ x ∈ interior D,
      HasDerivWithinAt stationaryKernelFirstDerivative
        (stationaryKernelSecondDerivative x) (interior D) x := by
    intro x hx
    rw [hopen] at hx
    exact (stationaryKernelFirstDerivative_hasDerivAt x hx).hasDerivWithinAt
  have hneg : ∀ x ∈ interior D,
      stationaryKernelSecondDerivative x < 0 := by
    intro x hx
    rw [hopen] at hx
    exact stationaryKernel_second_derivative_expression_neg x hx
  exact strictAntiOn_of_hasDerivWithinAt_neg hD hcont hder hneg

/-- Strict concavity of `stationaryKernel` on `(-1, 1)`. -/
theorem stationaryKernel_strictConcaveOn :
    StrictConcaveOn ℝ (Set.Ioo (-1 : ℝ) 1) stationaryKernel := by
  let D : Set ℝ := Set.Ioo (-1) 1
  have hD : Convex ℝ D := convex_Ioo (-1) 1
  have hopen : interior D = D := isOpen_Ioo.interior_eq
  have hcont : ContinuousOn stationaryKernel D := by
    intro x hx
    exact (stationaryKernel_hasDerivAt x hx).continuousAt.continuousWithinAt
  have hderAnti : StrictAntiOn (deriv stationaryKernel) D := by
    intro x hx y hy hxy
    have hlt := stationaryKernel_firstDerivative_strictAnti hx hy hxy
    have hdx := (stationaryKernel_hasDerivAt x hx).deriv
    have hdy := (stationaryKernel_hasDerivAt y hy).deriv
    rw [hdx, hdy]
    exact hlt
  apply StrictAntiOn.strictConcaveOn_of_deriv hD hcont
  rwa [hopen]

end SphericalTetrahedron
