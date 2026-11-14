module

public import SphericalTetrahedron.StationaryKernelDerivative
public import Sphere3.StationarityKernelCurvatureAlgebra
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Curvature of the stationary edge kernel

The angular kernel is not merely increasing: it is strictly concave.
The key positive numerator in -K'' is
Q(x)=(2+x) sqrt(1-x²)-(1+2x) arccos x.
It has derivative Q'(x)=2(sqrt(1-x²)-arccos x)<0 on (-1,1),
is continuous at 1, and Q(1)=0. Consequently Q(x)>0.
This module proves the gap inequality and records negativity of the exact
second-derivative expression; `StrictConcaveOn` is derived in
`StationaryKernelStrictConcavity`.
-/

noncomputable section

namespace SphericalTetrahedron

private def kernelCurvatureGap (x : ℝ) : ℝ :=
  (2 + x) * Real.sqrt (1 - x ^ 2) - (1 + 2 * x) * Real.arccos x

private theorem kernelCurvatureGap_hasDerivAt (x : ℝ)
    (hx : -1 < x ∧ x < 1) :
    HasDerivAt kernelCurvatureGap
      (2 * (Real.sqrt (1 - x ^ 2) - Real.arccos x)) x := by
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith [hx.2])
      (show 0 < 1 + x by linarith [hx.1])]
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hrad).ne'
  have hx1 : x ≠ -1 := by linarith [hx.1]
  have hx2 : x ≠ 1 := by linarith [hx.2]
  have hpoly : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    norm_num
  have hroot := hpoly.sqrt hrad.ne'
  have hlin1 : HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
    (hasDerivAt_id x).const_add 2
  have hlin2 : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 x := by
    convert ((hasDerivAt_id x).const_mul 2).const_add 1 using 1
    · funext y; simp
    · ring
  have hfirst := hlin1.mul hroot
  have hsecond := hlin2.mul (Real.hasDerivAt_arccos hx1 hx2)
  have hdiff := hfirst.sub hsecond
  have hsquared : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hrad.le
  have halgebra := Sphere3.stationary_curvature_gap_derivative_algebra
    x (Real.arccos x) (Real.sqrt (1 - x ^ 2)) hsquared hs0
  convert hdiff using 1
  · rfl
  · simp only [one_mul]
    exact halgebra.symm

/-- The crucial strict inequality needed for global concavity of K.
It holds on the *entire* admissible inner-product interval, including
negative values near -1. -/
theorem stationaryKernel_curvature_gap_pos (x : ℝ)
    (hx : -1 < x ∧ x < 1) :
    (1 + 2 * x) * Real.arccos x <
      (2 + x) * Real.sqrt (1 - x ^ 2) := by
  let D : Set ℝ := Set.Icc (-1) 1
  have hD : Convex ℝ D := convex_Icc (-1) 1
  have hcont : ContinuousOn kernelCurvatureGap D := by
    have hc : Continuous kernelCurvatureGap := by
      unfold kernelCurvatureGap
      fun_prop
    exact hc.continuousOn
  have hint : interior D = Set.Ioo (-1) 1 := by
    simp [D, interior_Icc]
  have hder : ∀ y ∈ interior D,
      HasDerivWithinAt kernelCurvatureGap
        (2 * (Real.sqrt (1 - y ^ 2) - Real.arccos y))
        (interior D) y := by
    intro y hy
    rw [hint] at hy
    exact (kernelCurvatureGap_hasDerivAt y hy).hasDerivWithinAt
  have hneg : ∀ y ∈ interior D,
      2 * (Real.sqrt (1 - y ^ 2) - Real.arccos y) < 0 := by
    intro y hy
    rw [hint] at hy
    have hstrict := arccos_gt_sqrt_of_mem y hy
    linarith
  have hanti := strictAntiOn_of_hasDerivWithinAt_neg hD hcont hder hneg
  have hxD : x ∈ D := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have h1D : (1 : ℝ) ∈ D := by
    change (-1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1
    norm_num
  have hlt := hanti hxD h1D hx.2
  have hone : kernelCurvatureGap 1 = 0 := by
    simp [kernelCurvatureGap]
  rw [hone] at hlt
  dsimp [kernelCurvatureGap] at hlt
  linarith

/-- Strict negativity of the exact rational expression for K''.
The identification with `deriv (deriv K)` requires differentiating the
already established `stationaryKernel_hasDerivAt`, and is not claimed
as a separately checked theorem here. -/
theorem stationaryKernel_second_derivative_expression_neg (x : ℝ)
    (hx : -1 < x ∧ x < 1) :
    ((1 + 2 * x) * Real.arccos x -
      (2 + x) * Real.sqrt (1 - x ^ 2)) /
      ((1 - x) * (Real.sqrt (1 - x ^ 2)) ^ 3) < 0 := by
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith [hx.2])
      (show 0 < 1 + x by linarith [hx.1])]
  exact Sphere3.stationary_kernel_second_derivative_certificate_neg
    x (Real.arccos x) (Real.sqrt (1 - x ^ 2)) hx.2
    (Real.sqrt_pos.mpr hrad) (stationaryKernel_curvature_gap_pos x hx)

end SphericalTetrahedron
