module

public import SphericalTetrahedron.StationaryKernelCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Exact derivative and strict monotonicity of the stationarity kernel

Establishes the derivative formula for `stationaryKernel` on `(-1, 1)`
and deduces strict monotonicity.
-/

noncomputable section

namespace SphericalTetrahedron

/-- Algebraic derivative simplification independent of `arccos` and `sqrt`.
The assumptions encode the square-root identity. -/
theorem stationaryKernel_derivative_field_identity
    (x theta s : ℝ) (hs : s ^ 2 = 1 - x ^ 2)
    (hs0 : s ≠ 0) (hx : 1 - x ≠ 0) :
    ((theta + (1 + x) * (-(1 / s))) * s -
      ((1 + x) * theta) * ((-2 * x) / (2 * s))) / s ^ 2 =
      (theta - s) / ((1 - x) * s) := by
  field_simp [hs0, hx]
  linear_combination (s - x * theta) * hs

/-- The angular edge kernel has the asserted positive derivative at
all feasible inner products. -/
theorem stationaryKernel_hasDerivAt (x : ℝ)
    (hx : -1 < x ∧ x < 1) :
    HasDerivAt stationaryKernel
      ((Real.arccos x - Real.sqrt (1 - x ^ 2)) /
       ((1 - x) * Real.sqrt (1 - x ^ 2))) x := by
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - x by linarith [hx.2])
      (show 0 < 1 + x by linarith [hx.1])]
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hrad).ne'
  have hx1 : x ≠ -1 := by linarith [hx.1]
  have hx2 : x ≠ 1 := by linarith [hx.2]
  have hxm : 1 - x ≠ 0 := by linarith [hx.2]
  have hpoly : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    norm_num
  have hroot := hpoly.sqrt hrad.ne'
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hnum := h1.mul (Real.hasDerivAt_arccos hx1 hx2)
  have hquot := hnum.div hroot hs0
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hrad.le
  have halgebra := stationaryKernel_derivative_field_identity
    x (Real.arccos x) (Real.sqrt (1 - x ^ 2)) hsq hs0 hxm
  have hfun :
      (fun y : ℝ => (1 + y) * Real.arccos y /
        Real.sqrt (1 - y ^ 2)) = stationaryKernel := by
    funext y
    simp only [stationaryKernel, mul_div_assoc]
  rw [← hfun]
  convert hquot using 1
  simp only [Pi.mul_apply, one_mul]
  exact halgebra.symm

/-- Positive derivative at each point of the admissible interval. -/
theorem stationaryKernel_hasDerivAt_pos (x : ℝ)
    (hx : -1 < x ∧ x < 1) :
    ∃ r : ℝ, 0 < r ∧ HasDerivAt stationaryKernel r x := by
  exact ⟨_, stationaryKernel_derivative_certificate_pos x hx,
    stationaryKernel_hasDerivAt x hx⟩

/-- The edge stationarity kernel is strictly increasing on `(-1,1)`. -/
theorem stationaryKernel_strictMonoOn :
    StrictMonoOn stationaryKernel (Set.Ioo (-1 : ℝ) 1) := by
  let D : Set ℝ := Set.Ioo (-1) 1
  have hD : Convex ℝ D := convex_Ioo (-1) 1
  have hinterior : interior D = D := isOpen_Ioo.interior_eq
  have hcont : ContinuousOn stationaryKernel D := by
    intro x hx
    exact (stationaryKernel_hasDerivAt x hx).continuousAt.continuousWithinAt
  have hder : ∀ x ∈ interior D,
      HasDerivWithinAt stationaryKernel
        ((Real.arccos x - Real.sqrt (1 - x ^ 2)) /
         ((1 - x) * Real.sqrt (1 - x ^ 2))) (interior D) x := by
    intro x hx
    rw [hinterior] at hx
    exact (stationaryKernel_hasDerivAt x hx).hasDerivWithinAt
  have hpos : ∀ x ∈ interior D,
      0 < (Real.arccos x - Real.sqrt (1 - x ^ 2)) /
         ((1 - x) * Real.sqrt (1 - x ^ 2)) := by
    intro x hx
    rw [hinterior] at hx
    exact stationaryKernel_derivative_certificate_pos x hx
  exact strictMonoOn_of_hasDerivWithinAt_pos hD hcont hder hpos

end SphericalTetrahedron
