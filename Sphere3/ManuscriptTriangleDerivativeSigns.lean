module

public import Sphere3.ManuscriptTriangleAlgebra

@[expose] public section

/-!
# The order-theoretic signs in the triangle ordering lemma

This file formalizes only elementary deductions from the Gram row
differences and the strict lower bound for the angular secant slope.
The analytic and geometric inequalities feeding these hypotheses are
supplied in `SphericalTetrahedron.ManuscriptTriangleOrdering`.
-/

namespace Sphere3

/-- The smallest inverse-Gram coordinate exceeds `1/3` whenever the
row-difference equation and the strict angular secant bound apply.
This is the algebraic heart of the estimate `z_i >= 1/3`. -/
theorem triangle_smallest_inverse_coefficient_gt_third
    (k23 k12 k13 t2 t3 z1 z2 z3 : ℝ)
    (hk23 : k23 < 1) (hkdiff : k13 < k12)
    (hz23 : z2 ≤ z3)
    (hrow : t2 - t3 =
      (1 - k23) * (z2 - z3) + (k12 - k13) * z1)
    (hsec : (k12 - k13) / 3 < t2 - t3) :
    (1 : ℝ) / 3 < z1 := by
  have hrowNonpos : (1 - k23) * (z2 - z3) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hmain : (k12 - k13) / 3 < (k12 - k13) * z1 := by
    nlinarith [hrowNonpos, hrow, hsec]
  have hprod : 0 < (k12 - k13) * (z1 - 1 / 3) := by
    nlinarith [hmain]
  by_contra hn
  have hzbad : z1 ≤ (1 : ℝ) / 3 := le_of_not_gt hn
  have hsign : (k12 - k13) * (z1 - 1 / 3) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  linarith

/-- If the larger inverse-Gram comparison term is at least `1`, then
the second strictly positive term forces the entire gradient negative. -/
theorem triangle_gradient_negative_of_comparison
    (zi zj zk g1 g2 : ℝ)
    (hzi : 0 < zi) (hzj : 0 < zj) (hg1 : 0 < g1)
    (hcomparison : 1 ≤ g2 * zk) :
    2 * zi * (1 - g1 * zj - g2 * zk) < 0 := by
  have hpositive : 0 < g1 * zj := mul_pos hg1 hzj
  have hnegative : 1 - g1 * zj - g2 * zk < 0 := by linarith
  exact mul_neg_of_pos_of_neg (by linarith) hnegative

/-- The isosceles derivative sign used in the manuscript, reduced to
`g U >= 1` and `U < 2 W`. -/
theorem triangle_isosceles_derivative_negative
    (U W g : ℝ) (hU : 0 < U) (hg : 0 < g)
    (hgu : 1 ≤ g * U) (hUW : U < 2 * W) :
    2 * U * (1 - 2 * g * W) < 0 := by
  have hscaled : g * U < g * (2 * W) :=
    mul_lt_mul_of_pos_left hUW hg
  have hnegative : 1 - 2 * g * W < 0 := by
    nlinarith [hgu, hscaled]
  exact mul_neg_of_pos_of_neg (by linarith) hnegative

end Sphere3
