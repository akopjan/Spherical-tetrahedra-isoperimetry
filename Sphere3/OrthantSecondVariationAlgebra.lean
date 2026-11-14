module

public import Mathlib

@[expose] public section

/-!
# Orthant: negative second variation on the fixed-area tangent space

Let `x01, ..., x23` be the six first-order Gram variations of the
inward facet normals at the spherical orthant (normal Gram matrix `I₄`).
The first area variation is `2 * (sum xij)`, and the first volume
variation is `(pi / 4) * (sum xij)`. Thus the relevant Lagrangian is
`volume - (pi / 8) * area`.

Its second differential is the quadratic form

  Q = Opp + (pi / 4) * Adj,

where `Opp` is the sum of products of opposite edges and `Adj` is the sum
of products of edges sharing a vertex. The exact identity

  Q = pi / 8 * S² - (pi - 2)/8 * P - 1/4 * M

holds, where `S` is the sum of all six edge variations, `P` is the sum
of squared *sums* on the three opposite pairs, and `M` is the sum of
squared *differences* on these pairs. Hence `Q < 0` on `S = 0`, except
in the zero direction.

This file formalizes the polynomial and order-theoretic part of that
calculation.
-/

noncomputable section

namespace Sphere3

def edgeSum (a b c d e f : ℝ) : ℝ := a + b + c + d + e + f

def oppositeProducts (a b c d e f : ℝ) : ℝ := a * f + b * e + c * d

def adjacentProducts (a b c d e f : ℝ) : ℝ :=
  a*b + a*c + a*d + a*e + b*c + b*d + b*f +
  c*e + c*f + d*e + d*f + e*f

def oppositePairSumsSq (a b c d e f : ℝ) : ℝ :=
  (a+f)^2 + (b+e)^2 + (c+d)^2

def oppositePairDiffSq (a b c d e f : ℝ) : ℝ :=
  (a-f)^2 + (b-e)^2 + (c-d)^2

/-- Exact expression for the constrained Lagrangian Hessian at the
orthant in the six off-diagonal Gram coordinates. -/
def orthantVariationQuadratic (a b c d e f : ℝ) : ℝ :=
  oppositeProducts a b c d e f +
    (Real.pi / 4) * adjacentProducts a b c d e f

/-- A pure polynomial identity, valid for all six real variations. -/
theorem orthant_quadratic_decomposition
    (a b c d e f : ℝ) :
    orthantVariationQuadratic a b c d e f =
      (Real.pi / 8) * (edgeSum a b c d e f)^2 -
        ((Real.pi - 2) / 8) * oppositePairSumsSq a b c d e f -
        (1 / 4 : ℝ) * oppositePairDiffSq a b c d e f := by
  unfold orthantVariationQuadratic oppositeProducts adjacentProducts
    edgeSum oppositePairSumsSq oppositePairDiffSq
  ring

/-- Strict negativity on the tangent space `d(area) = 2*S = 0`, provided
the variation is nonzero, expressed by the sum of opposite-pair squares. -/
theorem orthant_second_variation_strict
    (a b c d e f : ℝ)
    (hS : edgeSum a b c d e f = 0)
    (hne : 0 < oppositePairSumsSq a b c d e f +
      oppositePairDiffSq a b c d e f) :
    orthantVariationQuadratic a b c d e f < 0 := by
  let p : ℝ := oppositePairSumsSq a b c d e f
  let m : ℝ := oppositePairDiffSq a b c d e f
  have hp : 0 ≤ p := by
    dsimp [p, oppositePairSumsSq]
    positivity
  have hm : 0 ≤ m := by
    dsimp [m, oppositePairDiffSq]
    positivity
  have hpm : 0 < p + m := hne
  have hcoeff : (0 : ℝ) < (Real.pi - 2) / 8 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hstrict : 0 < ((Real.pi - 2) / 8) * p + (1 / 4 : ℝ) * m := by
    rcases lt_or_eq_of_le hp with hpos | heq
    · exact add_pos_of_pos_of_nonneg
        (mul_pos hcoeff hpos) (mul_nonneg (by norm_num) hm)
    · have hmpos : 0 < m := by linarith
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (le_of_lt hcoeff) hp)
        (mul_pos (by norm_num) hmpos)
  rw [orthant_quadratic_decomposition, hS]
  norm_num
  linarith


/-- Pairwise energy is exactly twice the squared Euclidean norm of
all six independent Gram variations. -/
theorem opposite_pair_energy_eq_two_sq
    (a b c d e f : ℝ) :
    oppositePairSumsSq a b c d e f +
      oppositePairDiffSq a b c d e f =
        2 * (a^2+b^2+c^2+d^2+e^2+f^2) := by
  unfold oppositePairSumsSq oppositePairDiffSq
  ring

/-- The opposite-pair energy is strictly positive for any nonzero
six-vector. Unlike `orthant_second_variation_strict`, this lemma
needs only an ordinary disjunction expressing nonzero components. -/
theorem opposite_pair_energy_pos_of_nonzero
    (a b c d e f : ℝ)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0) :
    0 < oppositePairSumsSq a b c d e f +
      oppositePairDiffSq a b c d e f := by
  rw [opposite_pair_energy_eq_two_sq]
  have hsum : 0 < a^2+b^2+c^2+d^2+e^2+f^2 := by
    rcases h with ha | hb | hc | hd | he | hf
    · nlinarith only [sq_pos_of_ne_zero ha, sq_nonneg b,
        sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg f]
    · nlinarith only [sq_nonneg a, sq_pos_of_ne_zero hb,
        sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg f]
    · nlinarith only [sq_nonneg a, sq_nonneg b,
        sq_pos_of_ne_zero hc, sq_nonneg d, sq_nonneg e, sq_nonneg f]
    · nlinarith only [sq_nonneg a, sq_nonneg b,
        sq_nonneg c, sq_pos_of_ne_zero hd, sq_nonneg e, sq_nonneg f]
    · nlinarith only [sq_nonneg a, sq_nonneg b,
        sq_nonneg c, sq_nonneg d, sq_pos_of_ne_zero he, sq_nonneg f]
    · nlinarith only [sq_nonneg a, sq_nonneg b,
        sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_pos_of_ne_zero hf]
  linarith

/-- Algebraic strict negative definiteness at the orthant on the
five-dimensional fixed-area tangent hyperplane. -/
theorem orthant_second_variation_negative_of_nonzero
    (a b c d e f : ℝ)
    (hS : edgeSum a b c d e f = 0)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0) :
    orthantVariationQuadratic a b c d e f < 0 := by
  exact orthant_second_variation_strict a b c d e f hS
    (opposite_pair_energy_pos_of_nonzero a b c d e f hne)


/-- Quantitative coercivity at the spherical orthant.  The factor `1/4`
is deliberately weaker than the sharp smallest curvature
`(Real.pi - 2)/4`, so its proof only needs `3 < pi`.  This is a
polynomial consequence of the known Hessian formula, not yet the
analytic theorem that the geometric Hessian has this formula. -/
theorem orthant_hessian_uniform_upper_bound
    (a b c d e f : ℝ)
    (hS : edgeSum a b c d e f = 0) :
    orthantVariationQuadratic a b c d e f ≤
      -(1/4 : ℝ) * (a^2+b^2+c^2+d^2+e^2+f^2) := by
  let p : ℝ := oppositePairSumsSq a b c d e f
  let m : ℝ := oppositePairDiffSq a b c d e f
  have hp : 0 ≤ p := by dsimp [p, oppositePairSumsSq]; positivity
  have hm : 0 ≤ m := by dsimp [m, oppositePairDiffSq]; positivity
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcoef : (1/8 : ℝ) ≤ (Real.pi-2)/8 := by linarith
  have hpineq : (1/8 : ℝ)*p ≤ ((Real.pi-2)/8)*p :=
    mul_le_mul_of_nonneg_right hcoef hp
  have hmineq : (1/8 : ℝ)*m ≤ (1/4)*m :=
    mul_le_mul_of_nonneg_right (by norm_num) hm
  have hq : orthantVariationQuadratic a b c d e f =
      -((Real.pi-2)/8)*p-(1/4)*m := by
    rw [orthant_quadratic_decomposition, hS]
    dsimp [p, m]
    ring
  have henergy : p+m =
      2*(a^2+b^2+c^2+d^2+e^2+f^2) :=
    opposite_pair_energy_eq_two_sq a b c d e f
  rw [hq]
  nlinarith only [hpineq, hmineq, henergy]

end Sphere3
