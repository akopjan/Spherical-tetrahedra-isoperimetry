module

public import Mathlib

@[expose] public section

/-!
# Algebraic decomposition of the five-dimensional fixed-area tangent space

For the six edges of K4, a variation with zero total sum decomposes as
  x_ij = (u_i + u_j) + y_ij,
where sum_i u_i = 0 and y has zero row sums. The latter satisfies
  y01 = y23,  y02 = y13,  y03 = y12,
with the sum of those three parameters zero.
The first subspace has dimension 3, the second dimension 2.

At a regular spherical tetrahedron, the constrained Lagrangian Hessian
has eigenvalues
  -lambda * tau * U * (1+2*t) * (2*a-b),   multiplicity 3,
  -lambda * tau * U * b,                   multiplicity 2.
The sign of these coefficients is proved below, under explicit positive
hypotheses. This does NOT itself identify them with the Hessian of the
original Hausdorff measures; that analytic bridge is still open.
-/

namespace Sphere3

/-- A linear identity decomposing edge variations into the standard
three-dimensional mode and the complementary opposite-edge mode.
The four `u` parameters are half the four incident row sums. -/
theorem tangent_edge_mode_decomposition
    (x01 x02 x03 x12 x13 x23 : ℝ)
    (hS : x01+x02+x03+x12+x13+x23=0) :
    let u0 : ℝ := (x01+x02+x03)/2
    let u1 : ℝ := (x01+x12+x13)/2
    let u2 : ℝ := (x02+x12+x23)/2
    let u3 : ℝ := (x03+x13+x23)/2
    let y01 : ℝ := x01-(u0+u1)
    let y02 : ℝ := x02-(u0+u2)
    let y03 : ℝ := x03-(u0+u3)
    let y12 : ℝ := x12-(u1+u2)
    let y13 : ℝ := x13-(u1+u3)
    let y23 : ℝ := x23-(u2+u3)
    y01=y23 ∧ y02=y13 ∧ y03=y12 ∧ y01+y02+y03=0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The standard three-dimensional mode has row-sum eigenvalue 2
and is reversed by taking the opposite edge. -/
theorem standard_mode_row_and_opposite
    (u0 u1 u2 u3 : ℝ) (h : u0+u1+u2+u3=0) :
    ((u0+u1)+(u0+u2)+(u0+u3)=2*u0) ∧
    (u0+u1=-(u2+u3)) := by
  constructor <;> linarith

/-- Strict negativity of the three-dimensional Hessian mode under
the already derived nonresonance inequality `b < 2*a`. -/
theorem regular_standard_hessian_eigenvalue_negative
    (lam τ U t a b : ℝ)
    (hlam : 0 < lam) (hτ : 0 < τ) (hU : 0 < U)
    (ht : -(1/3 : ℝ) < t) (hres : b < 2*a) :
    -(lam * τ * U * (1+2*t) * (2*a-b)) < 0 := by
  have htpos : 0 < 1+2*t := by linarith
  have hdpos : 0 < 2*a-b := by linarith
  have hpos : 0 < lam * τ * U * (1+2*t) * (2*a-b) :=
    mul_pos (mul_pos (mul_pos (mul_pos hlam hτ) hU) htpos) hdpos
  linarith

/-- Strict negativity of the two-dimensional opposite-edge Hessian mode. -/
theorem regular_two_hessian_eigenvalue_negative
    (lam τ U b : ℝ)
    (hlam : 0 < lam) (hτ : 0 < τ) (hU : 0 < U) (hb : 0 < b) :
    -(lam * τ * U * b) < 0 := by
  have hpos : 0 < lam * τ * U * b :=
    mul_pos (mul_pos (mul_pos hlam hτ) hU) hb
  linarith

end Sphere3
