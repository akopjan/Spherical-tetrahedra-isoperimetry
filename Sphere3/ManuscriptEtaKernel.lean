module

public import Sphere3.ManuscriptTriangleAlgebra

@[expose] public section

/-!
# Explicit positivity of the half-angle integral kernels

For every `s>0`, `η(s)=(s²+1)/(2s)≥1`. The manuscript's two
rational integrands then have a fixed strict sign. These lemmas
form the sign component of the triangle ordering argument.

The integral representation and integrability are handled in
`SphericalTetrahedron.ManuscriptKernelGlobal`.
-/

noncomputable section

namespace Sphere3

/-- The half-angle substitution used in the integral identities. -/
def manuscriptEta (s : ℝ) : ℝ := (s ^ 2 + 1) / (2 * s)

theorem manuscriptEta_ge_one (s : ℝ) (hs : 0 < s) :
    1 ≤ manuscriptEta s := by
  unfold manuscriptEta
  apply (le_div_iff₀ (by positivity : 0 < 2 * s)).2
  nlinarith [sq_nonneg (s - 1)]

/-- The complete positive integrand in the inverse-ordering lemma. -/
def manuscriptOrderIntegrand (u v w s : ℝ) : ℝ :=
  manuscriptEta s * (w - u) * (v - w) * (manuscriptEta s * w - u * v) /
    (s * (manuscriptEta s + u) * (manuscriptEta s + v) * (manuscriptEta s + w))

/-- Under the spherical half-angle constraints, the ordering
integrand is strictly positive for every positive integration variable. -/
theorem manuscriptOrderIntegrand_pos (u v w s : ℝ)
    (hs : 0 < s) (huw : u < w) (hwu : -w < u)
    (hwv : w < v) (hv : v < 1) :
    0 < manuscriptOrderIntegrand u v w s := by
  have heta := manuscriptEta_ge_one s hs
  have hw : 0 < w := by linarith
  have hu : -1 < u := by linarith
  have hnum := triangle_order_integrand_numerator_pos
    (manuscriptEta s) u v w heta huw hwu hwv hv
  have hdenu : 0 < manuscriptEta s + u := by linarith
  have hdenv : 0 < manuscriptEta s + v := by linarith
  have hdenw : 0 < manuscriptEta s + w := by linarith
  unfold manuscriptOrderIntegrand
  exact div_pos hnum (mul_pos (mul_pos
    (mul_pos hs hdenu) hdenv) hdenw)

/-- The complete strictly negative isosceles comparison integrand. -/
def manuscriptIsoIntegrand (x y s : ℝ) : ℝ :=
  ((manuscriptEta s - 1) * triangleIsoPolynomial x y +
    (x ^ 2 - 1) * (1 + y)) /
    ((manuscriptEta s + x) * (manuscriptEta s + y))

theorem manuscriptIsoIntegrand_neg (x y s : ℝ)
    (hs : 0 < s) (hxlo : -1 < x) (hxhi : x < 1)
    (hylo : -1 < y) (hyhi : y < 1)
    (hxy : y ≤ x) (hquad : 2 * y ^ 2 - 1 < x) :
    manuscriptIsoIntegrand x y s < 0 := by
  have heta := manuscriptEta_ge_one s hs
  have hnum := triangle_iso_integrand_numerator_neg
    (manuscriptEta s) x y heta hxlo hxhi hylo hyhi hxy hquad
  have hdenx : 0 < manuscriptEta s + x := by linarith
  have hdeny : 0 < manuscriptEta s + y := by linarith
  unfold manuscriptIsoIntegrand
  exact div_neg_of_neg_of_pos hnum (mul_pos hdenx hdeny)

end Sphere3
