module

public import Mathlib

@[expose] public section

/-!
# Exact algebraic certificates for the global spherical-tetrahedron manuscript

The following lemmas isolate the computations in the Appendix and in the
inverse-Gram part of the triangle ordering lemma. All expressions are rational
functions of real variables; no spherical geometry, measure normalization, or
unproved analytic hypothesis is used.
-/

noncomputable section

namespace Sphere3

/-- Determinant of the unit-diagonal Gram matrix
`[[1,z,y],[z,1,x],[y,x,1]]`. -/
def triangleGramDet (x y z : ℝ) : ℝ :=
  1 + 2 * x * y * z - x ^ 2 - y ^ 2 - z ^ 2

/-- Explicit first coordinate of `K⁻¹ t`, with `K` as above. -/
def triangleGramInverse₁ (x y z a b c : ℝ) : ℝ :=
  ((1 - x ^ 2) * a + (x * y - z) * b + (x * z - y) * c) /
    triangleGramDet x y z

/-- Explicit second coordinate of `K⁻¹ t`. -/
def triangleGramInverse₂ (x y z a b c : ℝ) : ℝ :=
  ((x * y - z) * a + (1 - y ^ 2) * b + (y * z - x) * c) /
    triangleGramDet x y z

/-- Explicit third coordinate of `K⁻¹ t`. -/
def triangleGramInverse₃ (x y z a b c : ℝ) : ℝ :=
  ((x * z - y) * a + (y * z - x) * b + (1 - z ^ 2) * c) /
    triangleGramDet x y z

/-- The inverse-Gram coordinates solve the first row. -/
theorem triangleGramInverse_row₁ (x y z a b c : ℝ)
    (hD : triangleGramDet x y z ≠ 0) :
    triangleGramInverse₁ x y z a b c +
      z * triangleGramInverse₂ x y z a b c +
      y * triangleGramInverse₃ x y z a b c = a := by
  unfold triangleGramInverse₁ triangleGramInverse₂ triangleGramInverse₃
  field_simp [hD]
  dsimp [triangleGramDet]
  ring

/-- The inverse-Gram coordinates solve the second row. -/
theorem triangleGramInverse_row₂ (x y z a b c : ℝ)
    (hD : triangleGramDet x y z ≠ 0) :
    z * triangleGramInverse₁ x y z a b c +
      triangleGramInverse₂ x y z a b c +
      x * triangleGramInverse₃ x y z a b c = b := by
  unfold triangleGramInverse₁ triangleGramInverse₂ triangleGramInverse₃
  field_simp [hD]
  dsimp [triangleGramDet]
  ring

/-- The inverse-Gram coordinates solve the third row. -/
theorem triangleGramInverse_row₃ (x y z a b c : ℝ)
    (hD : triangleGramDet x y z ≠ 0) :
    y * triangleGramInverse₁ x y z a b c +
      x * triangleGramInverse₂ x y z a b c +
      triangleGramInverse₃ x y z a b c = c := by
  unfold triangleGramInverse₁ triangleGramInverse₂ triangleGramInverse₃
  field_simp [hD]
  dsimp [triangleGramDet]
  ring

/-- The explicit quadratic expression `tᵀ K⁻¹ t` for a triangle Gram matrix. -/
def triangleGramEnergy (x y z a b c : ℝ) : ℝ :=
  ((1 - x ^ 2) * a ^ 2 + (1 - y ^ 2) * b ^ 2 +
    (1 - z ^ 2) * c ^ 2 +
    2 * (x * y - z) * a * b +
    2 * (x * z - y) * a * c +
    2 * (y * z - x) * b * c) / triangleGramDet x y z

/-- The Gram energy is unchanged by interchanging the first two vertices. -/
theorem triangleGramEnergy_swap12 (x y z a b c : ℝ) :
    triangleGramEnergy x y z a b c =
      triangleGramEnergy y x z b a c := by
  have hd : triangleGramDet x y z = triangleGramDet y x z := by
    unfold triangleGramDet
    ring
  unfold triangleGramEnergy
  rw [← hd]
  ring

/-- The Gram energy is unchanged by interchanging the last two vertices. -/
theorem triangleGramEnergy_swap23 (x y z a b c : ℝ) :
    triangleGramEnergy x y z a b c =
      triangleGramEnergy x z y a c b := by
  have hd : triangleGramDet x y z = triangleGramDet x z y := by
    unfold triangleGramDet
    ring
  unfold triangleGramEnergy
  rw [← hd]
  ring

/-- If `t=Kz`, then the cofactor energy of `t` is `zᵀKz`. -/
theorem triangleGramEnergy_of_gram_coefficients
    (x y z a b c : ℝ) (hD : triangleGramDet x y z ≠ 0) :
    triangleGramEnergy x y z
        (a + z * b + y * c)
        (z * a + b + x * c)
        (y * a + x * b + c) =
      a ^ 2 + b ^ 2 + c ^ 2 +
        2 * z * a * b + 2 * y * a * c + 2 * x * b * c := by
  unfold triangleGramEnergy
  field_simp [hD]
  dsimp [triangleGramDet]
  ring

/-- The auxiliary polynomial occurring in the isosceles comparison. -/
def triangleIsoPolynomial (x y : ℝ) : ℝ :=
  -(x ^ 2) - 2 * x * y - 2 * x + 4 * y ^ 2 + 2 * y - 1

/-- The exact rational identity in the isosceles part of the ordering lemma. -/
theorem triangle_iso_integrand_identity (h x y : ℝ)
    (hx : h + x ≠ 0) (hy : h + y ≠ 0) :
    2 * (1 + x + 2 * y) * (1 + y) / (h + y) -
      (3 + x + 4 * y) * (1 + x) / (h + x) =
    ((h - 1) * triangleIsoPolynomial x y +
      (x ^ 2 - 1) * (1 + y)) / ((h + x) * (h + y)) := by
  unfold triangleIsoPolynomial
  field_simp [hx, hy]
  ring

/-- The exact rational identity for the inverse-ordering comparison.
This is the third displayed identity in the manuscript's appendix. -/
theorem triangle_order_integrand_identity (h u v w : ℝ)
    (huv : v - u ≠ 0)
    (hu : h + u ≠ 0) (hv : h + v ≠ 0) (hw : h + w ≠ 0) :
    w * (w ^ 2 + u * v) / (h + w) +
      (u ^ 2 * (w ^ 2 - v ^ 2) / (h + u) +
        v ^ 2 * (u ^ 2 - w ^ 2) / (h + v)) / (v - u) =
    -(h * (u - w) * (v - w) * (u * v - h * w)) /
      ((h + u) * (h + v) * (h + w)) := by
  field_simp [huv, hu, hv, hw]
  ring

/-- The first appendix identity, before the half-angle substitution.
The variables `pX`, `pY`, `pZ` represent `φ(X)`, `φ(Y)`, `φ(Z)`. -/
theorem triangle_inverse_order_J_identity
    (x y z pX pY pZ : ℝ)
    (hxy : y - x ≠ 0) (hD : triangleGramDet x y z ≠ 0) :
    2 * triangleGramDet x y z *
      (triangleGramInverse₁ x y z
        ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2)
        ((pX + pY - pZ) / 2) -
       triangleGramInverse₂ x y z
        ((pY + pZ - pX) / 2) ((pX + pZ - pY) / 2)
        ((pX + pY - pZ) / 2)) =
    (y - x) *
      ((1 + x + y + z) * pZ -
        (1 + z) * (pX + pY - 2 * ((pY - pX) / (y - x))) -
        (x + y) ^ 2 * ((pY - pX) / (y - x))) := by
  unfold triangleGramInverse₁ triangleGramInverse₂
  field_simp [hxy, hD]
  ring


/-- The polynomial in the isosceles integral is strictly negative on the
spherical-triangle admissible region. The split at `y=-1/2` is essential. -/
theorem triangle_iso_polynomial_neg (x y : ℝ)
    (hxy : y ≤ x) (hquad : 2 * y ^ 2 - 1 < x)
    (hylo : -1 < y) (hyhi : y < 1) :
    triangleIsoPolynomial x y < 0 := by
  by_cases hhalf : (-1 / 2 : ℝ) ≤ y
  · have hprod : 0 ≤ (x - y) * (x + 3 * y + 2) := by
      apply mul_nonneg
      · linarith
      · linarith
    have hybound : y ^ 2 < 1 := by
      nlinarith [mul_pos (by linarith : 0 < 1 - y)
        (by linarith : 0 < 1 + y)]
    unfold triangleIsoPolynomial
    nlinarith [hprod]
  · let r : ℝ := 2 * y ^ 2 - 1
    have hyr : 0 < y * (2 * y + 1) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hsum : 0 < x + r + 2 * y + 2 := by
      dsimp [r]
      nlinarith [hyr]
    have hprod : 0 < (x - r) * (x + r + 2 * y + 2) :=
      mul_pos (by dsimp [r]; linarith) hsum
    have hypos : 0 < y * (y - 1) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hy2 : 0 < (y + 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
    have hfact : 0 < y * (y - 1) * (y + 1) ^ 2 := mul_pos hypos hy2
    have hPr : triangleIsoPolynomial r y =
        -4 * y * (y - 1) * (y + 1) ^ 2 := by
      dsimp [triangleIsoPolynomial, r]
      ring
    have hPdiff : triangleIsoPolynomial x y - triangleIsoPolynomial r y =
        -(x - r) * (x + r + 2 * y + 2) := by
      dsimp [triangleIsoPolynomial]
      ring
    linarith

/-- The combined numerator in the isosceles integral is negative for
`h≥1`, independently of any calculus or spherical geometry. -/
theorem triangle_iso_integrand_numerator_neg
    (h x y : ℝ) (hh : 1 ≤ h) (hxlo : -1 < x) (hxhi : x < 1)
    (hylo : -1 < y) (hyhi : y < 1)
    (hxy : y ≤ x) (hquad : 2 * y ^ 2 - 1 < x) :
    (h - 1) * triangleIsoPolynomial x y +
      (x ^ 2 - 1) * (1 + y) < 0 := by
  have hP := triangle_iso_polynomial_neg x y hxy hquad hylo hyhi
  have hterm1 : (h - 1) * triangleIsoPolynomial x y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hP)
  have hsq : x ^ 2 < 1 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - x)
      (by linarith : 0 < 1 + x)]
  have hterm2 : (x ^ 2 - 1) * (1 + y) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  linarith

/-- Positivity of the nontrivial factor of the ordering integral.
The bounds `-w < u < w < v < 1` come from spherical triangle geometry. -/
theorem triangle_order_integrand_numerator_pos
    (h u v w : ℝ) (hh : 1 ≤ h)
    (huw : u < w) (hwu : -w < u) (hwv : w < v) (hv : v < 1) :
    0 < h * (w - u) * (v - w) * (h * w - u * v) := by
  have hw : 0 < w := by linarith
  have hvpos : 0 < v := lt_trans hw hwv
  have huvw : u * v < w := by
    by_cases hu : 0 ≤ u
    · have haux : 0 ≤ u * (1 - v) :=
        mul_nonneg hu (by linarith)
      nlinarith
    · have hneg : u * v < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hu) hvpos
      linarith
  have hscaled : w ≤ h * w := by
    have hn : 0 ≤ (h - 1) * w :=
      mul_nonneg (by linarith) (le_of_lt hw)
    nlinarith
  have hgap : 0 < h * w - u * v := by linarith
  exact mul_pos (mul_pos (mul_pos (by linarith) (by linarith))
    (by linarith)) hgap

end Sphere3
