module

public import Mathlib

@[expose] public section

/-!
# A scalar contraction estimate for radial normalization

For any nonzero vectors `x`, `y` in a real inner product space with
`1 ≤ ‖x‖` and `1 ≤ ‖y‖`, radial normalization contracts the chordal
distance. The scalar identity in this file is the algebraic heart of
that fact. It is intended for the gnomonic map `u ↦ (u,1)/‖(u,1)‖`.
-/

noncomputable section

namespace Sphere3

/-- For `a,b ≥ 1` and `c ≤ ab`, the squared distance between two
unit directions is no larger than the squared distance between the
original vectors. The variables model the two norms and the inner
product of the vectors, respectively. -/
theorem radialNormalization_scalar_contracts
    (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : c ≤ a * b) :
    2 - 2 * c / (a * b) ≤ a ^ 2 + b ^ 2 - 2 * c := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  have hprod : 1 ≤ a * b := by
    have h : 0 ≤ (a - 1) * (b - 1) :=
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    nlinarith
  have hquot : c / (a * b) ≤ 1 := by
    apply (div_le_iff₀ hab0).2
    nlinarith [hc]
  have hnonneg : 0 ≤ (a - b) ^ 2 +
      2 * (a * b - 1) * (1 - c / (a * b)) := by
    have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ 2 * (a * b - 1) * (1 - c / (a * b)) := by
      apply mul_nonneg
      · nlinarith [hprod]
      · linarith [hquot]
    linarith
  have hident :
      a ^ 2 + b ^ 2 - 2 * c - (2 - 2 * c / (a * b)) =
        (a - b) ^ 2 + 2 * (a * b - 1) * (1 - c / (a * b)) := by
    field_simp [ne_of_gt ha0, ne_of_gt hb0]
    <;> ring
  linarith

/-- The factorization controlling the change in squared distance under
radial normalization. No geometric or measure-theoretic assumptions. -/
theorem radialNormalization_scalar_identity
    (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 2 + b ^ 2 - 2 * c - (2 - 2 * c / (a * b)) =
      (a - b) ^ 2 + 2 * (a * b - 1) * (1 - c / (a * b)) := by
  field_simp [ha, hb]
  <;> ring

end Sphere3
