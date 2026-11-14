module

public import Mathlib

@[expose] public section

/-!
# The square-suspension perturbation: exact four-dimensional Gram algebra

The matrix in Section 6 of the global manuscript is

  [ 1 a b a ]
  [ a 1 a b ]
  [ b a 1 a ]
  [ a b a 1 ]

where `b = 2*a - 1 + d`. Its four spectral values are `4*a+d`, `d`,
and `2*(1-a)-d` twice. We avoid matrix diagonalization API by proving
an exact identity for the associated quadratic form.

All results below are purely algebraic.
-/

noncomputable section

namespace Sphere3

/-- The quadratic form of the manuscript's normal Gram matrix. -/
def squareSuspensionGramQ (a d x₀ x₁ x₂ x₃ : ℝ) : ℝ :=
  x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 +
    2 * a * (x₀ * x₁ + x₁ * x₂ + x₂ * x₃ + x₃ * x₀) +
    2 * (2 * a - 1 + d) * (x₀ * x₂ + x₁ * x₃)

/-- Exact orthogonal spectral decomposition, with no square roots. -/
theorem squareSuspensionGramQ_spectral
    (a d x₀ x₁ x₂ x₃ : ℝ) :
    4 * squareSuspensionGramQ a d x₀ x₁ x₂ x₃ =
      (4 * a + d) * (x₀ + x₁ + x₂ + x₃) ^ 2 +
      d * (x₀ - x₁ + x₂ - x₃) ^ 2 +
      2 * (2 * (1 - a) - d) *
        ((x₀ - x₂) ^ 2 + (x₁ - x₃) ^ 2) := by
  unfold squareSuspensionGramQ
  ring

/-- The spectral coordinates vanish simultaneously only at the origin. -/
theorem squareSuspensionSpectral_injective
    (x₀ x₁ x₂ x₃ : ℝ)
    (hS : x₀ + x₁ + x₂ + x₃ = 0)
    (hA : x₀ - x₁ + x₂ - x₃ = 0)
    (hD₀ : x₀ - x₂ = 0)
    (hD₁ : x₁ - x₃ = 0) :
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Under the positive-eigenvalue conditions, the quadratic form is
nonnegative. This is the PSD part of the Gram certificate. -/
theorem squareSuspensionGramQ_nonneg
    (a d x₀ x₁ x₂ x₃ : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hupper : d ≤ 2 * (1 - a)) :
    0 ≤ squareSuspensionGramQ a d x₀ x₁ x₂ x₃ := by
  have hA : 0 ≤ 4 * a + d := by linarith
  have hB : 0 ≤ 2 * (2 * (1 - a) - d) := by linarith
  have hS : 0 ≤ (4 * a + d) * (x₀ + x₁ + x₂ + x₃) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  have hAlt : 0 ≤ d * (x₀ - x₁ + x₂ - x₃) ^ 2 :=
    mul_nonneg hd (sq_nonneg _)
  have hDiff : 0 ≤ 2 * (2 * (1 - a) - d) *
      ((x₀ - x₂) ^ 2 + (x₁ - x₃) ^ 2) :=
    mul_nonneg hB (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hId := squareSuspensionGramQ_spectral a d x₀ x₁ x₂ x₃
  linarith

/-- Strict positive definiteness of the perturbed Gram form.
The conditions hold for `0<a<1`, `0<d<2*(1-a)`. -/
theorem squareSuspensionGramQ_pos
    (a d x₀ x₁ x₂ x₃ : ℝ)
    (ha : 0 < a) (hd : 0 < d)
    (hupper : d < 2 * (1 - a))
    (hnonzero : x₀ ≠ 0 ∨ x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0) :
    0 < squareSuspensionGramQ a d x₀ x₁ x₂ x₃ := by
  have hA : 0 < 4 * a + d := by linarith
  have hB : 0 < 2 * (2 * (1 - a) - d) := by linarith
  let S : ℝ := x₀ + x₁ + x₂ + x₃
  let A : ℝ := x₀ - x₁ + x₂ - x₃
  let D₀ : ℝ := x₀ - x₂
  let D₁ : ℝ := x₁ - x₃
  have hSpectral : S ≠ 0 ∨ A ≠ 0 ∨ D₀ ≠ 0 ∨ D₁ ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨hz₀, hz₁, hz₂, hz₃⟩ :=
      squareSuspensionSpectral_injective x₀ x₁ x₂ x₃
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    rcases hnonzero with hh | hh | hh | hh
    · exact hh hz₀
    · exact hh hz₁
    · exact hh hz₂
    · exact hh hz₃
  have hS : 0 ≤ (4 * a + d) * S ^ 2 :=
    mul_nonneg (le_of_lt hA) (sq_nonneg _)
  have hAlt : 0 ≤ d * A ^ 2 :=
    mul_nonneg (le_of_lt hd) (sq_nonneg _)
  have hDiff₀ : 0 ≤ 2 * (2 * (1 - a) - d) * D₀ ^ 2 :=
    mul_nonneg (le_of_lt hB) (sq_nonneg _)
  have hDiff₁ : 0 ≤ 2 * (2 * (1 - a) - d) * D₁ ^ 2 :=
    mul_nonneg (le_of_lt hB) (sq_nonneg _)
  have hstrict :
      0 < (4 * a + d) * S ^ 2 + d * A ^ 2 +
          2 * (2 * (1 - a) - d) * (D₀ ^ 2 + D₁ ^ 2) := by
    rcases hSpectral with h | h | h | h
    · have hp : 0 < (4 * a + d) * S ^ 2 :=
        mul_pos hA (sq_pos_of_ne_zero h)
      nlinarith [hDiff₀, hDiff₁]
    · have hp : 0 < d * A ^ 2 :=
        mul_pos hd (sq_pos_of_ne_zero h)
      nlinarith [hDiff₀, hDiff₁]
    · have hp : 0 < 2 * (2 * (1 - a) - d) * D₀ ^ 2 :=
        mul_pos hB (sq_pos_of_ne_zero h)
      nlinarith [hS, hAlt, hDiff₁]
    · have hp : 0 < 2 * (2 * (1 - a) - d) * D₁ ^ 2 :=
        mul_pos hB (sq_pos_of_ne_zero h)
      nlinarith [hS, hAlt, hDiff₀]
  have hId := squareSuspensionGramQ_spectral a d x₀ x₁ x₂ x₃
  dsimp [S, A, D₀, D₁] at hstrict
  linarith


/-- The degenerating alternating eigenvector has eigenvalue `d`.
At `d=0`, this gives the one-dimensional Gram kernel of the regular
square suspension. -/
theorem squareSuspension_alternating_eigenvalue (a d : ℝ) :
    squareSuspensionGramQ a d 1 (-1) 1 (-1) = 4 * d := by
  unfold squareSuspensionGramQ
  ring

theorem squareSuspension_boundary_null (a : ℝ) :
    squareSuspensionGramQ a 0 1 (-1) 1 (-1) = 0 := by
  rw [squareSuspension_alternating_eigenvalue]
  ring

end Sphere3
