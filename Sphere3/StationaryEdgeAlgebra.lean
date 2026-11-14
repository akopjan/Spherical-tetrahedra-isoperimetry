module

public import Mathlib

@[expose] public section

/-!
# Exact linear relations forced by six stationary edge equations

If edge values have the form `c * K i j = h i + h j`, the three sums
of opposite-edge values are equal.  Conversely, every vertex height is
recovered from any three-edge triangle.  These purely algebraic lemmas
have no geometric, trigonometric or measure-theoretic assumptions.
-/

namespace Sphere3

/-- Each vertex height is recovered from three incident edge equations. -/
theorem stationary_height_triangle_identity
    (h : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ) (c : ℝ)
    (heq : ∀ i j : Fin 4, i ≠ j → h i + h j = c * K i j)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    2 * h i = c * (K i j + K i k - K j k) := by
  calc
    2 * h i = (h i + h j) + (h i + h k) - (h j + h k) := by ring
    _ = c * (K i j + K i k - K j k) := by
      rw [heq i j hij, heq i k hik, heq j k hjk]
      ring

/-- The two independent opposite-edge constraints for four vertices.
    This is a necessary condition for a stationary tetrahedron, with
    no positivity assumption on its Lagrange multiplier. -/
theorem stationary_opposite_edge_identities
    (h : Fin 4 → ℝ) (K : Fin 4 → Fin 4 → ℝ) (c : ℝ)
    (hc : c ≠ 0)
    (heq : ∀ i j : Fin 4, i ≠ j → h i + h j = c * K i j) :
    K 0 1 + K 2 3 = K 0 2 + K 1 3 ∧
      K 0 1 + K 2 3 = K 0 3 + K 1 2 := by
  have h01 := heq 0 1 (by decide)
  have h02 := heq 0 2 (by decide)
  have h03 := heq 0 3 (by decide)
  have h12 := heq 1 2 (by decide)
  have h13 := heq 1 3 (by decide)
  have h23 := heq 2 3 (by decide)
  constructor
  · apply mul_left_cancel₀ hc
    calc
      c * (K 0 1 + K 2 3) = (h 0 + h 1) + (h 2 + h 3) := by
        rw [mul_add, ← h01, ← h23]
      _ = (h 0 + h 2) + (h 1 + h 3) := by ring
      _ = c * (K 0 2 + K 1 3) := by
        rw [mul_add, ← h02, ← h13]
  · apply mul_left_cancel₀ hc
    calc
      c * (K 0 1 + K 2 3) = (h 0 + h 1) + (h 2 + h 3) := by
        rw [mul_add, ← h01, ← h23]
      _ = (h 0 + h 3) + (h 1 + h 2) := by ring
      _ = c * (K 0 3 + K 1 2) := by
        rw [mul_add, ← h03, ← h12]

end Sphere3
