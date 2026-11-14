module

public import Mathlib

@[expose] public section

/-!
# Algebraic obstruction to a critical point of total face area

The genuine formula for the area differential in unit-normal Gram
coordinates has six components, each a strictly positive factor times
`h_i+h_j`, where `h = H * alpha` and `H` is the positive-definite
dual vertex Gram matrix. In particular, `h != 0`.

Below is the algebraic part: four real numbers whose pairwise sums
vanish on a triangle and a fourth incident edge must all be zero.
This is NOT the analytic statement that the area gradient is nonzero;
that requires establishing the differential formula and positivity.
-/

namespace Sphere3

/-- Four heights vanish if the pairwise sums on three triangles vanish. -/
theorem heights_zero_of_four_pair_sums
    (h0 h1 h2 h3 : ℝ)
    (h01 : h0+h1=0) (h02 : h0+h2=0)
    (h12 : h1+h2=0) (h03 : h0+h3=0) :
    h0=0 ∧ h1=0 ∧ h2=0 ∧ h3=0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The elementary contradiction needed to show that at least one of
the six area-gradient components is nonzero, once `h!=0` is known. -/
theorem exists_nonzero_pair_sum
    (h0 h1 h2 h3 : ℝ)
    (h : h0 ≠ 0 ∨ h1 ≠ 0 ∨ h2 ≠ 0 ∨ h3 ≠ 0) :
    h0+h1 ≠ 0 ∨ h0+h2 ≠ 0 ∨
    h1+h2 ≠ 0 ∨ h0+h3 ≠ 0 := by
  by_contra hall
  push_neg at hall
  rcases hall with ⟨h01,h02,h12,h03⟩
  obtain ⟨hzero0,hzero1,hzero2,hzero3⟩ :=
    heights_zero_of_four_pair_sums h0 h1 h2 h3 h01 h02 h12 h03
  rcases h with h | h | h | h
  · exact h hzero0
  · exact h hzero1
  · exact h hzero2
  · exact h hzero3

end Sphere3
