module

public import Mathlib

@[expose] public section

/-!
# Infinitesimal rigidity of the six-edge stationarity system

This file is an *algebraic* theorem, requiring no differentiability
assumptions. It gives the injectivity statement needed after differentiating
stationarity equations along the regular one-parameter family.

Let `xij` be the first-order changes of the six off-diagonal entries of a
symmetric `4 x 4` Gram matrix and let `si = sum_{j != i} xij` be the four
row sums. If

  a * (si + sj) - b * xij = z

for all six edges and if `b != 0` and `2*a != b`, then all six variations
are equal. In particular, modulo the regular deformation direction, the
linearized system has trivial kernel.

This module establishes the purely algebraic injectivity of the
linearized system.
-/

noncomputable section

namespace Sphere3

private theorem edge_switch
    (a b z ti tl rj rk u v w x : ℝ)
    (hb : b ≠ 0) (hab : 2 * a ≠ b)
    (hrow : rj - rk = (u - v) + (w - x))
    (hij : a * (ti + rj) - b * u = z)
    (hik : a * (ti + rk) - b * v = z)
    (hlj : a * (tl + rj) - b * w = z)
    (hlk : a * (tl + rk) - b * x = z) :
    u = v ∧ w = x := by
  have hu : a * (rj - rk) = b * (u - v) := by
    nlinarith only [hij, hik]
  have hw : a * (rj - rk) = b * (w - x) := by
    nlinarith only [hlj, hlk]
  have hdifference : u - v = w - x := by
    apply mul_left_cancel₀ hb
    nlinarith only [hu, hw]
  have hrow' : rj - rk = 2 * (u - v) := by
    rw [hrow, ← hdifference]
    ring
  have hfactor : (2 * a - b) * (u - v) = 0 := by
    calc
      (2 * a - b) * (u - v) = a * (rj - rk) - b * (u - v) := by
        rw [hrow']
        ring
      _ = 0 := sub_eq_zero.mpr hu
  have huv : u - v = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hab)
  constructor
  · exact sub_eq_zero.mp huv
  · exact sub_eq_zero.mp (hdifference.symm.trans huv)

/-- The nonconstant first-order edge modes cannot satisfy the regular
stationarity linearization when `b != 0` and `b != 2*a`. -/
theorem stationary_linearization_all_edges_equal
    (a b z x01 x02 x03 x12 x13 x23 : ℝ)
    (hb : b ≠ 0) (hab : 2 * a ≠ b)
    (h01 : a * ((x01 + x02 + x03) + (x01 + x12 + x13)) - b * x01 = z)
    (h02 : a * ((x01 + x02 + x03) + (x02 + x12 + x23)) - b * x02 = z)
    (h03 : a * ((x01 + x02 + x03) + (x03 + x13 + x23)) - b * x03 = z)
    (h12 : a * ((x01 + x12 + x13) + (x02 + x12 + x23)) - b * x12 = z)
    (h13 : a * ((x01 + x12 + x13) + (x03 + x13 + x23)) - b * x13 = z)
    (h23 : a * ((x02 + x12 + x23) + (x03 + x13 + x23)) - b * x23 = z) :
    x01 = x02 ∧ x01 = x03 ∧ x01 = x12 ∧
      x01 = x13 ∧ x01 = x23 := by
  let s0 : ℝ := x01 + x02 + x03
  let s1 : ℝ := x01 + x12 + x13
  let s2 : ℝ := x02 + x12 + x23
  let s3 : ℝ := x03 + x13 + x23
  have e01 : a * (s0 + s1) - b * x01 = z := h01
  have e02 : a * (s0 + s2) - b * x02 = z := h02
  have e03 : a * (s0 + s3) - b * x03 = z := h03
  have e12 : a * (s1 + s2) - b * x12 = z := h12
  have e13 : a * (s1 + s3) - b * x13 = z := h13
  have e23 : a * (s2 + s3) - b * x23 = z := h23
  have h12row : s1 - s2 = (x01 - x02) + (x13 - x23) := by
    dsimp [s1, s2]
    ring
  have h13row : s1 - s3 = (x01 - x03) + (x12 - x23) := by
    dsimp [s1, s3]
    ring
  have h02row : s0 - s2 = (x01 - x12) + (x03 - x23) := by
    dsimp [s0, s2]
    ring
  obtain ⟨h01eq02, h13eq23⟩ := edge_switch a b z
    s0 s3 s1 s2 x01 x02 x13 x23 hb hab h12row
    e01 e02 (by simpa only [add_comm] using e13)
      (by simpa only [add_comm] using e23)
  obtain ⟨h01eq03, h12eq23⟩ := edge_switch a b z
    s0 s2 s1 s3 x01 x03 x12 x23 hb hab h13row
    e01 e03 (by simpa only [add_comm] using e12) e23
  obtain ⟨h01eq12, h03eq23⟩ := edge_switch a b z
    s1 s3 s0 s2 x01 x12 x03 x23 hb hab h02row
    (by simpa only [add_comm] using e01)
    (by simpa only [add_comm] using e12)
    (by simpa only [add_comm] using e03)
    (by simpa only [add_comm] using e23)
  exact ⟨h01eq02, h01eq03, h01eq12,
    h01eq12.trans (h12eq23.trans h13eq23.symm),
    h01eq12.trans h12eq23⟩

end Sphere3
