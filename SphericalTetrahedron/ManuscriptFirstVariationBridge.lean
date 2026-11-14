module

public import SphericalTetrahedron.ManuscriptFaceProjection

@[expose] public section

/-!
# Algebraic completion of the Lagrange-multiplier argument

The manuscript gives for each edge `ij` the gradient coefficients

  dV_ij = ell_ij / 2
  dA_ij = (height_i + height_j) * tan(ell_ij / 2).

The half-angle identity says `ell_ij = tan(ell_ij/2)*phi(cos ell_ij)`.
Given these formulas and proportionality of gradients, the unique
stationarity system follows with a NONZERO multiplier, because the
volume gradient has a strictly positive component.

This module proves that algebraic conclusion without assuming
stationarity. The differentiability and Lagrange-multiplier steps are established in
`ManuscriptGaussianSchlafli` and `ManuscriptFirstVariation`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SphericalTetrahedron

/-- Abstract algebraic edge-gradient cancellation. The assumptions
are precisely the six proportional-derivative equations, positivity of
the angular factor, and the spherical half-angle identity. -/
theorem manifold_lagrange_to_edge_equations
    (ell a : Fin 4 → Fin 4 → ℝ) (height : Fin 4 → ℝ)
    (K : Fin 4 → Fin 4 → ℝ) (mu : ℝ)
    (hEll : ∀ i j : Fin 4, i ≠ j → 0 < ell i j)
    (hA : ∀ i j : Fin 4, i ≠ j → 0 < a i j)
    (hTrig : ∀ i j : Fin 4, i ≠ j →
      ell i j = a i j * K i j)
    (hVar : ∀ i j : Fin 4, i ≠ j →
      ell i j / 2 = mu * ((height i + height j) * a i j)) :
    ∃ c : ℝ, c ≠ 0 ∧
      ∀ i j : Fin 4, i ≠ j →
        height i + height j = c * K i j := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hmu : mu ≠ 0 := by
    intro hz
    have hv := hVar 0 1 h01
    rw [hz] at hv
    have hp := hEll 0 1 h01
    nlinarith
  let c : ℝ := (2 * mu)⁻¹
  have hc : c ≠ 0 := by
    dsimp [c]
    exact inv_ne_zero (mul_ne_zero (by norm_num) hmu)
  have hc_unit : c * (2 * mu) = 1 := by
    dsimp [c]
    exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) hmu)
  refine ⟨c, hc, ?_⟩
  intro i j hij
  have hv := hVar i j hij
  have htri := hTrig i j hij
  have hfac := hA i j hij
  have hcancel : a i j * K i j =
      a i j * (2 * mu * (height i + height j)) := by
    nlinarith [hv, htri]
  have hK : K i j = 2 * mu * (height i + height j) :=
    mul_left_cancel₀ hfac.ne' hcancel
  calc
    height i + height j = 1 * (height i + height j) := by ring
    _ = (c * (2 * mu)) * (height i + height j) := by rw [hc_unit]
    _ = c * (2 * mu * (height i + height j)) := by ring
    _ = c * K i j := by rw [hK]

/-- The manuscript's Lagrange system implies the `Stationary` predicate
of the original challenge, once edge gradients and their trigonometric
connection have been established on the six-dimensional Gram chart. -/
theorem stationary_of_manuscript_variational_certificate
    (T : SphericalTetrahedron)
    (ell a : Fin 4 → Fin 4 → ℝ) (mu : ℝ)
    (hEll : ∀ i j : Fin 4, i ≠ j → 0 < ell i j)
    (hA : ∀ i j : Fin 4, i ≠ j → 0 < a i j)
    (hTrig : ∀ i j : Fin 4, i ≠ j →
      ell i j = a i j * stationaryKernel
        ⟪T.dualVertex i, T.dualVertex j⟫_ℝ)
    (hVar : ∀ i j : Fin 4, i ≠ j →
      ell i j / 2 = mu *
        ((⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
          ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ) * a i j)) :
    T.Stationary := by
  obtain ⟨c, hc, hEq⟩ := manifold_lagrange_to_edge_equations
    ell a (fun i => ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ)
    (fun i j => stationaryKernel ⟪T.dualVertex i, T.dualVertex j⟫_ℝ)
    mu hEll hA hTrig hVar
  apply (T.stationary_iff_dualVertex_equations).mpr
  exact ⟨c, hc, hEq⟩

end SphericalTetrahedron
