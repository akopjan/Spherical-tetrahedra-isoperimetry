module

public import Sphere3.CanonicalCones

@[expose] public section

/-!
# Gnomonic base of the canonical spherical tetrahedron

A canonical tetrahedral cone has a particularly simple cross section
at last coordinate `z = 1`. This cross section is a bounded Euclidean
tetrahedron, and spherical normalization is its gnomonic image.
-/

noncomputable section

namespace Sphere3

/-- A coordinate-inequality model for the regular Euclidean tetrahedron. -/
def GnomonicBase (t : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {u | CanonicalCone t (u 0) (u 1) (u 2) 1}

/-- The gnomonic cross section is closed. -/
theorem gnomonicBase_isClosed (t : ℝ) : IsClosed (GnomonicBase t) := by
  have h0 : IsClosed {u : EuclideanSpace ℝ (Fin 3) |
      0 ≤ u 0 + u 1 + u 2 + t} :=
    isClosed_le continuous_const (by fun_prop)
  have h1 : IsClosed {u : EuclideanSpace ℝ (Fin 3) |
      0 ≤ u 0 - u 1 - u 2 + t} :=
    isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {u : EuclideanSpace ℝ (Fin 3) |
      0 ≤ -u 0 + u 1 - u 2 + t} :=
    isClosed_le continuous_const (by fun_prop)
  have h3 : IsClosed {u : EuclideanSpace ℝ (Fin 3) |
      0 ≤ -u 0 - u 1 + u 2 + t} :=
    isClosed_le continuous_const (by fun_prop)
  simpa only [GnomonicBase, CanonicalCone, mul_one, Set.setOf_and]
    using h0.inter (h1.inter (h2.inter h3))

/-- The cross-section inequalities imply the sharp coordinate bounds. -/
theorem canonicalCone_base_bounds {t a b c : ℝ}
    (h : CanonicalCone t a b c 1) :
    -t ≤ a ∧ a ≤ t ∧ -t ≤ b ∧ b ≤ t ∧ -t ≤ c ∧ c ≤ t := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp only [mul_one] at h0 h1 h2 h3
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The cross section lies in the coordinate cube `[-t,t]^3`. -/
theorem gnomonicBase_subset_cube (t : ℝ) :
    GnomonicBase t ⊆ {u : EuclideanSpace ℝ (Fin 3) |
      -t ≤ u 0 ∧ u 0 ≤ t ∧
      -t ≤ u 1 ∧ u 1 ≤ t ∧
      -t ≤ u 2 ∧ u 2 ≤ t} := by
  intro u hu
  exact canonicalCone_base_bounds hu

/-- The Euclidean gnomonic tetrahedra are nested for increasing t. -/
theorem gnomonicBase_mono {t s : ℝ} (ht : 0 < t) (h : t ≤ s) :
    GnomonicBase t ⊆ GnomonicBase s := by
  intro u hu
  exact canonicalCone_mono ht h hu

/-- There is an interior point of the larger gnomonic tetrahedron
strictly outside the smaller one. -/
theorem gnomonicBase_strict_witness {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ a b c : ℝ,
      CanonicalConeInterior s a b c 1 ∧
      ¬ CanonicalCone t a b c 1 := by
  exact ⟨-(t + s) / 6, -(t + s) / 6, -(t + s) / 6, by
    dsimp [CanonicalConeInterior]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hts, ht], by
    intro h
    have hh := h.1
    nlinarith [hts]⟩

end Sphere3
