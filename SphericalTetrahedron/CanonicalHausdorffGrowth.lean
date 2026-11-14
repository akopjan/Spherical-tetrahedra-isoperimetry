module

public import SphericalTetrahedron.RegularReduction
public import Sphere3.GnomonicHausdorffFiniteness

@[expose] public section

/-!
# Strict growth of genuine Hausdorff volume on the regular family

The canonical tetrahedron defined using the original `SphericalTetrahedron`
structure has exactly the body `Sphere3.canonicalSphereBody t`. Strict growth
of the genuine 3-dimensional Hausdorff measure was proved in
`Sphere3.GnomonicHausdorffFiniteness` using an open projected patch and a
Lipschitz parametrization of a compact simplex.

This proof no longer assumes a polar measure conversion or a normalization
constant. The corresponding strict area monotonicity comparison is completed in
`CanonicalFaceHausdorffStrict`.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Canonical regular tetrahedra strictly increase in their *actual*
challenge volume (not a substitute angular or Lebesgue measure). -/
theorem canonicalTetrahedron_volume_strict
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (canonicalTetrahedron t ht).volume <
      (canonicalTetrahedron s (lt_trans ht hts)).volume := by
  rw [canonicalTetrahedron_volume_eq t ht,
    canonicalTetrahedron_volume_eq s (lt_trans ht hts)]
  exact Sphere3.canonicalSphereBody_real_volume_strict ht hts

/-- If the single remaining regular-area formula holds, the original
regular-family monotonicity theorem follows with no additional analytic
assumptions. In particular, a scaled polar identity is no longer needed. -/
theorem regular_area_lt_volume_lt_of_area_formula
    (κ : ℝ) (hκ : 0 < κ)
    (hArea : ∀ (T : SphericalTetrahedron), T.Regular →
      ∀ (ρ : ℝ),
        (∀ i j : Fin 4, i ≠ j →
          ⟪T.normal i, T.normal j⟫_ℝ = ρ) →
        T.area = κ * Sphere3.regularAreaModel ρ)
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area < S.area) :
    R.volume < S.volume := by
  have hCanonicalArea : ∀ (t : ℝ) (ht : 0 < t),
      (canonicalTetrahedron t ht).area =
        κ * Sphere3.canonicalAreaModel t := by
    intro t ht
    have hGram : ∀ i j : Fin 4, i ≠ j →
      ⟪(canonicalTetrahedron t ht).normal i,
        (canonicalTetrahedron t ht).normal j⟫_ℝ =
          Sphere3.canonicalGramParameter t := by
      intro i j hij
      exact canonicalUnitNormal_inner_offdiag t i j hij
    rw [Sphere3.canonicalAreaModel_eq_regular]
    exact hArea (canonicalTetrahedron t ht)
      (canonicalTetrahedron_regular t ht)
      (Sphere3.canonicalGramParameter t) hGram
  have hCanonicalVolume : ∀ (t s : ℝ)
      (ht : 0 < t) (hs : 0 < s), t < s →
      (canonicalTetrahedron t ht).volume <
        (canonicalTetrahedron s hs).volume := by
    intro t s ht hs hts
    exact canonicalTetrahedron_volume_strict ht hts
  exact regular_area_lt_volume_lt_of_canonical_data
    κ hκ hCanonicalArea hCanonicalVolume R S hR hS hA

end SphericalTetrahedron
