module

public import SphericalTetrahedron.RegularFaceSymmetry
public import Sphere3.CanonicalHausdorff
public import Sphere3.CanonicalArea
public import Sphere3.CanonicalLebesgue

@[expose] public section

/-!
# Reduction of regular-family geometry to a single canonical family

Every regular spherical tetrahedron is orthogonally congruent to an explicit
`canonicalTetrahedron t ht` at a unique positive scale. Consequently the
regular-family `area` and `volume` comparisons can be checked on a single
family of actual tetrahedra rather than on arbitrary four-tuples of normals.

It expresses the canonical-family measure monotonicity hypotheses explicitly;
these are supplied in `Sphere3.GnomonicHausdorffFiniteness` and
`SphericalTetrahedron.CanonicalFaceHausdorffStrict`.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Every regular nondegenerate spherical tetrahedron is congruent to
one member of the explicit canonical family, with equality of the two
measure invariants. -/
theorem regular_congruent_canonical (T : SphericalTetrahedron)
    (hReg : T.Regular) :
    ∃ (t : ℝ) (ht : 0 < t),
      T.Congruent (canonicalTetrahedron t ht) ∧
      T.area = (canonicalTetrahedron t ht).area ∧
      T.volume = (canonicalTetrahedron t ht).volume := by
  obtain ⟨rho, hrho, hT⟩ := regular_has_parameter T hReg
  let t : ℝ := Sphere3.canonicalScale rho
  have ht : 0 < t := Sphere3.canonicalScale_pos rho hrho
  have hparam : Sphere3.canonicalGramParameter t = rho :=
    Sphere3.canonicalGramParameter_canonicalScale rho hrho
  have hC : ∀ i j : Fin 4, i ≠ j →
      ⟪(canonicalTetrahedron t ht).normal i,
        (canonicalTetrahedron t ht).normal j⟫_ℝ = rho := by
    intro i j hij
    change ⟪canonicalUnitNormal t i, canonicalUnitNormal t j⟫_ℝ = rho
    exact (canonicalUnitNormal_inner_offdiag t i j hij).trans hparam
  have hcong : T.Congruent (canonicalTetrahedron t ht) :=
    regular_same_parameter_congruent T (canonicalTetrahedron t ht) rho hT hC
  exact ⟨t, ht, hcong,
    congruent_tetrahedron_equal_area T (canonicalTetrahedron t ht) hcong,
    congruent_tetrahedron_equal_volume T (canonicalTetrahedron t ht) hcong⟩

/-- Strict Hausdorff-volume growth in the canonical family, conditional
only on finiteness and a positive measure of the difference. The latter
are genuine measure claims, not consequences of mere nonemptiness. -/
theorem canonicalTetrahedron_volume_lt_of_positive_patch
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hFinT : (Measure.hausdorffMeasure (3 : ℝ))
        (Sphere3.canonicalSphereBody t) ≠ ⊤)
    (hFinS : (Measure.hausdorffMeasure (3 : ℝ))
        (Sphere3.canonicalSphereBody s) ≠ ⊤)
    (hPos : 0 < (Measure.hausdorffMeasure (3 : ℝ))
        (Sphere3.canonicalSphereBody s \ Sphere3.canonicalSphereBody t)) :
    (canonicalTetrahedron t ht).volume <
      (canonicalTetrahedron s (lt_trans ht hts)).volume := by
  have hMeas : MeasurableSet (Sphere3.canonicalSphereBody t) := by
    rw [← canonicalTetrahedron_body_eq t ht]
    exact (canonicalTetrahedron t ht).body_measurableSet
  have hMeasure := Sphere3.canonicalSphereBody_measure_lt_of_patch
    ht hts hMeas hFinT hPos
  rw [canonicalTetrahedron_volume_eq t ht,
    canonicalTetrahedron_volume_eq s (lt_trans ht hts)]
  exact ENNReal.toReal_strict_mono hFinS hMeasure

/-- A common, positive Hausdorff normalization on the canonical family
extends the face-area formula to every regular tetrahedron. -/
theorem regular_area_formula_of_canonical_area_formula
    (κ : ℝ) (hκ : 0 < κ)
    (hArea : ∀ (t : ℝ) (ht : 0 < t),
      (canonicalTetrahedron t ht).area =
        κ * Sphere3.canonicalAreaModel t) :
    ∀ T : SphericalTetrahedron, T.Regular →
      ∀ rho : ℝ,
        (∀ i j : Fin 4, i ≠ j →
          ⟪T.normal i, T.normal j⟫_ℝ = rho) →
        T.area = κ * Sphere3.regularAreaModel rho := by
  intro T hReg rho hGram
  have hrho : rho ∈ Sphere3.regularParameterDomain :=
    regular_parameter_mem T rho hGram
  let t : ℝ := Sphere3.canonicalScale rho
  have ht : 0 < t := Sphere3.canonicalScale_pos rho hrho
  have hparam : Sphere3.canonicalGramParameter t = rho :=
    Sphere3.canonicalGramParameter_canonicalScale rho hrho
  have hCanonical : ∀ i j : Fin 4, i ≠ j →
      ⟪(canonicalTetrahedron t ht).normal i,
        (canonicalTetrahedron t ht).normal j⟫_ℝ = rho := by
    intro i j hij
    change ⟪canonicalUnitNormal t i, canonicalUnitNormal t j⟫_ℝ = rho
    exact (canonicalUnitNormal_inner_offdiag t i j hij).trans hparam
  have hEq : T.area = (canonicalTetrahedron t ht).area :=
    (regular_same_parameter_equal_measurements
      T (canonicalTetrahedron t ht) rho hGram hCanonical).1
  calc
    T.area = (canonicalTetrahedron t ht).area := hEq
    _ = κ * Sphere3.canonicalAreaModel t := hArea t ht
    _ = κ * Sphere3.regularAreaModel rho := by
      rw [Sphere3.canonicalAreaModel_eq_regular, hparam]

/-- The true canonical surface area is determined by the measure
of any one canonical face, by normal-Gram symmetry. -/
theorem canonical_area_formula_of_single_face
    (κ : ℝ)
    (hFace : ∀ (t : ℝ) (ht : 0 < t),
      measure 2
        ((canonicalTetrahedron t ht).face (0 : Fin 4)) =
          κ * (3 * Real.arccos (Sphere3.canonicalFaceCos t) - Real.pi))
    (t : ℝ) (ht : 0 < t) :
    (canonicalTetrahedron t ht).area = κ * Sphere3.canonicalAreaModel t := by
  have hReg : (canonicalTetrahedron t ht).Regular :=
    canonicalTetrahedron_regular t ht
  calc
    (canonicalTetrahedron t ht).area =
        4 * measure 2
          ((canonicalTetrahedron t ht).face (0 : Fin 4)) :=
      regular_area_eq_four_face (canonicalTetrahedron t ht) hReg 0
    _ = 4 * (κ * (3 * Real.arccos (Sphere3.canonicalFaceCos t) -
          Real.pi)) := by rw [hFace t ht]
    _ = κ * Sphere3.canonicalAreaModel t := by
      unfold Sphere3.canonicalAreaModel
      ring

/-- To prove the true regular-surface-area formula it suffices to
identify the Hausdorff measure of just *one* canonical face.  Equality
of the other three face measures has already been proved by isometry. -/
theorem regular_area_formula_of_one_canonical_face
    (κ : ℝ) (hκ : 0 < κ)
    (hFace : ∀ (t : ℝ) (ht : 0 < t),
      measure 2
          ((canonicalTetrahedron t ht).face (0 : Fin 4)) =
        κ * (3 * Real.arccos (Sphere3.canonicalFaceCos t) - Real.pi)) :
    ∀ T : SphericalTetrahedron, T.Regular →
      ∀ rho : ℝ,
        (∀ i j : Fin 4, i ≠ j →
          ⟪T.normal i, T.normal j⟫_ℝ = rho) →
        T.area = κ * Sphere3.regularAreaModel rho := by
  apply regular_area_formula_of_canonical_area_formula κ hκ
  exact canonical_area_formula_of_single_face κ hFace

/-- Conditional reduction of the geometric regular-family monotonicity
to the canonical area identification and strict canonical volume growth.
The two quantified hypotheses are exactly the remaining analytic tasks. -/
theorem regular_area_lt_volume_lt_of_canonical_data
    (κ : ℝ) (hκ : 0 < κ)
    (hArea : ∀ (t : ℝ) (ht : 0 < t),
      (canonicalTetrahedron t ht).area =
        κ * Sphere3.canonicalAreaModel t)
    (hVolumeStrict : ∀ (t s : ℝ) (ht : 0 < t) (hs : 0 < s),
      t < s →
        (canonicalTetrahedron t ht).volume <
          (canonicalTetrahedron s hs).volume)
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area < S.area) :
    R.volume < S.volume := by
  obtain ⟨t, ht, hRC, hRArea, hRVolume⟩ := regular_congruent_canonical R hR
  obtain ⟨s, hs, hSC, hSArea, hSVolume⟩ := regular_congruent_canonical S hS
  have hModel : Sphere3.canonicalAreaModel t <
      Sphere3.canonicalAreaModel s := by
    apply lt_of_mul_lt_mul_left _ hκ.le
    calc
      κ * Sphere3.canonicalAreaModel t = (canonicalTetrahedron t ht).area :=
        (hArea t ht).symm
      _ = R.area := hRArea.symm
      _ < S.area := hA
      _ = (canonicalTetrahedron s hs).area := hSArea
      _ = κ * Sphere3.canonicalAreaModel s := hArea s hs
  have hts : t < s := by
    rcases lt_trichotomy t s with hlt | heq | hgt
    · exact hlt
    · subst s
      exact False.elim (lt_irrefl _ hModel)
    · have hreverse : Sphere3.canonicalAreaModel s <
          Sphere3.canonicalAreaModel t :=
        Sphere3.canonicalAreaModel_strictMonoOn hs ht hgt
      exact False.elim (lt_asymm hModel hreverse)
  calc
    R.volume = (canonicalTetrahedron t ht).volume := hRVolume
    _ < (canonicalTetrahedron s hs).volume :=
      hVolumeStrict t s ht hs hts
    _ = S.volume := hSVolume.symm

/-- A fixed multiplicative polar normalization gives strict monotonicity
of the genuine spherical Hausdorff volume on the explicit family.
Finiteness of the larger body must be proved separately to transport
strict inequality from `ENNReal` through `.toReal`. -/
theorem canonicalTetrahedron_volume_lt_of_scaled_polar
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (K : ENNReal)
    (hPolar : ∀ u : ℝ, 0 < u →
      (MeasureTheory.volume : Measure E4) (Sphere3.canonicalTruncatedCone u) =
        K * (Measure.hausdorffMeasure (3 : ℝ))
            (Sphere3.canonicalSphereBody u))
    (hFinS : (Measure.hausdorffMeasure (3 : ℝ))
        (Sphere3.canonicalSphereBody s) ≠ ⊤) :
    (canonicalTetrahedron t ht).volume <
      (canonicalTetrahedron s (lt_trans ht hts)).volume := by
  have hStrict :
      (Measure.hausdorffMeasure (3 : ℝ)) (Sphere3.canonicalSphereBody t) <
        (Measure.hausdorffMeasure (3 : ℝ)) (Sphere3.canonicalSphereBody s) :=
    Sphere3.canonicalSphereBody_hausdorff_strict_of_scaled_polar
      ht hts K hPolar
  rw [canonicalTetrahedron_volume_eq t ht,
    canonicalTetrahedron_volume_eq s (lt_trans ht hts)]
  exact ENNReal.toReal_strict_mono hFinS hStrict

/-- Two explicit analytic inputs suffice for monotonicity of true
spherical volumes on the whole regular family: (a) a common positive
Hausdorff normalization of one face, and (b) a scaled polar identity
with finite 3-dimensional Hausdorff measure.  Neither input has yet
been established as an unconditional Lean theorem. -/
theorem regular_area_lt_volume_lt_of_one_face_and_scaled_polar
    (κ : ℝ) (hκ : 0 < κ)
    (hFace : ∀ (t : ℝ) (ht : 0 < t),
      measure 2
          ((canonicalTetrahedron t ht).face (0 : Fin 4)) =
        κ * (3 * Real.arccos (Sphere3.canonicalFaceCos t) - Real.pi))
    (K : ENNReal)
    (hPolar : ∀ u : ℝ, 0 < u →
      (MeasureTheory.volume : Measure E4) (Sphere3.canonicalTruncatedCone u) =
        K * (Measure.hausdorffMeasure (3 : ℝ))
            (Sphere3.canonicalSphereBody u))
    (hFin : ∀ u : ℝ, 0 < u →
      (Measure.hausdorffMeasure (3 : ℝ))
        (Sphere3.canonicalSphereBody u) ≠ ⊤)
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area < S.area) :
    R.volume < S.volume := by
  exact regular_area_lt_volume_lt_of_canonical_data κ hκ
    (canonical_area_formula_of_single_face κ hFace)
    (fun t s ht hs hts =>
      canonicalTetrahedron_volume_lt_of_scaled_polar ht hts K hPolar (hFin s hs))
    R S hR hS hA

end SphericalTetrahedron
