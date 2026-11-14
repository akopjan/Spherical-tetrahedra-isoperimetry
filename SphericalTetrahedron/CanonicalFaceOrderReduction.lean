module

public import SphericalTetrahedron.CanonicalHausdorffGrowth
public import Sphere3.CanonicalFaceScale

@[expose] public section

/-!
# Reduction from strict growth of one canonical face to the isoperimetric
# regular-family comparison and uniqueness

The angular-area/Girard formula is not logically required.  The much weaker
hypothesis below is the *strict increase of the actual Hausdorff measure of
one canonical face* under the positive canonical height parameter.

Strict growth of the actual canonical Hausdorff volume is already the
conclusion of `canonicalTetrahedron_volume_strict`.

These lemmas reduce regular-family monotonicity and uniqueness to the
strict growth of one canonical face.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- The real two-dimensional Hausdorff measure of the first canonical face.
This is the *original problem's measure*, not a spherical-excess model. -/
def canonicalFirstFaceArea (t : ℝ) (ht : 0 < t) : ℝ :=
  measure 2
    ((canonicalTetrahedron t ht).face (0 : Fin 4))

/-- An abstract geometric hypothesis: the actual Hausdorff area of one
canonical regular face strictly increases along the family. -/
def CanonicalFirstFaceStrict : Prop :=
  ∀ (t s : ℝ) (ht : 0 < t) (hs : 0 < s),
    t < s → canonicalFirstFaceArea t ht < canonicalFirstFaceArea s hs

/-- Strict Hausdorff area growth of one face implies strict growth of
all four faces, hence of the full surface area. -/
theorem canonicalTetrahedron_area_strict_of_first_face
    (hFace : CanonicalFirstFaceStrict)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hts : t < s) :
    (canonicalTetrahedron t ht).area <
      (canonicalTetrahedron s hs).area := by
  have hft : (canonicalTetrahedron t ht).Regular :=
    canonicalTetrahedron_regular t ht
  have hfs : (canonicalTetrahedron s hs).Regular :=
    canonicalTetrahedron_regular s hs
  rw [regular_area_eq_four_face (canonicalTetrahedron t ht) hft 0,
    regular_area_eq_four_face (canonicalTetrahedron s hs) hfs 0]
  exact mul_lt_mul_of_pos_left (hFace t s ht hs hts) (by norm_num)

/-- The desired strict regular-family area/volume implication follows
from strict genuine face-measure growth, without any Girard formula. -/
theorem regular_area_lt_volume_lt_of_first_face_growth
    (hFace : CanonicalFirstFaceStrict)
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area < S.area) :
    R.volume < S.volume := by
  obtain ⟨t, ht, _hRC, hRArea, hRVolume⟩ :=
    regular_congruent_canonical R hR
  obtain ⟨s, hs, _hSC, hSArea, hSVolume⟩ :=
    regular_congruent_canonical S hS
  have hCanonArea : (canonicalTetrahedron t ht).area <
      (canonicalTetrahedron s hs).area := by
    calc
      (canonicalTetrahedron t ht).area = R.area := hRArea.symm
      _ < S.area := hA
      _ = (canonicalTetrahedron s hs).area := hSArea
  have hts : t < s := by
    rcases lt_trichotomy t s with hlt | heq | hgt
    · exact hlt
    · subst s
      exact False.elim (lt_irrefl _ hCanonArea)
    · have hReverse :=
        canonicalTetrahedron_area_strict_of_first_face hFace s t hs ht hgt
      exact False.elim (lt_asymm hCanonArea hReverse)
  calc
    R.volume = (canonicalTetrahedron t ht).volume := hRVolume
    _ < (canonicalTetrahedron s hs).volume :=
      canonicalTetrahedron_volume_strict ht hts
    _ = S.volume := hSVolume.symm

/-- Equal surface areas of regular tetrahedra determine the normal
Gram parameter if a single canonical face grows strictly in area. -/
theorem regular_same_area_congruent_of_first_face_growth
    (hFace : CanonicalFirstFaceStrict)
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular)
    (hA : R.area = S.area) :
    R.Congruent S := by
  obtain ⟨ρ, hρ, hRρ⟩ := regular_has_parameter R hR
  obtain ⟨σ, hσ, hSσ⟩ := regular_has_parameter S hS
  let t : ℝ := Sphere3.canonicalScale ρ
  let s : ℝ := Sphere3.canonicalScale σ
  have ht : 0 < t := Sphere3.canonicalScale_pos ρ hρ
  have hs : 0 < s := Sphere3.canonicalScale_pos σ hσ
  have htParam : Sphere3.canonicalGramParameter t = ρ :=
    Sphere3.canonicalGramParameter_canonicalScale ρ hρ
  have hsParam : Sphere3.canonicalGramParameter s = σ :=
    Sphere3.canonicalGramParameter_canonicalScale σ hσ
  have hCGramR : ∀ i j : Fin 4, i ≠ j →
      ⟪(canonicalTetrahedron t ht).normal i,
        (canonicalTetrahedron t ht).normal j⟫_ℝ = ρ := by
    intro i j hij
    exact (canonicalUnitNormal_inner_offdiag t i j hij).trans htParam
  have hCGramS : ∀ i j : Fin 4, i ≠ j →
      ⟪(canonicalTetrahedron s hs).normal i,
        (canonicalTetrahedron s hs).normal j⟫_ℝ = σ := by
    intro i j hij
    exact (canonicalUnitNormal_inner_offdiag s i j hij).trans hsParam
  have hRArea : R.area = (canonicalTetrahedron t ht).area :=
    (regular_same_parameter_equal_measurements R
      (canonicalTetrahedron t ht) ρ hRρ hCGramR).1
  have hSArea : S.area = (canonicalTetrahedron s hs).area :=
    (regular_same_parameter_equal_measurements S
      (canonicalTetrahedron s hs) σ hSσ hCGramS).1
  have hEqual : (canonicalTetrahedron t ht).area =
      (canonicalTetrahedron s hs).area := by
    calc
      (canonicalTetrahedron t ht).area = R.area := hRArea.symm
      _ = S.area := hA
      _ = (canonicalTetrahedron s hs).area := hSArea
  have hts : t = s := by
    rcases lt_trichotomy t s with hlt | heq | hgt
    · have h := canonicalTetrahedron_area_strict_of_first_face
        hFace t s ht hs hlt
      exact False.elim (h.ne hEqual)
    · exact heq
    · have h := canonicalTetrahedron_area_strict_of_first_face
        hFace s t hs ht hgt
      exact False.elim (h.ne hEqual.symm)
  have hρσ : ρ = σ := by
    calc
      ρ = Sphere3.canonicalGramParameter t := htParam.symm
      _ = Sphere3.canonicalGramParameter s := congrArg _ hts
      _ = σ := hsParam
  rw [← hρσ] at hSσ
  exact regular_same_parameter_congruent R S ρ hRρ hSσ

end SphericalTetrahedron
