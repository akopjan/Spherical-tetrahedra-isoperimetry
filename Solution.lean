module

/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
public import SphericalTetrahedron.CanonicalFaceHausdorffStrict
public import Sphere3
public import SphericalTetrahedron
public import SphericalTetrahedronManuscript

@[expose] public section

/-!
# Isoperimetric Inequality for Spherical Tetrahedra

The foundational definitions and congruence facts have been extracted to
`SolutionCore.lean` to make the canonical Hausdorff-measure comparison
available without a cyclic module import.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators
open SphericalTetrahedron

/-- Existence of a nondegenerate fixed-area volume maximizer. -/
theorem fixed_area_maximizer_exists (T : SphericalTetrahedron) :
    ∃ M : SphericalTetrahedron,
      M.area = T.area ∧
      (∀ S : SphericalTetrahedron, S.area = T.area → S.volume ≤ M.volume) := by
  exact fixed_area_maximizer_exists_manuscript T

/-- First variation and the Lagrange multiplier equation. -/
theorem volume_maximizer_is_stationary (M : SphericalTetrahedron)
    (hMax : ∀ S : SphericalTetrahedron, S.area = M.area → S.volume ≤ M.volume) :
    M.Stationary := by
  exact volume_maximizer_is_stationary_manuscript M hMax

/-- The triangle ordering lemma implies rigidity of stationary tetrahedra. -/
theorem stationary_tetrahedron_regular (M : SphericalTetrahedron)
    (h : M.Stationary) : M.Regular := by
  exact M.stationary_regular_manuscript h


/-- Strict growth for the two-dimensional Hausdorff area of one canonical
regular face, assembled in `CanonicalFaceHausdorffStrict.lean`. -/
theorem canonical_first_face_strict :
    SphericalTetrahedron.CanonicalFirstFaceStrict := by
  exact SphericalTetrahedron.canonicalFirstFaceStrict_from_open_patch

/-- Strict genuine-area/genuine-volume growth on the regular family follows
from strict Hausdorff area growth of one canonical face.  No normalization
constant or spherical-excess theorem is required. -/
theorem regular_area_lt_volume_lt (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area < S.area) :
    R.volume < S.volume := by
  exact SphericalTetrahedron.regular_area_lt_volume_lt_of_first_face_growth
    canonical_first_face_strict R S hR hS hA

/-- Strict ordering along the regular family implies that equal volumes
    force equal areas.  Only the geometric monotonicity theorem above is used. -/
theorem regular_same_volume_same_area (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular)
    (hV : R.volume = S.volume) : R.area = S.area := by
  rcases lt_trichotomy R.area S.area with hLt | hEq | hGt
  · have hv := regular_area_lt_volume_lt R S hR hS hLt
    exact False.elim (hv.ne hV)
  · exact hEq
  · have hv := regular_area_lt_volume_lt S R hS hR hGt
    exact False.elim (hv.ne hV.symm)


/-- Two regular tetrahedra of the same area are congruent, provided
that their true (UNNORMALIZED) Hausdorff surface area is a fixed positive
multiple of the intrinsic spherical area model.  A scale factor is
necessary: mathlib distinguishes `hausdorffMeasure` from the normalized
`euclideanHausdorffMeasure`.  This lemma does NOT prove that identification. -/
theorem regular_same_area_congruent_of_scaled_area_formula
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular)
    (hArea : R.area = S.area)
    (κ : ℝ) (hκ : 0 < κ)
    (hFormulaR : ∀ ρ : ℝ,
      (∀ i j : Fin 4, i ≠ j →
        ⟪R.normal i, R.normal j⟫_ℝ = ρ) →
      R.area = κ * Sphere3.regularAreaModel ρ)
    (hFormulaS : ∀ ρ : ℝ,
      (∀ i j : Fin 4, i ≠ j →
        ⟪S.normal i, S.normal j⟫_ℝ = ρ) →
      S.area = κ * Sphere3.regularAreaModel ρ) :
    R.Congruent S := by
  obtain ⟨ρ, hρ, hRρ⟩ := regular_has_parameter R hR
  obtain ⟨σ, hσ, hSσ⟩ := regular_has_parameter S hS
  have hscaled : κ * Sphere3.regularAreaModel ρ =
      κ * Sphere3.regularAreaModel σ := by
    calc
      κ * Sphere3.regularAreaModel ρ = R.area := (hFormulaR ρ hRρ).symm
      _ = S.area := hArea
      _ = κ * Sphere3.regularAreaModel σ := hFormulaS σ hSσ
  have hmodel : Sphere3.regularAreaModel ρ =
      Sphere3.regularAreaModel σ :=
    mul_left_cancel₀ (ne_of_gt hκ) hscaled
  have hρσ : ρ = σ := Sphere3.regularAreaModel_injOn hρ hσ hmodel
  subst σ
  exact regular_same_parameter_congruent R S ρ hRρ hSσ

/-- Strict growth of one canonical face determines the entire
congruence class of a regular tetrahedron by its true Hausdorff area. -/
theorem regular_same_area_congruent (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area = S.area) :
    R.Congruent S := by
  exact SphericalTetrahedron.regular_same_area_congruent_of_first_face_growth
    canonical_first_face_strict R S hR hS hA

/-- Equal area on the regular family forces equal volume via `regular_same_area_congruent`. -/
theorem regular_same_area_same_volume (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hA : R.area = S.area) :
    R.volume = S.volume := by
  exact congruent_tetrahedron_equal_volume R S
    (regular_same_area_congruent R S hR hS hA)

/-- Equal volume gives equal area by strict monotonicity, which then
    determines the congruence class by `regular_same_area_congruent`. -/
theorem regular_same_volume_congruent (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular) (hV : R.volume = S.volume) :
    R.Congruent S := by
  apply regular_same_area_congruent R S hR hS
  exact regular_same_volume_same_area R S hR hS hV

/-- Equality of areas on the regular family forces equality of volumes
once the common positive normalization of spherical face area is known. -/
theorem regular_same_area_same_volume_of_scaled_area_formula
    (R S : SphericalTetrahedron)
    (hR : R.Regular) (hS : S.Regular)
    (hArea : R.area = S.area)
    (κ : ℝ) (hκ : 0 < κ)
    (hFormulaR : ∀ ρ : ℝ,
      (∀ i j : Fin 4, i ≠ j →
        ⟪R.normal i, R.normal j⟫_ℝ = ρ) →
      R.area = κ * Sphere3.regularAreaModel ρ)
    (hFormulaS : ∀ ρ : ℝ,
      (∀ i j : Fin 4, i ≠ j →
        ⟪S.normal i, S.normal j⟫_ℝ = ρ) →
      S.area = κ * Sphere3.regularAreaModel ρ) :
    R.volume = S.volume := by
  exact congruent_tetrahedron_equal_volume R S
    (regular_same_area_congruent_of_scaled_area_formula
      R S hR hS hArea κ hκ hFormulaR hFormulaS)


theorem regular_fixed_area_maximizer (T : SphericalTetrahedron) :
    ∃ M : SphericalTetrahedron,
      M.Regular ∧ M.area = T.area ∧
      (∀ S : SphericalTetrahedron, S.area = T.area → S.volume ≤ M.volume) := by
  obtain ⟨M, hArea, hMax⟩ := fixed_area_maximizer_exists T
  have hMaxM : ∀ S : SphericalTetrahedron, S.area = M.area → S.volume ≤ M.volume := by
    intro S hSM
    exact hMax S (hSM.trans hArea)
  have hStat : M.Stationary := volume_maximizer_is_stationary M hMaxM
  refine ⟨M, stationary_tetrahedron_regular M hStat, hArea, hMax⟩

theorem area_minimal
    (T R : SphericalTetrahedron) (hReg : R.Regular)
    (hVol : T.volume = R.volume) :
    R.area ≤ T.area := by
  obtain ⟨M, hMReg, hMArea, hMax⟩ := regular_fixed_area_maximizer T
  by_contra hNot
  have hMAreaLt : M.area < R.area := by
    rw [hMArea]
    exact lt_of_not_ge hNot
  have hMVolLt : M.volume < R.volume :=
    regular_area_lt_volume_lt M R hMReg hReg hMAreaLt
  have hTVolLe : T.volume ≤ M.volume := hMax T rfl
  have hRVolLe : R.volume ≤ M.volume := by
    rw [← hVol]
    exact hTVolLe
  exact (not_lt_of_ge hRVolLe) hMVolLt

theorem regular_of_area_equality
    (T R : SphericalTetrahedron) (hReg : R.Regular)
    (hVol : T.volume = R.volume)
    (hArea : T.area = R.area) :
    T.Regular := by
  obtain ⟨M, hMReg, hMArea, hMax⟩ := regular_fixed_area_maximizer T
  have hMRarea : M.area = R.area := hMArea.trans hArea
  have hMRvol : M.volume = R.volume :=
    regular_same_area_same_volume M R hMReg hReg hMRarea
  have hMaxT : ∀ S : SphericalTetrahedron, S.area = T.area → S.volume ≤ T.volume := by
    intro S hSA
    calc
      S.volume ≤ M.volume := hMax S hSA
      _ = R.volume := hMRvol
      _ = T.volume := hVol.symm
  exact stationary_tetrahedron_regular T (volume_maximizer_is_stationary T hMaxT)

/-- Conditional on a given regular spherical tetrahedron `R` having the same
volume (`T.volume = R.volume`), `R` uniquely minimizes total surface area up to
congruence, with `volume` and `area` measured by Mathlib's unnormalized
`Measure.hausdorffMeasure`. -/
theorem isoperimetric_area
    (T R : SphericalTetrahedron)
    (hReg : R.Regular) (hV : T.volume = R.volume) :
    R.area ≤ T.area ∧
      (T.area = R.area ↔ T.Congruent R) := by
  constructor
  · exact area_minimal T R hReg hV
  · constructor
    · intro hArea
      have hTReg := regular_of_area_equality T R hReg hV hArea
      exact regular_same_volume_congruent T R hTReg hReg hV
    · intro hCongr
      exact congruent_tetrahedron_equal_area T R hCongr

theorem volume_maximal
    (T R : SphericalTetrahedron) (hReg : R.Regular)
    (hArea : T.area = R.area) :
    T.volume ≤ R.volume := by
  obtain ⟨M, hMReg, hMArea, hMax⟩ := regular_fixed_area_maximizer T
  have hMRarea : M.area = R.area := hMArea.trans hArea
  have hMRvol : M.volume = R.volume :=
    regular_same_area_same_volume M R hMReg hReg hMRarea
  have hTleM : T.volume ≤ M.volume := hMax T rfl
  rw [← hMRvol]
  exact hTleM

theorem regular_of_volume_equality
    (T R : SphericalTetrahedron) (hReg : R.Regular)
    (hArea : T.area = R.area)
    (hVol : T.volume = R.volume) :
    T.Regular := by
  obtain ⟨M, hMReg, hMArea, hMax⟩ := regular_fixed_area_maximizer T
  have hMRarea : M.area = R.area := hMArea.trans hArea
  have hMRvol : M.volume = R.volume :=
    regular_same_area_same_volume M R hMReg hReg hMRarea
  have hMaxT : ∀ S : SphericalTetrahedron, S.area = T.area → S.volume ≤ T.volume := by
    intro S hSA
    calc
      S.volume ≤ M.volume := hMax S hSA
      _ = R.volume := hMRvol
      _ = T.volume := hVol.symm
  exact stationary_tetrahedron_regular T (volume_maximizer_is_stationary T hMaxT)

/-- Conditional on a given regular spherical tetrahedron `R` having the same
surface area (`T.area = R.area`), `R` uniquely maximizes volume up to
congruence, with `volume` and `area` measured by Mathlib's unnormalized
`Measure.hausdorffMeasure`. -/
theorem isoperimetric_volume
    (T R : SphericalTetrahedron)
    (hR : R.Regular) (hA : T.area = R.area) :
    T.volume ≤ R.volume ∧
      (T.volume = R.volume ↔ T.Congruent R) := by
  constructor
  · exact volume_maximal T R hR hA
  · constructor
    · intro hVol
      have hTReg : T.Regular := regular_of_volume_equality T R hR hA hVol
      exact regular_same_volume_congruent T R hTReg hR hVol
    · intro hCongr
      exact congruent_tetrahedron_equal_volume T R hCongr
