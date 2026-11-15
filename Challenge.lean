module

/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
public import Mathlib

@[expose] public section

/-!
# Isoperimetric Inequality for Spherical Tetrahedra

Conditional isoperimetric comparisons for geodesic tetrahedra in the unit
three-sphere: given a regular spherical tetrahedron `R` with the same
Hausdorff volume (`T.volume = R.volume`) or surface area (`T.area = R.area`),
`R` uniquely minimizes surface area at fixed volume and uniquely maximizes
volume at fixed surface area up to congruence. Here `volume` and `area` are
defined using Mathlib's unnormalized `Measure.hausdorffMeasure` on `E4`.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A nondegenerate spherical tetrahedron, represented by its inward unit normals. -/
structure SphericalTetrahedron where
  normal : Fin 4 → E4
  unit : ∀ i, ‖normal i‖ = 1
  independent : LinearIndependent ℝ normal

namespace SphericalTetrahedron

/-- The intersection of four hemispheres in `S³`. -/
def body (T : SphericalTetrahedron) : Set E4 :=
  {x | ‖x‖ = 1 ∧ ∀ i, 0 ≤ ⟪T.normal i, x⟫_ℝ}

/-- The face opposite to the `i`-th vertex. -/
def face (T : SphericalTetrahedron) (i : Fin 4) : Set E4 :=
  {x ∈ T.body | ⟪T.normal i, x⟫_ℝ = 0}

/-- The `d`-dimensional Hausdorff measure of a set. -/
def measure (d : ℝ) (s : Set E4) : ℝ :=
  ((Measure.hausdorffMeasure d) s).toReal

/-- Spherical volume. -/
def volume (T : SphericalTetrahedron) : ℝ :=
  measure 3 T.body

/-- Total surface area. -/
def area (T : SphericalTetrahedron) : ℝ :=
  ∑ i : Fin 4, measure 2 (T.face i)

/-- Regularity: all pairwise angles between facet normals are equal. -/
def Regular (T : SphericalTetrahedron) : Prop :=
  ∃ c : ℝ, ∀ i j, i ≠ j →
    ⟪T.normal i, T.normal j⟫_ℝ = c

/-- Congruence up to an orthogonal transformation and relabeling. -/
def Congruent (T R : SphericalTetrahedron) : Prop :=
  ∃ (U : E4 ≃ₗᵢ[ℝ] E4) (σ : Equiv.Perm (Fin 4)),
    ∀ i, T.normal (σ i) = U (R.normal i)

end SphericalTetrahedron

open SphericalTetrahedron

/-- Conditional on a given regular spherical tetrahedron `R` having the same
volume (`T.volume = R.volume`), `R` uniquely minimizes total surface area up to
congruence, with `volume` and `area` measured by Mathlib's unnormalized
`Measure.hausdorffMeasure`. -/
theorem isoperimetric_area
    (T R : SphericalTetrahedron)
    (hR : R.Regular) (hV : T.volume = R.volume) :
    R.area ≤ T.area ∧ (T.area = R.area ↔ T.Congruent R) := by
  sorry

/-- Conditional on a given regular spherical tetrahedron `R` having the same
surface area (`T.area = R.area`), `R` uniquely maximizes volume up to
congruence, with `volume` and `area` measured by Mathlib's unnormalized
`Measure.hausdorffMeasure`. -/
theorem isoperimetric_volume
    (T R : SphericalTetrahedron)
    (hR : R.Regular) (hA : T.area = R.area) :
    T.volume ≤ R.volume ∧ (T.volume = R.volume ↔ T.Congruent R) := by
  sorry
