module

/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
public import Sphere3.GramCongruence
public import Sphere3.RegularGramBounds
public import Sphere3.RegularScale
public import Mathlib

@[expose] public section

/-!
# Isoperimetric Inequality for Spherical Tetrahedra

A formalization challenge: prove that the regular tetrahedron in `S³`
uniquely minimizes surface area at fixed volume, or equivalently,
maximizes volume at fixed surface area.
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

/-- The scalar kernel appearing in the edge first-variation equations:
    `ϕ(x) = (1 + x) * arccos(x) / √(1 - x²)`. -/
def stationaryKernel (x : ℝ) : ℝ :=
  (1 + x) * (Real.arccos x / Real.sqrt (1 - x ^ 2))

/-- The first-variation stationarity condition:
    There exist dual vertices `v i ∈ S³`, a dual vector `q ∈ ℝ⁴` with
    `⟨n i, q⟩ = 1`, and multiplier `c ≠ 0` such that
    `⟨q, v i⟩ + ⟨q, v j⟩ = c * ϕ(⟨v i, v j⟩)`. -/
def Stationary (T : SphericalTetrahedron) : Prop :=
  ∃ (v : Fin 4 → E4) (q : E4) (c : ℝ),
    c ≠ 0 ∧
    (∀ i : Fin 4, ‖v i‖ = 1) ∧
    (∀ i j : Fin 4, i ≠ j → ⟪T.normal i, v j⟫_ℝ = 0) ∧
    (∀ i : Fin 4, 0 < ⟪T.normal i, v i⟫_ℝ) ∧
    (∀ i : Fin 4, ⟪T.normal i, q⟫_ℝ = 1) ∧
    (∀ i j : Fin 4, i ≠ j →
      ⟪q, v i⟫_ℝ + ⟪q, v j⟫_ℝ =
        c * stationaryKernel ⟪v i, v j⟫_ℝ)

end SphericalTetrahedron

open SphericalTetrahedron

/-! ## Congruence, normal Gram parameter and exact geometric symmetry -/

/-- Equality of the normal Gram matrices implies congruence.  This
    reduces the geometric uniqueness problem to equality of a scalar Gram
    parameter in the regular family. -/
theorem congruent_of_equal_normal_gram (T R : SphericalTetrahedron)
    (hGram : ∀ i j : Fin 4,
      ⟪T.normal i, T.normal j⟫_ℝ = ⟪R.normal i, R.normal j⟫_ℝ) :
    T.Congruent R := by
  obtain ⟨U, hU⟩ := Sphere3.orthogonal_equiv_of_equal_gram
    R.normal T.normal R.independent T.independent
    (fun i j => (hGram i j).symm)
  refine ⟨U, Equiv.refl (Fin 4), ?_⟩
  intro i
  simpa using (hU i).symm

/-- The common off-diagonal normal inner product of a regular
    spherical tetrahedron is necessarily in `(-1/3, 1)`. -/
theorem regular_parameter_mem (T : SphericalTetrahedron) (rho : ℝ)
    (h : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho) :
    rho ∈ Sphere3.regularParameterDomain := by
  exact Sphere3.regularGramParameter_mem T.normal T.independent T.unit rho h

/-- Every regular tetrahedron has a common Gram parameter in the
    admissible interval. -/
theorem regular_has_parameter (T : SphericalTetrahedron)
    (h : T.Regular) :
    ∃ rho ∈ Sphere3.regularParameterDomain,
      ∀ i j : Fin 4, i ≠ j →
        ⟪T.normal i, T.normal j⟫_ℝ = rho := by
  rcases h with ⟨rho, hrho⟩
  exact ⟨rho, regular_parameter_mem T rho hrho, hrho⟩

/-- The common off-diagonal Gram parameter of a regular tetrahedron
    is uniquely determined by its four inward unit normals. -/
theorem regular_parameter_unique (T : SphericalTetrahedron)
    (rho sigma : ℝ)
    (hrho : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (hsigma : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = sigma) :
    rho = sigma := by
  have hij : (0 : Fin 4) ≠ 1 := by decide
  calc
    rho = ⟪T.normal 0, T.normal 1⟫_ℝ := (hrho 0 1 hij).symm
    _ = sigma := hsigma 0 1 hij

/-- Two regular tetrahedra with the same common off-diagonal normal
    inner product are congruent. -/
theorem regular_same_parameter_congruent (T R : SphericalTetrahedron)
    (ρ : ℝ)
    (hT : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = ρ)
    (hR : ∀ i j : Fin 4, i ≠ j →
      ⟪R.normal i, R.normal j⟫_ℝ = ρ) :
    T.Congruent R := by
  apply congruent_of_equal_normal_gram T R
  intro i j
  by_cases hij : i = j
  · subst j
    calc
      ⟪T.normal i, T.normal i⟫_ℝ = ‖T.normal i‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      _ = (1 : ℝ) := by rw [T.unit i]; norm_num
      _ = ‖R.normal i‖ ^ 2 := by rw [R.unit i]; norm_num
      _ = ⟪R.normal i, R.normal i⟫_ℝ :=
        (real_inner_self_eq_norm_sq _).symm
  · rw [hT i j hij, hR i j hij]

/-- Congruence preserves three-dimensional spherical Hausdorff volume. -/
theorem congruent_tetrahedron_equal_volume (T R : SphericalTetrahedron)
    (h : T.Congruent R) : T.volume = R.volume := by
  rcases h with ⟨U, σ, hU⟩
  dsimp [SphericalTetrahedron.volume, SphericalTetrahedron.measure]
  have h_img : T.body = (LinearIsometryEquiv.toIsometryEquiv U) '' R.body := by
    ext x
    constructor
    · intro ⟨hx_norm, hx_pos⟩
      refine ⟨U.symm x, ⟨?_, ?_⟩, ?_⟩
      · rw [← U.norm_map (U.symm x), U.apply_symm_apply x, hx_norm]
      · intro i
        have h1 := hx_pos (σ i)
        rw [hU i] at h1
        have h_inn : ⟪U (R.normal i), x⟫_ℝ = ⟪R.normal i, U.symm x⟫_ℝ := by
          have := (LinearIsometryEquiv.inner_map_map U.symm (U (R.normal i)) x).symm
          rw [U.symm_apply_apply] at this
          exact this
        rw [h_inn] at h1
        exact h1
      · exact U.apply_symm_apply x
    · rintro ⟨y, ⟨hy_norm, hy_pos⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change ‖U y‖ = 1
        rw [U.norm_map y, hy_norm]
      · intro i
        obtain ⟨j, hj⟩ : ∃ j, σ j = i := σ.surjective i
        subst hj
        rw [hU j]
        change 0 ≤ ⟪U (R.normal j), U y⟫_ℝ
        rw [LinearIsometryEquiv.inner_map_map]
        exact hy_pos j
  rw [h_img]
  rw [(LinearIsometryEquiv.toIsometryEquiv U).hausdorffMeasure_image 3 R.body]

theorem congruent_tetrahedron_image_face (T R : SphericalTetrahedron)
    (U : E4 ≃ₗᵢ[ℝ] E4) (σ : Equiv.Perm (Fin 4))
    (hU : ∀ i, T.normal (σ i) = U (R.normal i)) (i : Fin 4) :
    T.face (σ i) = (LinearIsometryEquiv.toIsometryEquiv U) '' R.face i := by
  ext x
  constructor
  · intro ⟨⟨hx_norm, hx_pos⟩, hx_face⟩
    refine ⟨U.symm x, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [← U.norm_map (U.symm x), U.apply_symm_apply x, hx_norm]
    · intro j
      have h1 := hx_pos (σ j)
      rw [hU j] at h1
      have h_inn : ⟪U (R.normal j), x⟫_ℝ = ⟪R.normal j, U.symm x⟫_ℝ := by
        have := (LinearIsometryEquiv.inner_map_map U.symm (U (R.normal j)) x).symm
        rw [U.symm_apply_apply] at this
        exact this
      rw [h_inn] at h1
      exact h1
    · rw [hU i] at hx_face
      have h_inn : ⟪U (R.normal i), x⟫_ℝ = ⟪R.normal i, U.symm x⟫_ℝ := by
        have := (LinearIsometryEquiv.inner_map_map U.symm (U (R.normal i)) x).symm
        rw [U.symm_apply_apply] at this
        exact this
      rw [h_inn] at hx_face
      exact hx_face
    · exact U.apply_symm_apply x
  · rintro ⟨y, ⟨⟨hy_norm, hy_pos⟩, hy_face⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ‖U y‖ = 1
      rw [U.norm_map y, hy_norm]
    · intro j
      obtain ⟨k, hk⟩ : ∃ k, σ k = j := σ.surjective j
      subst hk
      rw [hU k]
      change 0 ≤ ⟪U (R.normal k), U y⟫_ℝ
      rw [LinearIsometryEquiv.inner_map_map]
      exact hy_pos k
    · rw [hU i]
      change ⟪U (R.normal i), U y⟫_ℝ = 0
      rw [LinearIsometryEquiv.inner_map_map]
      exact hy_face

/-- Congruence preserves two-dimensional total surface area. -/
theorem congruent_tetrahedron_equal_area (T R : SphericalTetrahedron)
    (h : T.Congruent R) : T.area = R.area := by
  rcases h with ⟨U, σ, hU⟩
  dsimp [SphericalTetrahedron.area, SphericalTetrahedron.measure]
  have h_face (i : Fin 4) :
      (Measure.hausdorffMeasure 2 (T.face (σ i))).toReal =
      (Measure.hausdorffMeasure 2 (R.face i)).toReal := by
    rw [congruent_tetrahedron_image_face T R U σ hU i]
    rw [(LinearIsometryEquiv.toIsometryEquiv U).hausdorffMeasure_image 2 (R.face i)]
  calc
    (∑ i : Fin 4, (Measure.hausdorffMeasure 2 (T.face i)).toReal)
      = ∑ i : Fin 4, (Measure.hausdorffMeasure 2 (T.face (σ i))).toReal := by
        exact (Equiv.sum_comp σ (fun j => (Measure.hausdorffMeasure 2 (T.face j)).toReal)).symm
    _ = ∑ i : Fin 4, (Measure.hausdorffMeasure 2 (R.face i)).toReal := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_face i

/-- Congruence preserves the equal-edges condition defining regularity. -/
theorem regular_of_congruent (T R : SphericalTetrahedron)
    (h : T.Congruent R) (hR : R.Regular) : T.Regular := by
  rcases h with ⟨U, sigma, hU⟩
  rcases hR with ⟨rho, hrho⟩
  refine ⟨rho, ?_⟩
  intro i j hij
  obtain ⟨a, rfl⟩ := sigma.surjective i
  obtain ⟨b, rfl⟩ := sigma.surjective j
  have hab : a ≠ b := by
    intro hEq
    exact hij (congrArg sigma hEq)
  calc
    ⟪T.normal (sigma a), T.normal (sigma b)⟫_ℝ =
        ⟪U (R.normal a), U (R.normal b)⟫_ℝ := by rw [hU a, hU b]
    _ = ⟪R.normal a, R.normal b⟫_ℝ :=
      LinearIsometryEquiv.inner_map_map U (R.normal a) (R.normal b)
    _ = rho := hrho a b hab

/-- The same normal Gram parameter gives both equal area and equal
    volume. This uses only congruence and isometry invariance of
    Hausdorff measures, not any isoperimetric inequality. -/
theorem regular_same_parameter_equal_measurements
    (T R : SphericalTetrahedron) (rho : ℝ)
    (hT : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, T.normal j⟫_ℝ = rho)
    (hR : ∀ i j : Fin 4, i ≠ j →
      ⟪R.normal i, R.normal j⟫_ℝ = rho) :
    T.area = R.area ∧ T.volume = R.volume := by
  have h : T.Congruent R := regular_same_parameter_congruent T R rho hT hR
  exact ⟨congruent_tetrahedron_equal_area T R h,
    congruent_tetrahedron_equal_volume T R h⟩


/-! ## Elementary real-variable rigidity step -/

/-- Four equal three-variable symmetric face energies force four ordered parameters
    to coincide, under three local comparisons. -/
theorem ordered_four_face_rigidity
    (F : ℝ → ℝ → ℝ → ℝ)
    (swap12 : ∀ a b c : ℝ, F a b c = F b a c)
    (swap23 : ∀ a b c : ℝ, F a b c = F a c b)
    (a b c d : ℝ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c)
    (aboveFirst : b < a → F a c d < F b c d)
    (aboveSecond : c < b → F b d a < F c d a)
    (isosceles : d < a → F a a a < F d a a)
    (h01 : F a c d = F b c d)
    (h12 : F a b d = F a c d)
    (h23 : F a b c = F a b d) :
    a = b ∧ b = c ∧ c = d := by
  have heqAB : a = b := by
    rcases eq_or_lt_of_le hab with hEq | hLt
    · exact hEq.symm
    · exact False.elim ((ne_of_lt (aboveFirst hLt)) h01)
  have heqBC : b = c := by
    rcases eq_or_lt_of_le hbc with hEq | hLt
    · exact hEq.symm
    · have h12' : F b d a = F c d a := by
        calc
          F b d a = F b a d := (swap23 b a d).symm
          _ = F a b d := (swap12 a b d).symm
          _ = F a c d := h12
          _ = F c a d := swap12 a c d
          _ = F c d a := swap23 c a d
      exact False.elim ((ne_of_lt (aboveSecond hLt)) h12')
  subst b
  subst c
  refine ⟨rfl, rfl, ?_⟩
  rcases eq_or_lt_of_le hcd with hEq | hLt
  · exact hEq.symm
  · have hbad : F a a a < F a a d := by
      calc
        F a a a < F d a a := isosceles hLt
        _ = F a d a := swap12 d a a
        _ = F a a d := swap23 a d a
    exact False.elim ((ne_of_lt hbad) h23)

