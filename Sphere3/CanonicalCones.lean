module

public import Mathlib

@[expose] public section

/-!
# A nested one-parameter family of tetrahedral cones

These are elementary statements about four linear inequalities in four
real variables.  There are no geometric measure-theory assumptions.

The associated spherical tetrahedron is the intersection of this cone
with the unit sphere in `R^4`.  Strict volume monotonicity additionally
requires proving that a nonempty relatively open spherical patch has
positive 3-dimensional Hausdorff measure; this file deliberately does
not postulate that fact.

No custom axioms or `sorry` are used.
-/

namespace Sphere3

/-- Four halfspaces with normals `(1,1,1,t)`, `(1,-1,-1,t)`,
`(-1,1,-1,t)`, `(-1,-1,1,t)`. -/
def CanonicalCone (t a b c z : ℝ) : Prop :=
  0 ≤ a + b + c + t * z ∧
  0 ≤ a - b - c + t * z ∧
  0 ≤ -a + b - c + t * z ∧
  0 ≤ -a - b + c + t * z

/-- Interior of the four halfspaces. -/
def CanonicalConeInterior (t a b c z : ℝ) : Prop :=
  0 < a + b + c + t * z ∧
  0 < a - b - c + t * z ∧
  0 < -a + b - c + t * z ∧
  0 < -a - b + c + t * z

theorem canonicalInterior_subset {t a b c z : ℝ}
    (h : CanonicalConeInterior t a b c z) : CanonicalCone t a b c z := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  exact ⟨le_of_lt h₀, le_of_lt h₁, le_of_lt h₂, le_of_lt h₃⟩

/-- For `t > 0`, all points of the cone have nonnegative last coordinate. -/
theorem canonicalCone_height_nonneg {t a b c z : ℝ}
    (ht : 0 < t) (h : CanonicalCone t a b c z) : 0 ≤ z := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  by_contra hz
  have hz' : z < 0 := lt_of_not_ge hz
  have hmul : t * z < 0 := mul_neg_of_pos_of_neg ht hz'
  linarith

/-- If the last coordinate is zero, the four remaining coordinates
are zero as well. -/
theorem canonicalCone_zero_height {t a b c : ℝ}
    (h : CanonicalCone t a b c 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  norm_num at h₀ h₁ h₂ h₃
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Every nonzero point of a canonical cone lies strictly in the
northern halfspace. -/
theorem canonicalCone_height_pos {t a b c z : ℝ}
    (ht : 0 < t) (h : CanonicalCone t a b c z)
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ z ≠ 0) : 0 < z := by
  have hz := canonicalCone_height_nonneg ht h
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · have habc : a = 0 ∧ b = 0 ∧ c = 0 := by
      apply canonicalCone_zero_height (t := t)
      simpa [← hz0] using h
    rcases habc with ⟨ha, hb, hc⟩
    rcases hne with hne | hne | hne | hne
    · exact False.elim (hne ha)
    · exact False.elim (hne hb)
    · exact False.elim (hne hc)
    · exact False.elim (hne hz0.symm)
  · exact hzpos

/-- As `t` increases, every canonical tetrahedral cone expands. -/
theorem canonicalCone_mono {t s a b c z : ℝ}
    (ht : 0 < t) (hts : t ≤ s)
    (h : CanonicalCone t a b c z) : CanonicalCone s a b c z := by
  have hz : 0 ≤ z := canonicalCone_height_nonneg ht h
  have hdelta : 0 ≤ (s - t) * z := mul_nonneg (sub_nonneg.mpr hts) hz
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The inclusion is proper: an explicitly constructed point lies
strictly inside the larger cone but outside the smaller one. -/
theorem canonicalCone_strict_witness {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ a b c z : ℝ,
      CanonicalConeInterior s a b c z ∧ ¬ CanonicalCone t a b c z := by
  refine ⟨-(t + s) / 6, -(t + s) / 6, -(t + s) / 6, 1, ?_, ?_⟩
  · dsimp [CanonicalConeInterior]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · intro h
    have hfirst := h.1
    nlinarith

/-- Conical inclusion together with an interior point of the
set-theoretic difference. -/
theorem canonicalCone_strict_expansion {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (∀ a b c z : ℝ, CanonicalCone t a b c z →
      CanonicalCone s a b c z) ∧
    (∃ a b c z : ℝ,
      CanonicalCone s a b c z ∧ ¬ CanonicalCone t a b c z) := by
  constructor
  · intro a b c z h
    exact canonicalCone_mono ht (le_of_lt hts) h
  · obtain ⟨a, b, c, z, hs, htneg⟩ := canonicalCone_strict_witness ht hts
    exact ⟨a, b, c, z, canonicalInterior_subset hs, htneg⟩

end Sphere3

namespace Sphere3

/-- Positively rescaling a point preserves the cone conditions. -/
theorem canonicalCone_pos_scale {t a b c z k : ℝ} (hk : 0 < k)
    (h : CanonicalCone t a b c z) :
    CanonicalCone t (k * a) (k * b) (k * c) (k * z) := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hp := mul_nonneg (le_of_lt hk) h₀
    nlinarith
  · have hp := mul_nonneg (le_of_lt hk) h₁
    nlinarith
  · have hp := mul_nonneg (le_of_lt hk) h₂
    nlinarith
  · have hp := mul_nonneg (le_of_lt hk) h₃
    nlinarith

/-- Positively rescaling a point preserves the strict cone conditions. -/
theorem canonicalInterior_pos_scale {t a b c z k : ℝ} (hk : 0 < k)
    (h : CanonicalConeInterior t a b c z) :
    CanonicalConeInterior t (k * a) (k * b) (k * c) (k * z) := by
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hp := mul_pos hk h₀
    nlinarith
  · have hp := mul_pos hk h₁
    nlinarith
  · have hp := mul_pos hk h₂
    nlinarith
  · have hp := mul_pos hk h₃
    nlinarith

/-- The algebraic equation of the unit three-sphere in four real coordinates. -/
def CanonicalUnitSphere (a b c z : ℝ) : Prop :=
  a ^ 2 + b ^ 2 + c ^ 2 + z ^ 2 = 1

/-- The strict difference between two canonical tetrahedral cones already
contains a point on the unit three-sphere. -/
theorem canonicalUnitSphere_strict_witness {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ a b c z : ℝ,
      CanonicalUnitSphere a b c z ∧
      CanonicalConeInterior s a b c z ∧
      ¬ CanonicalCone t a b c z := by
  let a₀ : ℝ := -(t + s) / 6
  let Q : ℝ := 1 + 3 * a₀ ^ 2
  let k : ℝ := (Real.sqrt Q)⁻¹
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hk : 0 < k := inv_pos.mpr hroot
  have hk_sq : k ^ 2 * Q = 1 := by
    dsimp [k]
    rw [inv_pow, Real.sq_sqrt (le_of_lt hQ)]
    field_simp [ne_of_gt hQ]
  have hraw : CanonicalConeInterior s a₀ a₀ a₀ 1 := by
    dsimp [CanonicalConeInterior, a₀]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [ht, hts]
  refine ⟨k * a₀, k * a₀, k * a₀, k, ?_, ?_, ?_⟩
  · dsimp [CanonicalUnitSphere]
    have hh : k ^ 2 * (1 + 3 * a₀ ^ 2) = 1 := by
      simpa [Q] using hk_sq
    nlinarith [hh]
  · simpa using canonicalInterior_pos_scale (k := k) hk hraw
  · intro hsmall
    have hfirst := hsmall.1
    have hneg : 3 * a₀ + t < 0 := by
      dsimp [a₀]
      linarith [hts]
    have hp := mul_neg_of_pos_of_neg hk hneg
    nlinarith

end Sphere3

namespace Sphere3

/-- The canonical spherical tetrahedron as an actual subset of the
Euclidean unit three-sphere. It uses unnormalized normals, which define
the same four halfspaces as their positive unit-normal multiples. -/
def canonicalSphereBody (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin 4)) :=
  {x | ‖x‖ = 1 ∧ CanonicalCone t (x 0) (x 1) (x 2) (x 3)}

/-- The canonical spherical bodies are nested when their positive
normal parameters are ordered. -/
theorem canonicalSphereBody_mono {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    canonicalSphereBody t ⊆ canonicalSphereBody s := by
  intro x hx
  exact ⟨hx.1, canonicalCone_mono ht hts hx.2⟩

/-- Hausdorff measure is nondecreasing along the canonical regular
family. Proving strict growth requires the local positivity of the
three-dimensional surface measure on `S³`. -/
theorem canonicalSphereBody_hausdorff_mono {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    (MeasureTheory.Measure.hausdorffMeasure (3 : ℝ))
        (canonicalSphereBody t) ≤
      (MeasureTheory.Measure.hausdorffMeasure (3 : ℝ))
        (canonicalSphereBody s) := by
  exact MeasureTheory.measure_mono (canonicalSphereBody_mono ht hts)

end Sphere3

namespace Sphere3

/-- A four-tuple on the algebraic unit quadric represents an actual
unit vector in the Euclidean space `R^4`. -/
theorem canonical_vec_norm_one {a b c z : ℝ}
    (h : CanonicalUnitSphere a b c z) :
    ‖(!₂[a, b, c, z] : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
  have hnorm :
      ‖(!₂[a, b, c, z] : EuclideanSpace ℝ (Fin 4))‖ ^ 2 =
        a ^ 2 + b ^ 2 + c ^ 2 + z ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    ring
  have hnonneg : 0 ≤ ‖(!₂[a, b, c, z] : EuclideanSpace ℝ (Fin 4))‖ :=
    norm_nonneg _
  dsimp [CanonicalUnitSphere] at h
  nlinarith [hnorm]

/-- A point in the actual unit sphere lies strictly inside the larger
canonical tetrahedron and outside the smaller one. -/
theorem canonicalSphereBody_strict_witness {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ x : EuclideanSpace ℝ (Fin 4),
      x ∈ canonicalSphereBody s ∧ x ∉ canonicalSphereBody t ∧
      CanonicalConeInterior s (x 0) (x 1) (x 2) (x 3) := by
  obtain ⟨a, b, c, z, hquad, hinside, houtside⟩ :=
    canonicalUnitSphere_strict_witness ht hts
  refine ⟨!₂[a, b, c, z], ?_, ?_, ?_⟩
  · refine ⟨canonical_vec_norm_one hquad, ?_⟩
    simpa using canonicalInterior_subset hinside
  · intro hsmall
    exact houtside (by simpa using hsmall.2)
  · simpa using hinside

end Sphere3
