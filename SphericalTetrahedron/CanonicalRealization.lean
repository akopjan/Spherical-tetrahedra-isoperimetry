module

public import SphericalTetrahedron.AffineChart
public import Sphere3.CanonicalMatrix

@[expose] public section

/-!
# The canonical regular family in the challenge's geometric type

Four explicit rows of a non-singular matrix give inward facet normals.
After normalization, they form a genuine `SphericalTetrahedron` whose
body is *equal as a set* to the previously studied canonical sphere cone.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- The raw canonical inward normal, represented in `E4`. -/
def canonicalRawNormal (t : ℝ) (i : Fin 4) : E4 :=
  WithLp.toLp 2 ((Sphere3.canonicalNormalMatrix t).row i)

/-- Each raw normal has squared length `3 + t²`. -/
theorem canonicalRawNormal_norm_sq (t : ℝ) (i : Fin 4) :
    ‖canonicalRawNormal t i‖ ^ 2 = 3 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;>
    norm_num [canonicalRawNormal, Sphere3.canonicalNormalMatrix,
      Fin.sum_univ_succ, Matrix.row] <;> ring

/-- Each raw normal has positive length. -/
theorem canonicalRawNormal_norm (t : ℝ) (i : Fin 4) :
    ‖canonicalRawNormal t i‖ = Real.sqrt (3 + t ^ 2) := by
  have hs : (Real.sqrt (3 + t ^ 2)) ^ 2 = 3 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hn := canonicalRawNormal_norm_sq t i
  have hnn : 0 ≤ ‖canonicalRawNormal t i‖ := norm_nonneg _
  have hr : 0 ≤ Real.sqrt (3 + t ^ 2) := Real.sqrt_nonneg _
  nlinarith

/-- Unit-length inward facet normals. -/
def canonicalUnitNormal (t : ℝ) (i : Fin 4) : E4 :=
  (Real.sqrt (3 + t ^ 2))⁻¹ • canonicalRawNormal t i

/-- The canonical normals are unit vectors. -/
theorem canonicalUnitNormal_norm (t : ℝ) (i : Fin 4) :
    ‖canonicalUnitNormal t i‖ = 1 := by
  have hr : 0 < Real.sqrt (3 + t ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  unfold canonicalUnitNormal
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr), canonicalRawNormal_norm]
  exact inv_mul_cancel₀ hr.ne'

/-- The raw normals remain independent after the ambient linear equivalence. -/
theorem canonicalRawNormal_independent (t : ℝ) (ht : 0 < t) :
    LinearIndependent ℝ (canonicalRawNormal t) := by
  let f : (Fin 4 → ℝ) ≃ₗ[ℝ] E4 :=
    (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm
  have hrows : LinearIndependent ℝ
      (Sphere3.canonicalNormalMatrix t).row :=
    Sphere3.canonicalNormalMatrix_rows_independent t ht
  have hmapped : LinearIndependent ℝ
      (f ∘ (Sphere3.canonicalNormalMatrix t).row) :=
    hrows.map_injOn f.toLinearMap (fun _ _ _ _ h => f.injective h)
  change LinearIndependent ℝ (f ∘ (Sphere3.canonicalNormalMatrix t).row)
  exact hmapped

/-- Multiplying all the raw normals by the same nonzero number keeps
linear independence. -/
theorem canonicalUnitNormal_independent (t : ℝ) (ht : 0 < t) :
    LinearIndependent ℝ (canonicalUnitNormal t) := by
  have hr : 0 < Real.sqrt (3 + t ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hscale : (Real.sqrt (3 + t ^ 2))⁻¹ ≠ (0 : ℝ) :=
    inv_ne_zero hr.ne'
  let w : Fin 4 → ℝˣ :=
    fun _ => Units.mk0 (Real.sqrt (3 + t ^ 2))⁻¹ hscale
  have hscaled : LinearIndependent ℝ (w • canonicalRawNormal t) :=
    (LinearIndependent.units_smul_iff (canonicalRawNormal t) w).mpr
      (canonicalRawNormal_independent t ht)
  change LinearIndependent ℝ (w • canonicalRawNormal t)
  exact hscaled

/-- A genuine nondegenerate spherical tetrahedron at every positive scale. -/
def canonicalTetrahedron (t : ℝ) (ht : 0 < t) : SphericalTetrahedron where
  normal := canonicalUnitNormal t
  unit := canonicalUnitNormal_norm t
  independent := canonicalUnitNormal_independent t ht

/-- The distinct raw normals have inner product `t² - 1`. -/
theorem canonicalRawNormal_inner_offdiag (t : ℝ) (i j : Fin 4)
    (hij : i ≠ j) :
    ⟪canonicalRawNormal t i, canonicalRawNormal t j⟫_ℝ = t ^ 2 - 1 := by
  unfold canonicalRawNormal
  rw [EuclideanSpace.inner_toLp_toLp]
  fin_cases i <;> fin_cases j <;>
    simp_all [Sphere3.canonicalNormalMatrix,
      Fin.sum_univ_succ, Matrix.row, dotProduct] <;> ring

/-- The exact common Gram parameter of the unit normals. -/
theorem canonicalUnitNormal_inner_offdiag (t : ℝ) (i j : Fin 4)
    (hij : i ≠ j) :
    ⟪canonicalUnitNormal t i, canonicalUnitNormal t j⟫_ℝ =
      Sphere3.canonicalGramParameter t := by
  have hr : 0 < Real.sqrt (3 + t ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hsq : (Real.sqrt (3 + t ^ 2)) ^ 2 = 3 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hden : 3 + t ^ 2 ≠ 0 := by positivity
  unfold canonicalUnitNormal Sphere3.canonicalGramParameter
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [canonicalRawNormal_inner_offdiag t i j hij]
  field_simp [hr.ne', hden]
  nlinarith

/-- Every canonical tetrahedron is regular. -/
theorem canonicalTetrahedron_regular (t : ℝ) (ht : 0 < t) :
    (canonicalTetrahedron t ht).Regular := by
  refine ⟨Sphere3.canonicalGramParameter t, ?_⟩
  intro i j hij
  exact canonicalUnitNormal_inner_offdiag t i j hij

/-- Normalizing an inward normal by a positive scalar does not alter
its hemisphere. -/
theorem canonicalTetrahedron_normal_nonneg_iff
    (t : ℝ) (ht : 0 < t) (i : Fin 4) (x : E4) :
    0 ≤ ⟪(canonicalTetrahedron t ht).normal i, x⟫_ℝ ↔
      0 ≤ ⟪canonicalRawNormal t i, x⟫_ℝ := by
  have hroot : 0 < Real.sqrt (3 + t ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hscale : 0 < (Real.sqrt (3 + t ^ 2))⁻¹ :=
    inv_pos.mpr hroot
  change 0 ≤ ⟪canonicalUnitNormal t i, x⟫_ℝ ↔ _
  rw [canonicalUnitNormal, real_inner_smul_left]
  exact mul_nonneg_iff_of_pos_left hscale

/-- The four inequalities of the raw normal system coincide exactly
with those of the canonical cone. -/
theorem canonicalRawNormal_cone_iff (t : ℝ) (x : E4) :
    (∀ i : Fin 4, 0 ≤ ⟪canonicalRawNormal t i, x⟫_ℝ) ↔
      Sphere3.CanonicalCone t (x 0) (x 1) (x 2) (x 3) := by
  have hx : x = WithLp.toLp 2 x.ofLp := rfl
  have h0 : ⟪canonicalRawNormal t 0, x⟫_ℝ =
      x 0 + x 1 + x 2 + t * x 3 := by
    conv_lhs => rw [hx, canonicalRawNormal, EuclideanSpace.inner_toLp_toLp]
    simp [Sphere3.canonicalNormalMatrix, dotProduct, Fin.sum_univ_four]
    ring
  have h1 : ⟪canonicalRawNormal t 1, x⟫_ℝ =
      x 0 - x 1 - x 2 + t * x 3 := by
    conv_lhs => rw [hx, canonicalRawNormal, EuclideanSpace.inner_toLp_toLp]
    simp [Sphere3.canonicalNormalMatrix, dotProduct, Fin.sum_univ_four]
    ring
  have h2 : ⟪canonicalRawNormal t 2, x⟫_ℝ =
      -x 0 + x 1 - x 2 + t * x 3 := by
    conv_lhs => rw [hx, canonicalRawNormal, EuclideanSpace.inner_toLp_toLp]
    simp [Sphere3.canonicalNormalMatrix, dotProduct, Fin.sum_univ_four]
    ring
  have h3 : ⟪canonicalRawNormal t 3, x⟫_ℝ =
      -x 0 - x 1 + x 2 + t * x 3 := by
    conv_lhs => rw [hx, canonicalRawNormal, EuclideanSpace.inner_toLp_toLp]
    simp [Sphere3.canonicalNormalMatrix, dotProduct, Fin.sum_univ_four]
    ring
  change (∀ i : Fin 4, 0 ≤ ⟪canonicalRawNormal t i, x⟫_ℝ) ↔
    (0 ≤ x 0 + x 1 + x 2 + t * x 3 ∧
     0 ≤ x 0 - x 1 - x 2 + t * x 3 ∧
     0 ≤ -x 0 + x 1 - x 2 + t * x 3 ∧
     0 ≤ -x 0 - x 1 + x 2 + t * x 3)
  constructor
  · intro h
    exact ⟨by simpa only [h0] using h 0,
      by simpa only [h1] using h 1,
      by simpa only [h2] using h 2,
      by simpa only [h3] using h 3⟩
  · rintro ⟨ha, hb, hc, hd⟩ i
    fin_cases i
    · change 0 ≤ ⟪canonicalRawNormal t 0, x⟫_ℝ; linarith
    · change 0 ≤ ⟪canonicalRawNormal t 1, x⟫_ℝ; linarith
    · change 0 ≤ ⟪canonicalRawNormal t 2, x⟫_ℝ; linarith
    · change 0 ≤ ⟪canonicalRawNormal t 3, x⟫_ℝ; linarith

/-- Equality of the genuine body and the canonical auxiliary body.
This is a set identity, not a statement about a substitute measure. -/
theorem canonicalTetrahedron_body_eq (t : ℝ) (ht : 0 < t) :
    (canonicalTetrahedron t ht).body = Sphere3.canonicalSphereBody t := by
  ext x
  change (‖x‖ = 1 ∧
      ∀ i : Fin 4, 0 ≤ ⟪canonicalUnitNormal t i, x⟫_ℝ) ↔
    (‖x‖ = 1 ∧ Sphere3.CanonicalCone t (x 0) (x 1) (x 2) (x 3))
  constructor
  · rintro ⟨hn, hunit⟩
    refine ⟨hn, ?_⟩
    apply (canonicalRawNormal_cone_iff t x).mp
    intro i
    exact (canonicalTetrahedron_normal_nonneg_iff t ht i x).mp (hunit i)
  · rintro ⟨hn, hcone⟩
    refine ⟨hn, ?_⟩
    intro i
    apply (canonicalTetrahedron_normal_nonneg_iff t ht i x).mpr
    exact (canonicalRawNormal_cone_iff t x).mpr hcone i

/-- The actual challenge volume equals Hausdorff measure of the cone
studied by the canonical auxiliary lemmas. -/
theorem canonicalTetrahedron_volume_eq (t : ℝ) (ht : 0 < t) :
    (canonicalTetrahedron t ht).volume =
      ((MeasureTheory.Measure.hausdorffMeasure (3 : ℝ))
        (Sphere3.canonicalSphereBody t)).toReal := by
  unfold SphericalTetrahedron.volume SphericalTetrahedron.measure
  rw [canonicalTetrahedron_body_eq t ht]

end SphericalTetrahedron
