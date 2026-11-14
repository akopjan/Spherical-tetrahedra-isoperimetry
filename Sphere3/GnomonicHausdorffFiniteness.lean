module

public import Sphere3.GnomonicLipschitz
public import Sphere3.CanonicalProjection

@[expose] public section

/-!
# Finiteness and strict Hausdorff-volume growth in the regular family

The gnomonic base `B_t` is a compact Euclidean three-dimensional tetrahedron.
Its normalized affine lift covers the actual spherical tetrahedron `C_t`.
The chart is globally 2-Lipschitz, so `H³(C_t) < ∞`. Together with the
strictly positive projected open patch proved in `CanonicalProjection`, this
gives strict monotonicity of the actual (unnormalized) `hausdorffMeasure 3`.

No polar-normalization factor and no comparison with `toSphere` are used.
-/

noncomputable section

open MeasureTheory

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- On the compact gnomonic base, each coordinate has absolute value
at most `t`, giving a uniform Euclidean norm bound. -/
theorem gnomonicBase_norm_le (t : ℝ) (ht : 0 < t)
    (u : E3) (hu : u ∈ GnomonicBase t) :
    ‖u‖ ≤ 3 * t + 1 := by
  obtain ⟨h0L, h0R, h1L, h1R, h2L, h2R⟩ :=
    canonicalCone_base_bounds hu
  have h0 : 0 ≤ (t - u 0) * (t + u 0) :=
    mul_nonneg (by linarith) (by linarith)
  have h1 : 0 ≤ (t - u 1) * (t + u 1) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (t - u 2) * (t + u 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq u, Fin.sum_univ_three]
  have hBoundSq : ‖u‖ ^ 2 ≤ 3 * t ^ 2 := by
    nlinarith [h0, h1, h2, hsq]
  nlinarith [norm_nonneg u, sq_nonneg (3 * t)]

/-- Closedness and boundedness prove compactness of the gnomonic base. -/
theorem gnomonicBase_isCompact (t : ℝ) (ht : 0 < t) :
    IsCompact (GnomonicBase t) := by
  apply Metric.isCompact_of_isClosed_isBounded (gnomonicBase_isClosed t)
  apply (isBounded_iff_forall_norm_le).2
  exact ⟨3 * t + 1, fun u hu => gnomonicBase_norm_le t ht u hu⟩

/-- Affine coordinates of a spherical point with positive fourth coordinate. -/
def canonicalGnomonicPoint (x : E4) : E3 :=
  !₂[x 0 / x 3, x 1 / x 3, x 2 / x 3]

/-- On the positive hemisphere, the affine lift of the gnomonic point
is the original vector multiplied by the reciprocal of its height. -/
theorem gnomonicLift_point (x : E4) (hx : x 3 ≠ 0) :
    gnomonicLift (canonicalGnomonicPoint x) = (x 3)⁻¹ • x := by
  ext i
  fin_cases i <;>
    simp [gnomonicLift, canonicalGnomonicPoint, div_eq_inv_mul, hx]

/-- Every point of a nonzero canonical spherical cone has positive height. -/
theorem canonicalSphereBody_height_pos (t : ℝ) (ht : 0 < t)
    (x : E4) (hx : x ∈ canonicalSphereBody t) : 0 < x 3 := by
  have hnonneg : 0 ≤ x 3 := canonicalCone_height_nonneg ht hx.2
  rcases eq_or_lt_of_le hnonneg with hz | hzpos
  · have hz0 : x 3 = 0 := hz.symm
    have habc := canonicalCone_zero_height (t := t) (by
      simpa [hz0] using hx.2)
    have hxzero : x = (0 : E4) := by
      ext i
      fin_cases i <;> simp [habc.1, habc.2.1, habc.2.2, hz0]
    have hnorm := hx.1
    rw [hxzero] at hnorm
    norm_num at hnorm
  · exact hzpos

/-- The gnomonic point of a spherical canonical cone belongs to its
bounded three-dimensional cross-section. -/
theorem canonicalGnomonicPoint_mem_base (t : ℝ)
    (x : E4) (hx : x ∈ canonicalSphereBody t)
    (hHeight : 0 < x 3) :
    canonicalGnomonicPoint x ∈ GnomonicBase t := by
  have hScale : CanonicalCone t
      ((x 3)⁻¹ * x 0) ((x 3)⁻¹ * x 1) ((x 3)⁻¹ * x 2)
      ((x 3)⁻¹ * x 3) :=
    canonicalCone_pos_scale (inv_pos.mpr hHeight) hx.2
  have hLast : (x 3)⁻¹ * x 3 = 1 := inv_mul_cancel₀ hHeight.ne'
  simpa [GnomonicBase, canonicalGnomonicPoint, hLast,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hScale

/-- The spherical normalization of the affine chart is exactly the
original unit vector, provided the original vector has positive height. -/
theorem gnomonicNormalize_point (x : E4)
    (hNorm : ‖x‖ = 1) (hHeight : 0 < x 3) :
    gnomonicNormalize (canonicalGnomonicPoint x) = x := by
  have hLift := gnomonicLift_point x hHeight.ne'
  have hLiftNorm : ‖gnomonicLift (canonicalGnomonicPoint x)‖ =
      (x 3)⁻¹ := by
    rw [hLift, norm_smul, hNorm, mul_one, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr hHeight)
  unfold gnomonicNormalize
  rw [hLiftNorm, inv_inv, hLift, smul_smul,
    mul_inv_cancel₀ hHeight.ne', one_smul]

/-- Exact representation of the spherical body as the chart image of
its compact gnomonic base (at positive regular parameters). -/
theorem canonicalSphereBody_eq_gnomonic_image
    (t : ℝ) (ht : 0 < t) :
    canonicalSphereBody t = gnomonicNormalize '' GnomonicBase t := by
  ext x
  constructor
  · intro hx
    have hHeight := canonicalSphereBody_height_pos t ht x hx
    exact ⟨canonicalGnomonicPoint x,
      canonicalGnomonicPoint_mem_base t x hx hHeight,
      gnomonicNormalize_point x hx.1 hHeight⟩
  · rintro ⟨u, hu, rfl⟩
    have hLiftPos : 0 < ‖gnomonicLift u‖⁻¹ :=
      inv_pos.mpr (lt_of_lt_of_le zero_lt_one (gnomonicLift_norm_ge_one u))
    have hNorm : ‖gnomonicNormalize u‖ = 1 := by
      unfold gnomonicNormalize
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLiftPos]
      exact inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one
        (gnomonicLift_norm_ge_one u)))
    have hCone : CanonicalCone t
        ((gnomonicNormalize u) 0) ((gnomonicNormalize u) 1)
        ((gnomonicNormalize u) 2) ((gnomonicNormalize u) 3) := by
      have h := canonicalCone_pos_scale (k := ‖gnomonicLift u‖⁻¹)
        hLiftPos hu
      simpa [gnomonicNormalize, gnomonicLift, GnomonicBase]
        using h
    exact ⟨hNorm, hCone⟩

/-- The 3-dimensional Hausdorff measure of every canonical regular body
is finite; this is now a consequence of a compact domain and a
Lipschitz chart, rather than a polar-integration assumption. -/
theorem canonicalSphereBody_hausdorff_finite
    (t : ℝ) (ht : 0 < t) :
    (Measure.hausdorffMeasure (3 : ℝ) : Measure E4)
      (canonicalSphereBody t) ≠ ⊤ := by
  rw [canonicalSphereBody_eq_gnomonic_image t ht]
  exact gnomonicNormalize_compact_hausdorff_finite
    (GnomonicBase t) (gnomonicBase_isCompact t ht)

/-- The full-dimensional Hausdorff measure on Euclidean R^3 is a Haar
measure; in particular nonempty open sets have positive measure. -/
theorem euclideanThree_hausdorff_isOpenPos :
    (Measure.hausdorffMeasure (3 : ℝ) : Measure E3).IsOpenPosMeasure := by
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  letI : (Measure.hausdorffMeasure (3 : ℝ) : Measure E3).IsAddHaarMeasure := by
    simpa [hdim] using
      (inferInstance : (Measure.hausdorffMeasure
        (Module.finrank ℝ E3 : ℝ) : Measure E3).IsAddHaarMeasure)
  infer_instance

/-- Strict increase of actual 3-dimensional unnormalized Hausdorff
measure on the canonical regular spherical tetrahedra. -/
theorem canonicalSphereBody_hausdorff_strict
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (Measure.hausdorffMeasure (3 : ℝ) : Measure E4) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ) : Measure E4) (canonicalSphereBody s) := by
  letI : (Measure.hausdorffMeasure (3 : ℝ) : Measure E3).IsOpenPosMeasure :=
    euclideanThree_hausdorff_isOpenPos
  exact canonicalSphereBody_hausdorff_strict_of_finite ht hts
    (canonicalSphereBody_hausdorff_finite t ht)

/-- Strict increase for the real-valued volume used in the challenge,
with the actual `hausdorffMeasure 3` and not angular measure. -/
theorem canonicalSphereBody_real_volume_strict
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    ((Measure.hausdorffMeasure (3 : ℝ) : Measure E4) (canonicalSphereBody t)).toReal <
      ((Measure.hausdorffMeasure (3 : ℝ) : Measure E4) (canonicalSphereBody s)).toReal := by
  exact ENNReal.toReal_strict_mono
    (canonicalSphereBody_hausdorff_finite s (lt_trans ht hts))
    (canonicalSphereBody_hausdorff_strict ht hts)

end Sphere3
