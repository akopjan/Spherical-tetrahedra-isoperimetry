module

public import Sphere3.CanonicalArea

@[expose] public section

/-!
# A common spherical chart for the four regular faces

For the canonical normal rows `(r_i,t)` with `r_0=(1,1,1)` and
`r_1=(1,-1,-1)`, `r_2=(-1,1,-1)`, `r_3=(-1,-1,1)`, the first face can
be placed isometrically in a single fixed unit two-sphere. In that
fixed sphere it is the gnomonic image of the expanding planar triangle

  {u_0+u_1+u_2=0,  2u_i+aperture(t)>=0  for each i=0,1,2}.

The aperture `4t/(sqrt 3 * sqrt(3+t^2))` is strictly increasing for
t>0.  These lemmas cover the exact real algebra and the strict interior patch
used in the 2-dimensional Hausdorff area comparison.
-/

noncomputable section

namespace Sphere3

/-- Positive geometric scale in the canonical face chart. -/
def canonicalFaceScale (t : ℝ) : ℝ :=
  t / Real.sqrt (3 + t ^ 2)

/-- The offset of the three supporting lines after orthogonal rotation
of the moving face plane to a fixed three-dimensional ambient space. -/
def canonicalFaceAperture (t : ℝ) : ℝ :=
  (4 / Real.sqrt 3) * canonicalFaceScale t

private theorem faceScale_den_pos (t : ℝ) :
    0 < Real.sqrt (3 + t ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- Both the scale and aperture are strictly positive for positive t. -/
theorem canonicalFaceScale_pos {t : ℝ} (ht : 0 < t) :
    0 < canonicalFaceScale t := by
  exact div_pos ht (faceScale_den_pos t)

theorem canonicalFaceAperture_pos {t : ℝ} (ht : 0 < t) :
    0 < canonicalFaceAperture t := by
  unfold canonicalFaceAperture
  exact mul_pos (div_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
    (canonicalFaceScale_pos ht)

/-- Squaring the scale eliminates its sole radical. -/
theorem canonicalFaceScale_sq (t : ℝ) :
    canonicalFaceScale t ^ 2 = t ^ 2 / (3 + t ^ 2) := by
  unfold canonicalFaceScale
  rw [div_pow, Real.sq_sqrt (by positivity)]

/-- The canonical-face aperture is strictly increasing, without any
use of the spherical-excess or Girard area formula. -/
theorem canonicalFaceScale_strictMonoOn :
    StrictMonoOn canonicalFaceScale (Set.Ioi 0) := by
  intro a ha b hb hab
  have hsq : a ^ 2 < b ^ 2 := by
    have hp : 0 < (b - a) * (b + a) :=
      mul_pos (sub_pos.mpr hab) (add_pos hb ha)
    nlinarith
  have hda : 0 < 3 + a ^ 2 := by positivity
  have hdb : 0 < 3 + b ^ 2 := by positivity
  have hfrac : a ^ 2 / (3 + a ^ 2) <
      b ^ 2 / (3 + b ^ 2) := by
    apply (div_lt_div_iff₀ hda hdb).2
    nlinarith
  have hapos := canonicalFaceScale_pos ha
  have hbpos := canonicalFaceScale_pos hb
  rw [← canonicalFaceScale_sq, ← canonicalFaceScale_sq] at hfrac
  by_contra h
  have hle : canonicalFaceScale b ≤ canonicalFaceScale a := le_of_not_gt h
  have hmul : 0 ≤
      (canonicalFaceScale a - canonicalFaceScale b) *
      (canonicalFaceScale a + canonicalFaceScale b) :=
    mul_nonneg (sub_nonneg.mpr hle)
      (add_nonneg hapos.le hbpos.le)
  nlinarith

theorem canonicalFaceAperture_strictMonoOn :
    StrictMonoOn canonicalFaceAperture (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold canonicalFaceAperture
  exact mul_lt_mul_of_pos_left
    (canonicalFaceScale_strictMonoOn ha hb hab)
    (div_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))

/-- The planar domain of the first regular face, written in coordinates
with sum zero. It is a compact equilateral triangle in that affine plane.
The parameter `a` denotes the common *linear-inequality offset*. -/
def canonicalFaceTriangle (a : ℝ) : Set (Fin 3 → ℝ) :=
  {u | (u 0 + u 1 + u 2 = 0) ∧
    (∀ i : Fin 3, -a / 2 ≤ u i)}

/-- The planar triangles are nested when the offset increases. -/
theorem canonicalFaceTriangle_mono {a b : ℝ} (hab : a ≤ b) :
    canonicalFaceTriangle a ⊆ canonicalFaceTriangle b := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  intro i
  have h := hu.2 i
  linarith

/-- A witness strictly inside the larger triangle but violating the
first inequality of the smaller one.  All three larger inequalities
are strict, so the new region contains a relatively open planar patch. -/
theorem canonicalFaceTriangle_strict_witness {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ u : Fin 3 → ℝ,
      u 0 + u 1 + u 2 = 0 ∧
      (∀ i : Fin 3, -b / 2 < u i) ∧
      u 0 < -a / 2 := by
  let u : Fin 3 → ℝ := ![-(a + b) / 4, (a + b) / 8, (a + b) / 8]
  refine ⟨u, ?_, ?_, ?_⟩
  · dsimp [u]
    ring
  · intro i
    fin_cases i <;> dsimp [u] <;> linarith
  · dsimp [u]
    linarith

/-- A normalized face parameter is an admissible positive offset. -/
theorem canonicalFaceAperture_strict {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    0 < canonicalFaceAperture t ∧
    canonicalFaceAperture t < canonicalFaceAperture s := by
  exact ⟨canonicalFaceAperture_pos ht,
    canonicalFaceAperture_strictMonoOn ht (lt_trans ht hts) hts⟩

end Sphere3
