module

public import Sphere3.CanonicalFaceCoordinates

@[expose] public section

/-!
# Nested planar domains of canonical spherical faces

The normalized charts `canonicalFacePoint t p q` have the same intrinsic
metric for every `t` (see `CanonicalFaceCoordinates`).  The admissible
parameter domains are planar triangles strictly nested with `t`, so the
Hausdorff area must strictly increase once the measure-preserving chart
and positive-measure open-patch lemmas are available.

These lemmas handle the exact real inequalities and nested domain witnesses.
-/

noncomputable section

namespace Sphere3

/-- The physically meaningful radius of the planar triangle. -/
def canonicalFaceRawAperture (t : ℝ) : ℝ :=
  4 * t / canonicalFaceHeight t

/-- The two radical descriptions of the face-plane height agree. -/
theorem canonicalFaceHeight_eq (t : ℝ) :
    canonicalFaceHeight t =
      Real.sqrt 3 * Real.sqrt (3 + t ^ 2) := by
  have h : 9 + 3 * t ^ 2 = 3 * (3 + t ^ 2) := by ring
  unfold canonicalFaceHeight
  rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- These two equivalent aperture formulas make the elementary nested-
triangle argument and the original Gram scaling directly comparable. -/
theorem canonicalFaceRawAperture_eq (t : ℝ) :
    canonicalFaceRawAperture t = canonicalFaceAperture t := by
  unfold canonicalFaceRawAperture canonicalFaceAperture canonicalFaceScale
  rw [canonicalFaceHeight_eq]
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hden : Real.sqrt (3 + t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp [h3, hden]

/-- The aperture of the actual raw first-face chart is strictly
increasing on positive parameters. -/
theorem canonicalFaceRawAperture_strictMonoOn :
    StrictMonoOn canonicalFaceRawAperture (Set.Ioi 0) := by
  intro t ht s hs hts
  rw [canonicalFaceRawAperture_eq, canonicalFaceRawAperture_eq]
  exact canonicalFaceAperture_strictMonoOn ht hs hts

/-- The three inequalities in raw coordinates are equivalent to a
triangle with common offset ±α(t)/2. -/
def canonicalFacePlanarTriangle (t : ℝ) : Set (ℝ × ℝ) :=
  {z | -canonicalFaceRawAperture t / 2 ≤ z.1 ∧
       -canonicalFaceRawAperture t / 2 ≤ z.2 ∧
       z.1 + z.2 ≤ canonicalFaceRawAperture t / 2}

/-- Multiply both sides by the positive face height to eliminate
all denominators in the triangular inequalities. -/
theorem canonicalFaceRawRegion_eq_triangle (t : ℝ) :
    canonicalFaceRawRegion t = canonicalFacePlanarTriangle t := by
  ext z
  have hh : 0 < canonicalFaceHeight t := canonicalFaceHeight_pos t
  have hEq : canonicalFaceRawAperture t / 2 =
      2 * t / canonicalFaceHeight t := by
    unfold canonicalFaceRawAperture
    ring
  have hFirst :
      (0 ≤ 2 * canonicalFaceHeight t * z.1 + 4 * t) ↔
      -2 * t / canonicalFaceHeight t ≤ z.1 := by
    constructor
    · intro h
      apply (div_le_iff₀ hh).2
      nlinarith
    · intro h
      have hmul := (div_le_iff₀ hh).1 h
      nlinarith
  have hSecond :
      (0 ≤ 2 * canonicalFaceHeight t * z.2 + 4 * t) ↔
      -2 * t / canonicalFaceHeight t ≤ z.2 := by
    constructor
    · intro h
      apply (div_le_iff₀ hh).2
      nlinarith
    · intro h
      have hmul := (div_le_iff₀ hh).1 h
      nlinarith
  have hThird :
      (0 ≤ -2 * canonicalFaceHeight t * (z.1 + z.2) + 4 * t) ↔
      z.1 + z.2 ≤ 2 * t / canonicalFaceHeight t := by
    constructor
    · intro h
      apply (le_div_iff₀ hh).2
      nlinarith
    · intro h
      have hmul := (le_div_iff₀ hh).1 h
      nlinarith
  have hNeg : -canonicalFaceRawAperture t / 2 =
      -2 * t / canonicalFaceHeight t := by
    unfold canonicalFaceRawAperture
    ring
  simpa [canonicalFaceRawRegion, canonicalFacePlanarTriangle,
    hEq, hNeg] using (and_congr hFirst (and_congr hSecond hThird))

/-- The parameter triangles increase with t. -/
theorem canonicalFacePlanarTriangle_mono {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    canonicalFacePlanarTriangle t ⊆ canonicalFacePlanarTriangle s := by
  have hOffset : canonicalFaceRawAperture t ≤
      canonicalFaceRawAperture s := by
    rcases eq_or_lt_of_le hts with heq | hlt
    · rw [heq]
    · exact (canonicalFaceRawAperture_strictMonoOn
        ht (lt_trans ht hlt) hlt).le
  intro z hz
  rcases hz with ⟨h1, h2, h3⟩
  change -canonicalFaceRawAperture s / 2 ≤ z.1 ∧
    -canonicalFaceRawAperture s / 2 ≤ z.2 ∧
    z.1 + z.2 ≤ canonicalFaceRawAperture s / 2
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The larger triangle contains a point in its strict interior which
is not in the smaller triangle. The point is explicit and rational in
the two offsets. -/
theorem canonicalFacePlanarTriangle_strict_witness {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ z : ℝ × ℝ,
      (-canonicalFaceRawAperture s / 2 < z.1) ∧
      (-canonicalFaceRawAperture s / 2 < z.2) ∧
      (z.1 + z.2 < canonicalFaceRawAperture s / 2) ∧
      z ∉ canonicalFacePlanarTriangle t := by
  let a : ℝ := canonicalFaceRawAperture t
  let b : ℝ := canonicalFaceRawAperture s
  have ha : 0 < a := by
    dsimp [a]
    rw [canonicalFaceRawAperture_eq]
    exact canonicalFaceAperture_pos ht
  have hab : a < b := canonicalFaceRawAperture_strictMonoOn
    ht (lt_trans ht hts) hts
  let z : ℝ × ℝ := (-(a + b) / 4, (a + b) / 8)
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · dsimp [z, b]
    linarith
  · dsimp [z, b]
    linarith
  · dsimp [z, b]
    linarith
  · intro hz
    have h0 := hz.1
    dsimp [canonicalFacePlanarTriangle, z, a] at h0
    linarith


/-- A relatively open planar patch lies inside the enlarged triangle and
strictly outside the smaller one.  It is a useful domain for the
positive-measure Hausdorff projection argument. -/
def canonicalFaceOpenDifference (t s : ℝ) : Set (ℝ × ℝ) :=
  {z | -canonicalFaceRawAperture s / 2 < z.1 ∧
       -canonicalFaceRawAperture s / 2 < z.2 ∧
       z.1 + z.2 < canonicalFaceRawAperture s / 2 ∧
       z.1 < -canonicalFaceRawAperture t / 2}

/-- Openness uses the ordinary Euclidean topology on R×R. -/
theorem canonicalFaceOpenDifference_isOpen (t s : ℝ) :
    IsOpen (canonicalFaceOpenDifference t s) := by
  have h1 : IsOpen {z : ℝ × ℝ | -canonicalFaceRawAperture s / 2 < z.1} :=
    isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {z : ℝ × ℝ | -canonicalFaceRawAperture s / 2 < z.2} :=
    isOpen_lt continuous_const continuous_snd
  have h3 : IsOpen {z : ℝ × ℝ | z.1 + z.2 < canonicalFaceRawAperture s / 2} :=
    isOpen_lt (continuous_fst.add continuous_snd) continuous_const
  have h4 : IsOpen {z : ℝ × ℝ | z.1 < -canonicalFaceRawAperture t / 2} :=
    isOpen_lt continuous_fst continuous_const
  change IsOpen ({z : ℝ × ℝ | -canonicalFaceRawAperture s / 2 < z.1} ∩
    ({z : ℝ × ℝ | -canonicalFaceRawAperture s / 2 < z.2} ∩
    ({z : ℝ × ℝ | z.1 + z.2 < canonicalFaceRawAperture s / 2} ∩
     {z : ℝ × ℝ | z.1 < -canonicalFaceRawAperture t / 2})))
  exact h1.inter (h2.inter (h3.inter h4))

/-- The explicit difference patch is nonempty whenever the parameter
grows strictly. -/
theorem canonicalFaceOpenDifference_nonempty
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (canonicalFaceOpenDifference t s).Nonempty := by
  let a : ℝ := canonicalFaceRawAperture t
  let b : ℝ := canonicalFaceRawAperture s
  have ha : 0 < a := by
    dsimp [a]
    rw [canonicalFaceRawAperture_eq]
    exact canonicalFaceAperture_pos ht
  have hab : a < b := canonicalFaceRawAperture_strictMonoOn
    ht (lt_trans ht hts) hts
  refine ⟨(-(a + b) / 4, (a + b) / 8), ?_⟩
  change -b / 2 < -(a + b) / 4 ∧
    -b / 2 < (a + b) / 8 ∧
    -(a + b) / 4 + (a + b) / 8 < b / 2 ∧
    -(a + b) / 4 < -a / 2
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Every point of the relatively open patch is in the larger triangle,
but not in the smaller. -/
theorem canonicalFaceOpenDifference_subset
    (t s : ℝ) :
    canonicalFaceOpenDifference t s ⊆
      canonicalFacePlanarTriangle s \ canonicalFacePlanarTriangle t := by
  intro z hz
  rcases hz with ⟨h1, h2, h3, h4⟩
  change (-canonicalFaceRawAperture s / 2 ≤ z.1 ∧
    -canonicalFaceRawAperture s / 2 ≤ z.2 ∧
    z.1 + z.2 ≤ canonicalFaceRawAperture s / 2) ∧
    z ∉ canonicalFacePlanarTriangle t
  constructor
  · exact ⟨h1.le, h2.le, h3.le⟩
  · intro hsmall
    exact (not_lt_of_ge hsmall.1) h4

end Sphere3
