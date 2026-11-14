module

public import Sphere3.HausdorffTwoProjection
public import Sphere3.CanonicalFaceRotation

@[expose] public section

/-!
# The projected fixed-plane gnomonic chart is a diffeomorphism onto an ellipse

For the canonical first-face chart at parameter t=0, first-two-coordinate
projection gives the planar map

    k(p,q) = (p,q)/sqrt(Q(p,q)),
    Q(p,q) = 1 + p^2 + q^2 + (p+q)^2.

Its image is the open ellipse

    D(u,v) = 1 - u^2 - v^2 - (u+v)^2 > 0,

and the inverse is (u,v)/sqrt(D(u,v)). The exact inverse formulas show
that a nonempty open subset of the expanding planar triangle projects to
an open planar patch, and hence has positive raw H^2 measure.

This module establishes the inverse identities, inverse continuity on the
ellipse, and the planar open-mapping property used to prove
`canonical_first_face_strict`.
-/

noncomputable section

namespace Sphere3

/-- The fixed gnomonic chart's positive quadratic denominator. -/
def canonicalFaceDiskQ (z : ℝ × ℝ) : ℝ :=
  1 + z.1 ^ 2 + z.2 ^ 2 + (z.1 + z.2) ^ 2

/-- A globally defined planar version of the spherical gnomonic map. -/
def canonicalFaceDiskMap (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 / Real.sqrt (canonicalFaceDiskQ z),
   z.2 / Real.sqrt (canonicalFaceDiskQ z))

/-- The defining quadratic of the open elliptical disk. -/
def canonicalFaceDiskDefect (z : ℝ × ℝ) : ℝ :=
  1 - z.1 ^ 2 - z.2 ^ 2 - (z.1 + z.2) ^ 2

def canonicalFaceDisk (z : ℝ × ℝ) : Prop :=
  0 < canonicalFaceDiskDefect z

/-- The explicit inverse of the disk chart on points of positive defect. -/
def canonicalFaceDiskInverse (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 / Real.sqrt (canonicalFaceDiskDefect z),
   z.2 / Real.sqrt (canonicalFaceDiskDefect z))

theorem canonicalFaceDiskQ_pos (z : ℝ × ℝ) :
    0 < canonicalFaceDiskQ z := by
  unfold canonicalFaceDiskQ
  positivity

/-- Eliminating the square root in the disk-defect identity. -/
theorem canonicalFaceDiskDefect_div (p q r : ℝ)
    (hr : r ^ 2 = 1 + p ^ 2 + q ^ 2 + (p + q) ^ 2)
    (hr0 : r ≠ 0) :
    1 - (p / r) ^ 2 - (q / r) ^ 2 -
      (p / r + q / r) ^ 2 = 1 / r ^ 2 := by
  field_simp [hr0]
  nlinarith [hr]

/-- In disk coordinates, the elliptic defect is exactly 1/Q. -/
theorem canonicalFaceDiskDefect_map (z : ℝ × ℝ) :
    canonicalFaceDiskDefect (canonicalFaceDiskMap z) =
      1 / canonicalFaceDiskQ z := by
  have hq : 0 < canonicalFaceDiskQ z := canonicalFaceDiskQ_pos z
  have hroot : Real.sqrt (canonicalFaceDiskQ z) ≠ 0 :=
    (Real.sqrt_pos.2 hq).ne'
  have hsquare : (Real.sqrt (canonicalFaceDiskQ z)) ^ 2 =
      1 + z.1 ^ 2 + z.2 ^ 2 + (z.1 + z.2) ^ 2 := by
    rw [Real.sq_sqrt hq.le]
    rfl
  have hdiv := canonicalFaceDiskDefect_div z.1 z.2
    (Real.sqrt (canonicalFaceDiskQ z)) hsquare hroot
  change 1 - (z.1 / Real.sqrt (canonicalFaceDiskQ z)) ^ 2 -
    (z.2 / Real.sqrt (canonicalFaceDiskQ z)) ^ 2 -
    (z.1 / Real.sqrt (canonicalFaceDiskQ z) +
      z.2 / Real.sqrt (canonicalFaceDiskQ z)) ^ 2 =
      1 / canonicalFaceDiskQ z
  calc
    _ = 1 / (Real.sqrt (canonicalFaceDiskQ z)) ^ 2 := hdiv
    _ = 1 / canonicalFaceDiskQ z := by rw [Real.sq_sqrt hq.le]

/-- The planar gnomonic projection maps every real parameter into the
open ellipse, without excluding any finite parameter values. -/
theorem canonicalFaceDiskMap_mem (z : ℝ × ℝ) :
    canonicalFaceDisk (canonicalFaceDiskMap z) := by
  unfold canonicalFaceDisk
  rw [canonicalFaceDiskDefect_map]
  exact one_div_pos.mpr (canonicalFaceDiskQ_pos z)

/-- A positive elliptic defect gives an exact normalization identity. -/
theorem canonicalFaceDiskQ_inverse (z : ℝ × ℝ)
    (hz : canonicalFaceDisk z) :
    canonicalFaceDiskQ (canonicalFaceDiskInverse z) =
      1 / canonicalFaceDiskDefect z := by
  have hd : 0 < canonicalFaceDiskDefect z := hz
  have hroot : Real.sqrt (canonicalFaceDiskDefect z) ≠ 0 :=
    (Real.sqrt_pos.2 hd).ne'
  have hsquare : Real.sqrt (canonicalFaceDiskDefect z) ^ 2 =
      canonicalFaceDiskDefect z := Real.sq_sqrt hd.le
  unfold canonicalFaceDiskQ canonicalFaceDiskInverse
  field_simp [hroot, hd.ne']
  rw [hsquare]
  unfold canonicalFaceDiskDefect
  ring

/-- Explicit left inverse of the gnomonic disk chart. -/
theorem canonicalFaceDiskInverse_map (z : ℝ × ℝ) :
    canonicalFaceDiskInverse (canonicalFaceDiskMap z) = z := by
  have hq : 0 < canonicalFaceDiskQ z := canonicalFaceDiskQ_pos z
  have hs : 0 < Real.sqrt (canonicalFaceDiskQ z) := Real.sqrt_pos.2 hq
  have hd : 0 < canonicalFaceDiskDefect (canonicalFaceDiskMap z) :=
    canonicalFaceDiskMap_mem z
  have hroot : Real.sqrt
      (canonicalFaceDiskDefect (canonicalFaceDiskMap z)) =
        (Real.sqrt (canonicalFaceDiskQ z))⁻¹ := by
    have hsq : Real.sqrt
        (canonicalFaceDiskDefect (canonicalFaceDiskMap z)) ^ 2 =
          ((Real.sqrt (canonicalFaceDiskQ z))⁻¹) ^ 2 := by
      rw [Real.sq_sqrt hd.le, canonicalFaceDiskDefect_map,
        inv_pow, Real.sq_sqrt hq.le, one_div]
    nlinarith [Real.sqrt_nonneg
      (canonicalFaceDiskDefect (canonicalFaceDiskMap z)), inv_pos.mpr hs]
  apply Prod.ext
  · change (z.1 / Real.sqrt (canonicalFaceDiskQ z)) /
        Real.sqrt (canonicalFaceDiskDefect (canonicalFaceDiskMap z)) = z.1
    rw [hroot, div_inv_eq_mul, div_mul_cancel₀ _ hs.ne']
  · change (z.2 / Real.sqrt (canonicalFaceDiskQ z)) /
        Real.sqrt (canonicalFaceDiskDefect (canonicalFaceDiskMap z)) = z.2
    rw [hroot, div_inv_eq_mul, div_mul_cancel₀ _ hs.ne']

/-- The disk map is injective on all of R^2. -/
theorem canonicalFaceDiskMap_injective :
    Function.Injective canonicalFaceDiskMap := by
  intro z w h
  calc
    z = canonicalFaceDiskInverse (canonicalFaceDiskMap z) :=
      (canonicalFaceDiskInverse_map z).symm
    _ = canonicalFaceDiskInverse (canonicalFaceDiskMap w) := congrArg _ h
    _ = w := canonicalFaceDiskInverse_map w


/-- The inverse map is also a right inverse on the open ellipse. -/
theorem canonicalFaceDiskMap_inverse (z : ℝ × ℝ)
    (hz : canonicalFaceDisk z) :
    canonicalFaceDiskMap (canonicalFaceDiskInverse z) = z := by
  have hd : 0 < canonicalFaceDiskDefect z := hz
  have hr : Real.sqrt (canonicalFaceDiskDefect z) ≠ 0 :=
    (Real.sqrt_pos.2 hd).ne'
  have hQ : Real.sqrt (canonicalFaceDiskQ
      (canonicalFaceDiskInverse z)) =
        (Real.sqrt (canonicalFaceDiskDefect z))⁻¹ := by
    rw [canonicalFaceDiskQ_inverse z hz]
    simpa only [one_div] using (Real.sqrt_inv (canonicalFaceDiskDefect z))
  apply Prod.ext
  · change (z.1 / Real.sqrt (canonicalFaceDiskDefect z)) /
      Real.sqrt (canonicalFaceDiskQ (canonicalFaceDiskInverse z)) = z.1
    rw [hQ, div_div, mul_inv_cancel₀ hr, div_one]
  · change (z.2 / Real.sqrt (canonicalFaceDiskDefect z)) /
      Real.sqrt (canonicalFaceDiskQ (canonicalFaceDiskInverse z)) = z.2
    rw [hQ, div_div, mul_inv_cancel₀ hr, div_one]

/-- The image of ANY subset under the disk map is an explicit
intersection of the open disk with the inverse-image condition. -/
theorem canonicalFaceDiskMap_image_eq (U : Set (ℝ × ℝ)) :
    canonicalFaceDiskMap '' U =
      {z | canonicalFaceDisk z ∧ canonicalFaceDiskInverse z ∈ U} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨canonicalFaceDiskMap_mem w, by
      simpa [canonicalFaceDiskInverse_map] using hw⟩
  · intro hz
    exact ⟨canonicalFaceDiskInverse z, hz.2,
      canonicalFaceDiskMap_inverse z hz.1⟩

/-- The ellipse is an ordinary open subset of the Euclidean plane. -/
theorem canonicalFaceDisk_isOpen :
    IsOpen {z : ℝ × ℝ | canonicalFaceDisk z} := by
  have hc : Continuous canonicalFaceDiskDefect := by
    unfold canonicalFaceDiskDefect
    fun_prop
  exact isOpen_lt continuous_const hc

/-- The inverse is continuous on the open ellipse. -/
theorem canonicalFaceDiskInverse_continuousOn :
    ContinuousOn canonicalFaceDiskInverse
      {z : ℝ × ℝ | canonicalFaceDisk z} := by
  have hc : Continuous canonicalFaceDiskDefect := by
    unfold canonicalFaceDiskDefect
    fun_prop
  have hroot : ContinuousOn
      (fun z : ℝ × ℝ => Real.sqrt (canonicalFaceDiskDefect z))
      {z : ℝ × ℝ | canonicalFaceDisk z} :=
    (Real.continuous_sqrt.comp hc).continuousOn
  have hne : ∀ z ∈ {z : ℝ × ℝ | canonicalFaceDisk z},
      Real.sqrt (canonicalFaceDiskDefect z) ≠ 0 := by
    intro z hz
    exact (Real.sqrt_pos.2 hz).ne'
  change ContinuousOn (fun z : ℝ × ℝ =>
    (z.1 / Real.sqrt (canonicalFaceDiskDefect z),
     z.2 / Real.sqrt (canonicalFaceDiskDefect z))) _
  exact (continuous_fst.continuousOn.div hroot hne).prodMk
    (continuous_snd.continuousOn.div hroot hne)

/-- The projected fixed-face chart is an open map onto its ellipse.
The proof uses the exact inverse, not a differentiable inverse theorem. -/
theorem canonicalFaceDiskMap_isOpenMap :
    IsOpenMap canonicalFaceDiskMap := by
  intro U hU
  rw [canonicalFaceDiskMap_image_eq]
  change IsOpen
    ({z : ℝ × ℝ | canonicalFaceDisk z} ∩
      canonicalFaceDiskInverse ⁻¹' U)
  exact canonicalFaceDiskInverse_continuousOn.isOpen_inter_preimage
    canonicalFaceDisk_isOpen hU


end Sphere3
