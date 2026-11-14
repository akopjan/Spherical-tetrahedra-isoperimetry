module

public import Sphere3.CanonicalFaceSurjectivity

@[expose] public section

/-!
# Ambient isometries relating the moving canonical face planes

The plane of the first canonical face rotates in the 2-plane generated
by the vector (1,1,1,0) and the fourth coordinate axis. Its orthogonal
complement within the first three coordinates is fixed pointwise.

The exact rotation `R_{t,s}` has scalar coefficients

    c = (3+t*s)/(sqrt(3+t²)*sqrt(3+s²)),
    b = (s-t)/(sqrt(3+t²)*sqrt(3+s²)),

with `c² + 3*b² = 1`. It acts by

    R(x)_i = x_i + (c-1)*(x₀+x₁+x₂)/3 - b*x₃,    i=0,1,2,
    R(x)_3 = b*(x₀+x₁+x₂) + c*x₃.

These lemmas are intended to construct a *global ambient isometry* and
avoid invoking any two-dimensional surface-area formula.
-/

noncomputable section

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)

def canonicalFaceRotationC (t s : ℝ) : ℝ :=
  (3 + t * s) /
    (Real.sqrt (3 + t ^ 2) * Real.sqrt (3 + s ^ 2))

def canonicalFaceRotationB (t s : ℝ) : ℝ :=
  (s - t) /
    (Real.sqrt (3 + t ^ 2) * Real.sqrt (3 + s ^ 2))

/-- The identity `c²+3b²=1` makes the rotation orthogonal. -/
theorem canonicalFaceRotation_coeff_sq (t s : ℝ) :
    canonicalFaceRotationC t s ^ 2 +
      3 * canonicalFaceRotationB t s ^ 2 = 1 := by
  have ht : 0 < 3 + t ^ 2 := by positivity
  have hs : 0 < 3 + s ^ 2 := by positivity
  have hdt : (Real.sqrt (3 + t ^ 2)) ^ 2 = 3 + t ^ 2 :=
    Real.sq_sqrt ht.le
  have hds : (Real.sqrt (3 + s ^ 2)) ^ 2 = 3 + s ^ 2 :=
    Real.sq_sqrt hs.le
  have hprod := congrArg₂ (fun a b : ℝ => a * b) hdt hds
  have hden : Real.sqrt (3 + t ^ 2) * Real.sqrt (3 + s ^ 2) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.2 ht).ne' (Real.sqrt_pos.2 hs).ne'
  unfold canonicalFaceRotationC canonicalFaceRotationB
  field_simp [hden]
  nlinarith [hprod]

/-- A two-dimensional rotation, expressed in standard coordinates of ℝ⁴. -/
def canonicalFaceRotationMap (c b : ℝ) (x : E4) : E4 :=
  let v : ℝ := x 0 + x 1 + x 2
  !₂[x 0 + (c - 1) * v / 3 - b * x 3,
     x 1 + (c - 1) * v / 3 - b * x 3,
     x 2 + (c - 1) * v / 3 - b * x 3,
     b * v + c * x 3]

/-- The map is additive. -/
theorem canonicalFaceRotationMap_add (c b : ℝ) (x y : E4) :
    canonicalFaceRotationMap c b (x + y) =
      canonicalFaceRotationMap c b x + canonicalFaceRotationMap c b y := by
  ext i
  fin_cases i <;>
    simp [canonicalFaceRotationMap] <;> ring

/-- The map respects scalar multiplication. -/
theorem canonicalFaceRotationMap_smul
    (c b r : ℝ) (x : E4) :
    canonicalFaceRotationMap c b (r • x) =
      r • canonicalFaceRotationMap c b x := by
  ext i
  fin_cases i <;>
    simp [canonicalFaceRotationMap] <;> ring

theorem canonicalFaceRotationMap_zero (c b : ℝ) :
    canonicalFaceRotationMap c b (0 : E4) = 0 := by
  ext i
  fin_cases i <;> simp [canonicalFaceRotationMap]

theorem canonicalFaceRotationMap_sub (c b : ℝ) (x y : E4) :
    canonicalFaceRotationMap c b (x - y) =
      canonicalFaceRotationMap c b x - canonicalFaceRotationMap c b y := by
  ext i
  fin_cases i <;>
    simp [canonicalFaceRotationMap] <;> ring

/-- A polynomial identity valid without any orthogonality assumption. -/
theorem canonicalFaceRotationMap_norm_sq (c b : ℝ) (x : E4) :
    ‖canonicalFaceRotationMap c b x‖ ^ 2 =
      ‖x‖ ^ 2 +
        (c ^ 2 + 3 * b ^ 2 - 1) *
          (((x 0 + x 1 + x 2) ^ 2) / 3 + (x 3) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq (canonicalFaceRotationMap c b x),
    EuclideanSpace.real_norm_sq_eq x]
  simp [canonicalFaceRotationMap, Fin.sum_univ_succ]
  ring

/-- If `c²+3b²=1`, the ambient rotation preserves all distances. -/
theorem canonicalFaceRotationMap_isometry (c b : ℝ)
    (h : c ^ 2 + 3 * b ^ 2 = 1) :
    Isometry (canonicalFaceRotationMap c b) := by
  have hnorm (x : E4) : ‖canonicalFaceRotationMap c b x‖ = ‖x‖ := by
    have hsq := canonicalFaceRotationMap_norm_sq c b x
    rw [h, sub_self, zero_mul, add_zero] at hsq
    nlinarith [norm_nonneg (canonicalFaceRotationMap c b x), norm_nonneg x]
  intro x y
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm,
    ← canonicalFaceRotationMap_sub, hnorm]

/-- The canonical parameter-dependent rotation is a global ambient
isometry for every pair of real parameters, without restricting to a
specific face or assuming positivity of the parameters. -/
def canonicalFaceRotation (t s : ℝ) (x : E4) : E4 :=
  canonicalFaceRotationMap
    (canonicalFaceRotationC t s) (canonicalFaceRotationB t s) x

theorem canonicalFaceRotation_isometry (t s : ℝ) :
    Isometry (canonicalFaceRotation t s) := by
  exact canonicalFaceRotationMap_isometry _ _
    (canonicalFaceRotation_coeff_sq t s)

/-- Reversing t and s reverses the sine coefficient. -/
theorem canonicalFaceRotation_reverse_coeff (t s : ℝ) :
    canonicalFaceRotationC s t = canonicalFaceRotationC t s ∧
    canonicalFaceRotationB s t = -canonicalFaceRotationB t s := by
  constructor
  · unfold canonicalFaceRotationC
    rw [mul_comm s t, mul_comm (Real.sqrt (3 + s ^ 2))]
  · unfold canonicalFaceRotationB
    rw [← neg_sub s t, neg_div, mul_comm (Real.sqrt (3 + s ^ 2))]



/-- The ratio of face-axis lengths is the ratio of the normal-plane
radicals, with the same `sqrt 3` factor cancelling. -/
theorem canonicalFaceHeight_ratio (t s : ℝ) :
    canonicalFaceHeight t / canonicalFaceHeight s =
      Real.sqrt (3 + t ^ 2) / Real.sqrt (3 + s ^ 2) := by
  rw [canonicalFaceHeight_eq, canonicalFaceHeight_eq]
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs : Real.sqrt (3 + s ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp [h3, hs]

/-- Scalar identities ensuring that rotation maps the affine chart of
the first face to its counterpart at the new height parameter. -/
theorem canonicalFaceRotation_height_identities (t s : ℝ) :
    (canonicalFaceRotationC t s - canonicalFaceRotationB t s * t) *
        canonicalFaceHeight s = canonicalFaceHeight t ∧
    (canonicalFaceRotationC t s * t + 3 * canonicalFaceRotationB t s) *
        canonicalFaceHeight s = canonicalFaceHeight t * s := by
  have ht : 0 < 3 + t ^ 2 := by positivity
  have hs : 0 < 3 + s ^ 2 := by positivity
  let dt : ℝ := Real.sqrt (3 + t ^ 2)
  let ds : ℝ := Real.sqrt (3 + s ^ 2)
  have hdt : dt ^ 2 = 3 + t ^ 2 := Real.sq_sqrt ht.le
  have hdt0 : dt ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hds0 : ds ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have hratio : canonicalFaceHeight t / canonicalFaceHeight s =
      dt / ds := canonicalFaceHeight_ratio t s
  have hdiv : (3 + t ^ 2) / (dt * ds) = dt / ds := by
    rw [← hdt]
    field_simp [hdt0, hds0]
  have hc1 : canonicalFaceRotationC t s -
      canonicalFaceRotationB t s * t =
      (3 + t ^ 2) / (dt * ds) := by
    unfold canonicalFaceRotationC canonicalFaceRotationB
    dsimp [dt, ds]
    ring
  have hc2 : canonicalFaceRotationC t s * t +
      3 * canonicalFaceRotationB t s =
      s * ((3 + t ^ 2) / (dt * ds)) := by
    unfold canonicalFaceRotationC canonicalFaceRotationB
    dsimp [dt, ds]
    ring
  constructor
  · rw [hc1, hdiv, ← hratio]
    exact div_mul_cancel₀ _ (canonicalFaceHeight_pos s).ne'
  · rw [hc2, hdiv, ← hratio]
    calc
      s * (canonicalFaceHeight t / canonicalFaceHeight s) *
          canonicalFaceHeight s =
        s * ((canonicalFaceHeight t / canonicalFaceHeight s) *
          canonicalFaceHeight s) := by ring
      _ = s * canonicalFaceHeight t := by
        rw [div_mul_cancel₀ _ (canonicalFaceHeight_pos s).ne']
      _ = canonicalFaceHeight t * s := by ring

/-- Exact conjugacy between raw parameter charts under ambient rotation.
The scalar is strictly positive because both chart heights are positive. -/
theorem canonicalFaceRotation_raw_chart (t s p q : ℝ) :
    canonicalFaceRotation t s (canonicalFaceRawLift t p q) =
      (canonicalFaceHeight t / canonicalFaceHeight s) •
        canonicalFaceRawLift s p q := by
  have hi := canonicalFaceRotation_height_identities t s
  have hs : canonicalFaceHeight s ≠ 0 := (canonicalFaceHeight_pos s).ne'
  ext i
  fin_cases i <;>
    simp [canonicalFaceRotation, canonicalFaceRotationMap,
      canonicalFaceRawLift] <;>
    field_simp [hs] <;>
    nlinarith [hi.1, hi.2]

/-- The normalized face charts are related by a single global ambient
isometry, and therefore have exactly equal Hausdorff measures on the
images of any shared parameter domain. -/
theorem canonicalFaceRotation_chart (t s p q : ℝ) :
    canonicalFaceRotation t s (canonicalFacePoint t p q) =
      canonicalFacePoint s p q := by
  let Ct : E4 := canonicalFaceRawLift t p q
  let Cs : E4 := canonicalFaceRawLift s p q
  let k : ℝ := canonicalFaceHeight t / canonicalFaceHeight s
  have hk : 0 < k := div_pos (canonicalFaceHeight_pos t)
    (canonicalFaceHeight_pos s)
  have hraw : canonicalFaceRotation t s Ct = k • Cs :=
    canonicalFaceRotation_raw_chart t s p q
  have hnCt : 0 < ‖Ct‖ := canonicalFaceRawLift_norm_pos t p q
  have hnCs : 0 < ‖Cs‖ := canonicalFaceRawLift_norm_pos s p q
  have hNormRot : ‖canonicalFaceRotation t s Ct‖ = ‖Ct‖ := by
    have hdist := (canonicalFaceRotation_isometry t s).dist_eq Ct (0 : E4)
    simpa [canonicalFaceRotation, canonicalFaceRotationMap_zero,
      dist_zero_right] using hdist
  have hNorm : ‖Ct‖ = k * ‖Cs‖ := by
    rw [hraw, norm_smul, Real.norm_eq_abs, abs_of_pos hk] at hNormRot
    exact hNormRot.symm
  change canonicalFaceRotation t s (‖Ct‖⁻¹ • Ct) = ‖Cs‖⁻¹ • Cs
  unfold canonicalFaceRotation
  rw [canonicalFaceRotationMap_smul, ← canonicalFaceRotation,
    hraw, smul_smul, hNorm]
  have hc : (k * ‖Cs‖)⁻¹ * k = ‖Cs‖⁻¹ := by
    field_simp [hk.ne', hnCs.ne']
  rw [hc]

/-- A moving face is carried into the new face by an ambient isometry,
provided its planar parameters belong to the new triangle. -/
theorem canonicalFaceRotation_mem_new_face
    (t s : ℝ) (hs : 0 < s) (p q : ℝ)
    (hParam : (p, q) ∈ canonicalFacePlanarTriangle s) :
    canonicalFaceRotation t s (canonicalFacePoint t p q) ∈
      (SphericalTetrahedron.canonicalTetrahedron s hs).face 0 := by
  rw [canonicalFaceRotation_chart]
  apply (canonicalFacePoint_mem_first_face_iff s hs p q).mpr
  rwa [canonicalFaceRawRegion_eq_triangle]

/-- The rotating isometry maps every earlier canonical first face into
the later face. This uses only exact domain nesting and the face chart. -/
theorem canonicalFaceRotation_first_face_subset
    {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    canonicalFaceRotation t s ''
        (SphericalTetrahedron.canonicalTetrahedron t ht).face 0 ⊆
      (SphericalTetrahedron.canonicalTetrahedron s
        (lt_of_lt_of_le ht hts)).face 0 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [canonicalTetrahedron_first_face_eq_chart] at hy
  rcases hy with ⟨z, hz, rfl⟩
  exact canonicalFaceRotation_mem_new_face t s (lt_of_lt_of_le ht hts)
    z.1 z.2 (canonicalFacePlanarTriangle_mono ht hts hz)

end Sphere3
