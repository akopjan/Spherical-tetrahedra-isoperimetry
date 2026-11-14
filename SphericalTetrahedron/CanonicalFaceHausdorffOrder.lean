module

public import SphericalTetrahedron.CanonicalFaceOrderReduction
public import Sphere3.CanonicalFaceGlobalLipschitz
public import Sphere3.CanonicalFaceRotation
public import Sphere3.MeasureGrowth

@[expose] public section

/-!
# Hausdorff comparison of canonical spherical faces via an ambient rotation

The rotation of `Sphere3.CanonicalFaceRotation` transports the smaller
canonical first face into the larger one. Because the transformation is an
ambient Euclidean isometry, **the original raw two-dimensional Hausdorff
measure** is preserved. This establishes weak monotonicity unconditionally.

The second result isolates the only strictness inputs: finiteness of the
small face, and strictly positive Hausdorff measure of the difference.
A finite measure of the larger face is needed separately for the `toReal`
statement used by the benchmark; this cannot be omitted since
`ENNReal.toReal ⊤ = 0`.
-/

noncomputable section

open MeasureTheory

namespace SphericalTetrahedron

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The smaller canonical first face has at most as much actual H^2
measure as the larger one, even though their supporting planes differ. -/
theorem canonical_first_face_hausdorff_mono
    {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron t ht).face 0) ≤
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_of_lt_of_le ht hts)).face 0) := by
  let μ : Measure E4 := Measure.hausdorffMeasure (2 : ℝ)
  let T := canonicalTetrahedron t ht
  let S := canonicalTetrahedron s (lt_of_lt_of_le ht hts)
  let f : E4 → E4 := Sphere3.canonicalFaceRotation t s
  have hf : Isometry f := Sphere3.canonicalFaceRotation_isometry t s
  have hincl : f '' T.face 0 ⊆ S.face 0 :=
    Sphere3.canonicalFaceRotation_first_face_subset ht hts
  have hiso : μ (f '' T.face 0) = μ (T.face 0) :=
    hf.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) (T.face 0)
  change μ (T.face 0) ≤ μ (S.face 0)
  calc
    μ (T.face 0) = μ (f '' T.face 0) := hiso.symm
    _ ≤ μ (S.face 0) := measure_mono hincl

/-- Exact strictness criterion without presupposing a normalization
constant for Hausdorff measure. The difference is formed after rotating
the smaller face into the larger face's supporting plane. -/
theorem canonical_first_face_hausdorff_strict_of_patch
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hSmallFinite :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron t ht).face 0) ≠ ⊤)
    (hPatchPos : 0 <
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0 \
          (Sphere3.canonicalFaceRotation t s) ''
            ((canonicalTetrahedron t ht).face 0))) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron t ht).face 0) <
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0) := by
  let μ : Measure E4 := Measure.hausdorffMeasure (2 : ℝ)
  let T := canonicalTetrahedron t ht
  let S := canonicalTetrahedron s (lt_trans ht hts)
  let f : E4 → E4 := Sphere3.canonicalFaceRotation t s
  have hf : Isometry f := Sphere3.canonicalFaceRotation_isometry t s
  have hincl : f '' T.face 0 ⊆ S.face 0 :=
    Sphere3.canonicalFaceRotation_first_face_subset ht hts.le
  have hiso : μ (f '' T.face 0) = μ (T.face 0) :=
    hf.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) (T.face 0)
  have hMeas : MeasurableSet (f '' T.face 0) :=
    ((face_isCompact T 0).image hf.continuous).isClosed.measurableSet
  have hFinImage : μ (f '' T.face 0) ≠ ⊤ := by
    rw [hiso]
    exact hSmallFinite
  change μ (T.face 0) < μ (S.face 0)
  calc
    μ (T.face 0) = μ (f '' T.face 0) := hiso.symm
    _ < μ (S.face 0) :=
      Sphere3.measure_lt_of_positive_sdiff μ hincl hMeas hFinImage hPatchPos

/-- Conversion of strict extended measure inequality to the real-valued
challenge area requires finite measure of the LARGER face. -/
theorem canonical_first_face_area_strict_of_patch
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hSmallFinite :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron t ht).face 0) ≠ ⊤)
    (hBigFinite :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0) ≠ ⊤)
    (hPatchPos : 0 <
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0 \
          Sphere3.canonicalFaceRotation t s ''
            ((canonicalTetrahedron t ht).face 0))) :
    canonicalFirstFaceArea t ht <
      canonicalFirstFaceArea s (lt_trans ht hts) := by
  unfold canonicalFirstFaceArea SphericalTetrahedron.measure
  exact ENNReal.toReal_strict_mono hBigFinite
    (canonical_first_face_hausdorff_strict_of_patch ht hts
      hSmallFinite hPatchPos)


/-- Strict growth can be derived from just the finite face measures
and a nonempty open set in the two-coordinate projection of the
rotated face-difference patch.  This is the final generic H^2 bridge
needed before instantiating the explicit planar disk chart. -/
theorem canonical_first_face_area_strict_of_open_projection
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hSmallFinite :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron t ht).face 0) ≠ ⊤)
    (hBigFinite :
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0) ≠ ⊤)
    (O : Set (EuclideanSpace ℝ (Fin 2)))
    (hOopen : IsOpen O) (hOne : O.Nonempty)
    (hOSubset : O ⊆ Sphere3.canonicalTwoProjection ''
      (Sphere3.canonicalFaceRotation s 0 ''
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0 \
          Sphere3.canonicalFaceRotation t s ''
            (canonicalTetrahedron t ht).face 0))) :
    canonicalFirstFaceArea t ht <
      canonicalFirstFaceArea s (lt_trans ht hts) := by
  let U : Set E4 :=
    (canonicalTetrahedron s (lt_trans ht hts)).face 0 \
      Sphere3.canonicalFaceRotation t s ''
        (canonicalTetrahedron t ht).face 0
  have hPosRot : 0 <
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        (Sphere3.canonicalFaceRotation s 0 '' U) :=
    Sphere3.canonicalTwoProjection_patch_hausdorff_pos
      hOopen hOne hOSubset
  have hIso := (Sphere3.canonicalFaceRotation_isometry s 0).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) U
  have hPosU : 0 <
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4) U := by
    rwa [hIso] at hPosRot
  exact canonical_first_face_area_strict_of_patch
    ht hts hSmallFinite hBigFinite hPosU


/-- After the global Lipschitz estimate, strict Hausdorff-area growth
requires only positive measure of the explicit geometric patch.
Both face-finiteness assumptions are discharged unconditionally. -/
theorem canonical_first_face_area_strict_of_positive_patch
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (hPatchPos : 0 <
      (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0 \
          Sphere3.canonicalFaceRotation t s ''
            (canonicalTetrahedron t ht).face 0)) :
    canonicalFirstFaceArea t ht <
      canonicalFirstFaceArea s (lt_trans ht hts) := by
  exact canonical_first_face_area_strict_of_patch ht hts
    (Sphere3.canonical_first_face_hausdorff_finite t ht)
    (Sphere3.canonical_first_face_hausdorff_finite s (lt_trans ht hts))
    hPatchPos

/-- Equivalent final criterion: the genuine face-difference patch has
an open nonempty image under the two-coordinate projection after
rotation to the fixed face plane.  Neither face-finiteness nor any
Girard identity is needed as an additional premise. -/
theorem canonical_first_face_area_strict_of_open_projection_final
    {t s : ℝ} (ht : 0 < t) (hts : t < s)
    (O : Set (EuclideanSpace ℝ (Fin 2)))
    (hOopen : IsOpen O) (hOne : O.Nonempty)
    (hOSubset : O ⊆ Sphere3.canonicalTwoProjection ''
      (Sphere3.canonicalFaceRotation s 0 ''
        ((canonicalTetrahedron s (lt_trans ht hts)).face 0 \
          Sphere3.canonicalFaceRotation t s ''
            (canonicalTetrahedron t ht).face 0))) :
    canonicalFirstFaceArea t ht <
      canonicalFirstFaceArea s (lt_trans ht hts) := by
  exact canonical_first_face_area_strict_of_open_projection ht hts
    (Sphere3.canonical_first_face_hausdorff_finite t ht)
    (Sphere3.canonical_first_face_hausdorff_finite s (lt_trans ht hts))
    O hOopen hOne hOSubset

end SphericalTetrahedron
