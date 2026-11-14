module

public import Sphere3.CanonicalFaceFiniteBridge
public import Sphere3.GnomonicLipschitz
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NNNorm

@[expose] public section

/-!
# Global Lipschitz bound for the canonical two-dimensional face chart

The unnormalized chart F_t : R×R -> R^4 is affine, with linear part

    L_t(p,q) = (h_t p, h_t q, -h_t(p+q), 0),
    h_t = sqrt(9+3t^2).

Its norm is >= 3 at every point.  A finite-dimensional linear map is
continuous and Lipschitz; radial normalization on vectors of norm >= 1
has Lipschitz constant at most 2.  Thus the entire normalized chart is
globally Lipschitz, and the face has *finite raw H^2 measure*.
-/

noncomputable section

open MeasureTheory

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- The linear part of the raw canonical face parametrization. -/
def canonicalFaceAffineLinear (t : ℝ) : (ℝ × ℝ) →ₗ[ℝ] E4 where
  toFun z := !₂[canonicalFaceHeight t * z.1,
      canonicalFaceHeight t * z.2,
      -canonicalFaceHeight t * (z.1 + z.2),
      0]
  map_add' := by
    intro z w
    ext i
    fin_cases i <;>
      simp [mul_add] <;> ring
  map_smul' := by
    intro r z
    ext i
    fin_cases i <;>
      simp [smul_eq_mul] <;> ring

/-- The raw lift is a translation of the finite-dimensional linear map. -/
theorem canonicalFaceRawLift_sub_eq_linear
    (t : ℝ) (z w : ℝ × ℝ) :
    canonicalFaceRawLift t z.1 z.2 - canonicalFaceRawLift t w.1 w.2 =
      canonicalFaceAffineLinear t (z - w) := by
  ext i
  fin_cases i <;>
    simp [canonicalFaceRawLift, canonicalFaceAffineLinear] <;> ring

/-- A uniform lower norm bound; the fourth coordinate is always 3. -/
theorem canonicalFaceRawLift_norm_ge_one (t p q : ℝ) :
    1 ≤ ‖canonicalFaceRawLift t p q‖ := by
  have hQ : 1 ≤ canonicalFaceQ p q := by
    unfold canonicalFaceQ
    nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg (p + q)]
  have hProd : (9 : ℝ) ≤
      (9 + 3 * t ^ 2) * canonicalFaceQ p q := by
    calc
      (9 : ℝ) ≤ 9 + 3 * t ^ 2 := by nlinarith [sq_nonneg t]
      _ = (9 + 3 * t ^ 2) * 1 := by ring
      _ ≤ (9 + 3 * t ^ 2) * canonicalFaceQ p q :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
  have hSquare := canonicalFaceRawLift_norm_sq t p q
  nlinarith [norm_nonneg (canonicalFaceRawLift t p q)]

/-- The normalized canonical face map is globally Lipschitz on R×R. -/
theorem canonicalFacePoint_lipschitz_exists (t : ℝ) :
    ∃ K : NNReal, LipschitzWith K
      (fun z : ℝ × ℝ => canonicalFacePoint t z.1 z.2) := by
  let l : (ℝ × ℝ) →L[ℝ] E4 :=
    LinearMap.toContinuousLinearMap (canonicalFaceAffineLinear t)
  refine ⟨2 * ‖l‖₊, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hNormZ := canonicalFaceRawLift_norm_ge_one t z.1 z.2
  have hNormW := canonicalFaceRawLift_norm_ge_one t w.1 w.2
  have hRad := radialNormalization_two_lipschitz_pair
    (canonicalFaceRawLift t z.1 z.2)
    (canonicalFaceRawLift t w.1 w.2) hNormZ hNormW
  have hLinDiff :
      canonicalFaceRawLift t z.1 z.2 - canonicalFaceRawLift t w.1 w.2 =
        l (z - w) := by
    simpa [l] using canonicalFaceRawLift_sub_eq_linear t z w
  have hLinBound :
      ‖l (z - w)‖ ≤ (‖l‖₊ : ℝ) * ‖z - w‖ := by
    simpa only [dist_eq_norm, map_sub] using
      (l.lipschitzWith.dist_le_mul z w)
  change dist (canonicalFacePoint t z.1 z.2)
    (canonicalFacePoint t w.1 w.2) ≤
      (↑(2 * ‖l‖₊) : ℝ) * dist z w
  calc
    dist (canonicalFacePoint t z.1 z.2)
      (canonicalFacePoint t w.1 w.2) =
        ‖‖canonicalFaceRawLift t z.1 z.2‖⁻¹ •
            canonicalFaceRawLift t z.1 z.2 -
          ‖canonicalFaceRawLift t w.1 w.2‖⁻¹ •
            canonicalFaceRawLift t w.1 w.2‖ := by
          rfl
    _ ≤ 2 * ‖l (z - w)‖ := by
      rw [← hLinDiff]
      exact hRad
    _ ≤ 2 * ((‖l‖₊ : ℝ) * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left hLinBound (by norm_num)
    _ = (↑(2 * ‖l‖₊) : ℝ) * dist z w := by
      simp only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat]
      ring

/-- Finiteness of original (unnormalized) H² on every canonical face,
without using any polar Jacobian or Girard's formula. -/
theorem canonical_first_face_hausdorff_finite
    (t : ℝ) (ht : 0 < t) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E4)
      ((SphericalTetrahedron.canonicalTetrahedron t ht).face 0) ≠ ⊤ := by
  obtain ⟨K, hLip⟩ := canonicalFacePoint_lipschitz_exists t
  exact canonical_first_face_hausdorff_finite_of_lipschitz t ht K hLip

end Sphere3
