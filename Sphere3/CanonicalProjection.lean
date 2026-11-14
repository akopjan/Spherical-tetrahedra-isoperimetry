module

public import Sphere3.CanonicalPatch
public import Sphere3.HausdorffProjection
public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section

/-!
# A projected open patch in the canonical spherical tetrahedron

Project `R⁴` to its first three coordinates. The coordinate projection is
1-Lipschitz and admits the explicit inverse upper-hemisphere graph
`u ↦ (u,sqrt(1-‖u‖²))` on the Euclidean unit ball. Every strict canonical
spherical patch contains a nonempty open chart of this form; its
projection therefore contains an open subset of `R³`.

Together with the standard full-dimensional Hausdorff measure positivity
instance on Euclidean `R³`, this supplies the projected open patch.
-/

noncomputable section

open MeasureTheory

namespace Sphere3

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Discard the fourth Euclidean coordinate. -/
def canonicalProjection (x : E4) : E3 :=
  WithLp.toLp 2 (fun i : Fin 3 => x (Fin.castSucc i))

/-- Exact Pythagorean identity for the coordinate projection. -/
theorem canonicalProjection_norm_sq (x : E4) :
    ‖canonicalProjection x‖ ^ 2 + (x 3) ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq (canonicalProjection x),
    EuclideanSpace.real_norm_sq_eq x, Fin.sum_univ_three, Fin.sum_univ_four]
  rfl

/-- Coordinate projection is nonexpansive in Euclidean norm. -/
theorem canonicalProjection_norm_le (x : E4) :
    ‖canonicalProjection x‖ ≤ ‖x‖ := by
  have hsq := canonicalProjection_norm_sq x
  have hlast : 0 ≤ (x 3) ^ 2 := sq_nonneg _
  nlinarith [norm_nonneg (canonicalProjection x), norm_nonneg x]

/-- The projection is compatible with subtraction. -/
theorem canonicalProjection_sub (x y : E4) :
    canonicalProjection (x - y) =
      canonicalProjection x - canonicalProjection y := by
  ext i
  simp [canonicalProjection]

/-- The exact Lipschitz constant is one. -/
theorem canonicalProjection_lipschitz :
    LipschitzWith 1 canonicalProjection := by
  apply LipschitzWith.mk_one
  intro x y
  have h := canonicalProjection_norm_le (x - y)
  rw [canonicalProjection_sub] at h
  simpa only [dist_eq_norm] using h

/-- Graph of the northern unit hemisphere on the three-ball. -/
def canonicalUpperGraph (u : E3) : E4 :=
  !₂[u 0, u 1, u 2, Real.sqrt (1 - ‖u‖ ^ 2)]

/-- The upper graph is globally continuous as a map to `R⁴`.
On points outside the ball it is not necessarily a unit vector. -/
theorem canonicalUpperGraph_continuous :
    Continuous canonicalUpperGraph := by
  unfold canonicalUpperGraph
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  · exact PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
  · exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))

/-- Projection of the upper graph is the original point. -/
theorem canonicalProjection_upperGraph (u : E3) :
    canonicalProjection (canonicalUpperGraph u) = u := by
  ext i
  fin_cases i <;> rfl

/-- On the open three-ball, the upper graph has Euclidean norm one. -/
theorem canonicalUpperGraph_norm (u : E3) (hu : ‖u‖ < 1) :
    ‖canonicalUpperGraph u‖ = 1 := by
  have hs : 0 ≤ 1 - ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg u]
  have hroot : (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 = 1 - ‖u‖ ^ 2 :=
    Real.sq_sqrt hs
  have hnorm : ‖canonicalUpperGraph u‖ ^ 2 =
      ‖u‖ ^ 2 + (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 := by
    have h1 : ‖canonicalUpperGraph u‖ ^ 2 =
        u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + (Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
      rfl
    have h2 : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    linarith
  nlinarith [norm_nonneg (canonicalUpperGraph u)]

/-- The positive fourth coordinate is recovered as the square root
of the norm defect of the projected point. -/
theorem canonicalUpperGraph_projection_eq
    (x : E4) (hunit : ‖x‖ = 1) (hupper : 0 < x 3) :
    canonicalUpperGraph (canonicalProjection x) = x := by
  have hnorm := canonicalProjection_norm_sq x
  rw [hunit] at hnorm
  have hradicand : 0 ≤ 1 - ‖canonicalProjection x‖ ^ 2 := by
    nlinarith [sq_nonneg (x 3)]
  have hroot : (Real.sqrt (1 - ‖canonicalProjection x‖ ^ 2)) ^ 2 =
      1 - ‖canonicalProjection x‖ ^ 2 := Real.sq_sqrt hradicand
  have hlast : Real.sqrt (1 - ‖canonicalProjection x‖ ^ 2) = x 3 := by
    nlinarith [Real.sqrt_nonneg (1 - ‖canonicalProjection x‖ ^ 2)]
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hlast

/-- Every point in the northern hemisphere projects strictly inside
its open coordinate ball. -/
theorem canonicalProjection_norm_lt_one
    (x : E4) (hunit : ‖x‖ = 1) (hupper : 0 < x 3) :
    ‖canonicalProjection x‖ < 1 := by
  have hsq := canonicalProjection_norm_sq x
  rw [hunit] at hsq
  nlinarith [norm_nonneg (canonicalProjection x), sq_pos_of_pos hupper]

/-- Strict satisfaction of all four cone inequalities forces positive
fourth coordinate whenever the cone parameter is positive. -/
theorem canonicalConeInterior_height_pos
    {s a b c z : ℝ} (hs : 0 < s)
    (h : CanonicalConeInterior s a b c z) : 0 < z := by
  rcases h with ⟨h0, h1, h2, h3⟩
  have hprod : 0 < s * z := by linarith
  by_contra hn
  have hnonpos : z ≤ 0 := le_of_not_gt hn
  have hcontr := mul_nonpos_of_nonneg_of_nonpos hs.le hnonpos
  linarith

/-- An explicitly open subset of the Euclidean three-ball whose
upper-hemisphere graph belongs to the strict canonical patch. -/
def canonicalProjectedOpenSet (t s : ℝ) : Set E3 :=
  {u | ‖u‖ < 1 ∧ canonicalUpperGraph u ∈ canonicalAmbientPatch t s}

/-- The projected chart domain is open. -/
theorem canonicalProjectedOpenSet_isOpen (t s : ℝ) :
    IsOpen (canonicalProjectedOpenSet t s) := by
  change IsOpen ({u : E3 | ‖u‖ < 1} ∩
    canonicalUpperGraph ⁻¹' canonicalAmbientPatch t s)
  exact (isOpen_Iio.preimage continuous_norm).inter
    ((canonicalAmbientPatch_isOpen t s).preimage
      canonicalUpperGraph_continuous)

/-- The projected chart domain is nonempty whenever the canonical
spherical bodies are strictly nested. -/
theorem canonicalProjectedOpenSet_nonempty {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (canonicalProjectedOpenSet t s).Nonempty := by
  obtain ⟨x, hxS, _hxT, hxInterior⟩ :=
    canonicalSphereBody_strict_witness ht hts
  have hupper : 0 < x 3 :=
    canonicalConeInterior_height_pos (lt_trans ht hts) hxInterior
  refine ⟨canonicalProjection x, ?_, ?_⟩
  · exact canonicalProjection_norm_lt_one x hxS.1 hupper
  · rw [canonicalUpperGraph_projection_eq x hxS.1 hupper]
    exact ⟨hxInterior, fun hCone => _hxT ⟨hxS.1, hCone⟩⟩

/-- Every point of the open projected chart is attained by a point
in the spherical patch. -/
theorem canonicalProjectedOpenSet_subset_projection_patch (t s : ℝ) :
    canonicalProjectedOpenSet t s ⊆
      canonicalProjection '' canonicalSpherePatch t s := by
  intro u hu
  refine ⟨canonicalUpperGraph u, ?_, ?_⟩
  · exact ⟨canonicalUpperGraph_norm u hu.1, hu.2⟩
  · exact canonicalProjection_upperGraph u

/-- The projection of a genuine spherical difference patch contains
a nonempty open subset of the three-dimensional Euclidean space. -/
theorem canonicalProjection_patch_contains_open {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ∃ O : Set E3, IsOpen O ∧ O.Nonempty ∧
      O ⊆ canonicalProjection '' canonicalSpherePatch t s := by
  exact ⟨canonicalProjectedOpenSet t s,
    canonicalProjectedOpenSet_isOpen t s,
    canonicalProjectedOpenSet_nonempty ht hts,
    canonicalProjectedOpenSet_subset_projection_patch t s⟩

/-- Strict positive Hausdorff three-measure of the spherical patch,
using the known full-dimensional open-set positivity on `R³` and the
nonexpansive projection. This avoids angular-measure normalization. -/
theorem canonicalSpherePatch_hausdorff_pos {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    [Measure.IsOpenPosMeasure
      (Measure.hausdorffMeasure (3 : ℝ) : Measure E3)] :
    0 < (Measure.hausdorffMeasure (3 : ℝ))
      (canonicalSpherePatch t s) := by
  obtain ⟨O, hOpen, hNonempty, hSubset⟩ :=
    canonicalProjection_patch_contains_open ht hts
  exact hausdorff_pos_of_open_subset_lipschitz_image
    canonicalProjection_lipschitz hOpen hNonempty hSubset

/-- The remaining hypothesis for strict canonical volume growth is
ONLY finiteness of the smaller spherical body's Hausdorff measure.
The patch-positivity argument is now fully explicit in source. -/
theorem canonicalSphereBody_hausdorff_strict_of_finite {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    (hFin : (Measure.hausdorffMeasure (3 : ℝ))
      (canonicalSphereBody t) ≠ ⊤)
    [Measure.IsOpenPosMeasure
      (Measure.hausdorffMeasure (3 : ℝ) : Measure E3)] :
    (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t) <
      (Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s) := by
  exact canonicalHausdorff_lt_of_patch_pos ht hts hFin
    (canonicalSpherePatch_hausdorff_pos ht hts)

end Sphere3
