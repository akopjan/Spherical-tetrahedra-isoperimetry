module

public import Sphere3.RegularParameter

@[expose] public section

/-!
# A radial coordinate for the regular family

Let four unit vectors `w_i` in Euclidean three-space satisfy
`inner w_i w_j = -1/3` when `i != j`.  Consider the spherical vertices
`(t*w_i,1)/sqrt(1+t^2)` for `t>0` in `S^3`.

Their pairwise vertex Gram value is `(3-t^2)/(3*(1+t^2))`.
The *inward normal* Gram parameter is `(t^2-3)/(t^2+9)`.
The lemmas here are algebraic; the geometric construction and volume
monotonicity via gnomonic inclusion remain to be formalized.

Source-level proofs; no Lean compilation was performed.
-/

noncomputable section

namespace Sphere3

/-- Common normal Gram value of the regular spherical tetrahedron
obtained by radially scaling a centred Euclidean regular tetrahedron. -/
def radialGramParameter (t : ℝ) : ℝ := (t ^ 2 - 3) / (t ^ 2 + 9)

/-- A positive scale gives a positive-definite equicorrelation parameter. -/
theorem radialGramParameter_mem (t : ℝ) (ht : 0 < t) :
    radialGramParameter t ∈ regularParameterDomain := by
  have hs : 0 < t ^ 2 := sq_pos_of_pos ht
  have hd : 0 < t ^ 2 + 9 := by positivity
  change -(1 : ℝ) / 3 < (t ^ 2 - 3) / (t ^ 2 + 9) ∧
    (t ^ 2 - 3) / (t ^ 2 + 9) < 1
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith
  · apply (div_lt_iff₀ hd).2
    nlinarith

/-- The normal Gram parameter is strictly increasing in the radial scale. -/
theorem strictMonoOn_radialGramParameter :
    StrictMonoOn radialGramParameter (Set.Ioi 0) := by
  intro a ha b hb hab
  have hsq : a ^ 2 < b ^ 2 := by
    have hprod : 0 < (b - a) * (b + a) :=
      mul_pos (sub_pos.mpr hab) (add_pos (Set.mem_Ioi.mp hb) (Set.mem_Ioi.mp ha))
    nlinarith
  have hda : 0 < a ^ 2 + 9 := by positivity
  have hdb : 0 < b ^ 2 + 9 := by positivity
  unfold radialGramParameter
  apply (div_lt_div_iff₀ hda hdb).2
  nlinarith

/-- An explicit positive inverse scale for the normal parameter. -/
def radialScale (rho : ℝ) : ℝ :=
  Real.sqrt (3 * (3 * rho + 1) / (1 - rho))

/-- The inverse scale is positive on the admissible normal parameter interval. -/
theorem radialScale_pos (rho : ℝ)
    (hrho : rho ∈ regularParameterDomain) : 0 < radialScale rho := by
  have hlow : -(1 : ℝ) / 3 < rho := hrho.1
  have hhigh : rho < 1 := hrho.2
  have hn : 0 < 3 * (3 * rho + 1) := by linarith
  have hd : 0 < 1 - rho := by linarith
  unfold radialScale
  exact Real.sqrt_pos.2 (div_pos hn hd)

/-- The radial scale is a right inverse of the normal Gram parameter. -/
theorem radialGramParameter_radialScale (rho : ℝ)
    (hrho : rho ∈ regularParameterDomain) :
    radialGramParameter (radialScale rho) = rho := by
  have hlow : -(1 : ℝ) / 3 < rho := hrho.1
  have hhigh : rho < 1 := hrho.2
  have hn : 0 < 3 * (3 * rho + 1) := by linarith
  have hd : 0 < 1 - rho := by linarith
  have hden : 1 - rho ≠ 0 := ne_of_gt hd
  have hsq : radialScale rho ^ 2 = 3 * (3 * rho + 1) / (1 - rho) := by
    exact Real.sq_sqrt (le_of_lt (div_pos hn hd))
  unfold radialGramParameter
  rw [hsq]
  apply (div_eq_iff (by
    have hh : 0 < 3 * (3 * rho + 1) / (1 - rho) + 9 := by
      positivity
    exact ne_of_gt hh)).2
  field_simp [hden]
  ring

end Sphere3
