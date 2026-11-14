module

public import Sphere3.CanonicalCones
public import Sphere3.RadialParameter

@[expose] public section

/-!
# A canonical regular family: exact Gram calculations

The four sign vectors form a regular Euclidean tetrahedron.  For `t > 0`,
its spherical vertices are `(t * sign_i, 1)/sqrt(1+3*t^2)`, and the
inward normals are `(sign_i,t)/sqrt(3+t^2)`. Their common normal Gram
parameter is `(t^2-1)/(t^2+3)`.

This module establishes the underlying finite Gram algebra for the
canonical family.
-/

noncomputable section

namespace Sphere3

/-- The four sign vectors of a centred regular Euclidean tetrahedron. -/
def tetraSign : Fin 4 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

/-- The squared Euclidean length of each sign vector is three. -/
theorem tetraSign_diag (i : Fin 4) :
    (∑ j : Fin 3, tetraSign i j * tetraSign i j) = 3 := by
  fin_cases i <;> norm_num [tetraSign, Fin.sum_univ_succ]

/-- Distinct sign vectors have scalar product minus one. -/
theorem tetraSign_offdiag (i j : Fin 4) (h : i ≠ j) :
    (∑ k : Fin 3, tetraSign i k * tetraSign j k) = -1 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [tetraSign, Fin.sum_univ_succ]

/-- The four sign vectors sum to zero. -/
theorem tetraSign_sum_zero (j : Fin 3) :
    (∑ i : Fin 4, tetraSign i j) = 0 := by
  fin_cases j <;> norm_num [tetraSign, Fin.sum_univ_succ]

/-- Common off-diagonal Gram parameter of the inward unit normals. -/
def canonicalGramParameter (t : ℝ) : ℝ :=
  (t ^ 2 - 1) / (t ^ 2 + 3)

/-- Every positive canonical parameter defines a positive-definite
regular normal Gram parameter. -/
theorem canonicalGramParameter_mem (t : ℝ) (ht : 0 < t) :
    canonicalGramParameter t ∈ regularParameterDomain := by
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hd : 0 < t ^ 2 + 3 := by positivity
  change -(1 : ℝ) / 3 < (t ^ 2 - 1) / (t ^ 2 + 3) ∧
    (t ^ 2 - 1) / (t ^ 2 + 3) < 1
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith
  · apply (div_lt_iff₀ hd).2
    nlinarith

/-- The canonical normal parameter is strictly increasing. -/
theorem canonicalGramParameter_strictMonoOn :
    StrictMonoOn canonicalGramParameter (Set.Ioi 0) := by
  intro a ha b hb hab
  have hsq : a ^ 2 < b ^ 2 := by
    have hprod : 0 < (b - a) * (b + a) :=
      mul_pos (sub_pos.mpr hab) (add_pos (Set.mem_Ioi.mp hb) (Set.mem_Ioi.mp ha))
    nlinarith
  have hda : 0 < a ^ 2 + 3 := by positivity
  have hdb : 0 < b ^ 2 + 3 := by positivity
  unfold canonicalGramParameter
  apply (div_lt_div_iff₀ hda hdb).2
  nlinarith

/-- The canonical and gnomonic normal parameters are the same, with
spatial scaling `s = sqrt(3)*t`. -/
theorem canonicalGramParameter_eq_radial (t : ℝ) :
    canonicalGramParameter t = radialGramParameter (Real.sqrt 3 * t) := by
  have hroot : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsq : (Real.sqrt 3 * t) ^ 2 = 3 * t ^ 2 := by
    calc
      (Real.sqrt 3 * t) ^ 2 = (Real.sqrt 3) ^ 2 * t ^ 2 := by ring
      _ = 3 * t ^ 2 := by rw [hroot]
  have hd : t ^ 2 + 3 ≠ 0 := by positivity
  unfold canonicalGramParameter radialGramParameter
  rw [hsq]
  have hden : 3 * t ^ 2 + 9 ≠ 0 := by positivity
  field_simp [hd, hden]
  <;> ring

/-- Positive inverse of the canonical Gram parameter. -/
def canonicalScale (rho : ℝ) : ℝ :=
  Real.sqrt ((3 * rho + 1) / (1 - rho))

theorem canonicalScale_pos (rho : ℝ)
    (h : rho ∈ regularParameterDomain) : 0 < canonicalScale rho := by
  have hlo : -(1 : ℝ) / 3 < rho := h.1
  have hhi : rho < 1 := h.2
  have hn : 0 < 3 * rho + 1 := by linarith
  have hd : 0 < 1 - rho := by linarith
  exact Real.sqrt_pos.2 (div_pos hn hd)

theorem canonicalGramParameter_canonicalScale (rho : ℝ)
    (h : rho ∈ regularParameterDomain) :
    canonicalGramParameter (canonicalScale rho) = rho := by
  have hlo : -(1 : ℝ) / 3 < rho := h.1
  have hhi : rho < 1 := h.2
  have hn : 0 < 3 * rho + 1 := by linarith
  have hd : 0 < 1 - rho := by linarith
  have hden : 1 - rho ≠ 0 := ne_of_gt hd
  have hs : canonicalScale rho ^ 2 = (3 * rho + 1) / (1 - rho) := by
    exact Real.sq_sqrt (le_of_lt (div_pos hn hd))
  unfold canonicalGramParameter
  rw [hs]
  apply (div_eq_iff (by
    have hpos : 0 < (3 * rho + 1) / (1 - rho) + 3 := by positivity
    exact ne_of_gt hpos)).2
  field_simp [hden]
  ring

theorem canonicalScale_canonicalGramParameter (t : ℝ) (ht : 0 < t) :
    canonicalScale (canonicalGramParameter t) = t := by
  have hparam : canonicalGramParameter t ∈ regularParameterDomain :=
    canonicalGramParameter_mem t ht
  have hscale : 0 < canonicalScale (canonicalGramParameter t) :=
    canonicalScale_pos _ hparam
  apply canonicalGramParameter_strictMonoOn.injOn hscale ht
  exact canonicalGramParameter_canonicalScale _ hparam

end Sphere3
