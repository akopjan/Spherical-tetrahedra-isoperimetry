module

public import SphericalTetrahedron.DualHeightNoncritical
public import Sphere3.GramCongruence

@[expose] public section

/-!
# Six-Dimensional Gram Chart on Spherical Tetrahedra

This module constructs the open unit-Gram domain `gramOpen ⊂ (Fin 6 → ℝ)`,
its explicit Cholesky realization `tetOf : ∀ x ∈ gramOpen, SphericalTetrahedron`,
the exact 4×4 adjugate `symUnitAdj` with the polynomial Jacobi and area-gradient
identities, and the inverse embedding `gramPoint : SphericalTetrahedron → Fin 6 → ℝ`.
-/

noncomputable section

open scoped InnerProductSpace BigOperators Matrix

namespace SphericalTetrahedron

/-- Edge index pairs `(p, q)` with `p < q` corresponding to coordinates `Fin 6 → ℝ`. -/
def pairIdx : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | 5 => (2, 3)

/-- Complementary opposite edge pairs `(i, j)` with `{p, q, i, j} = Fin 4` and `i < j`. -/
def oppIdx : Fin 6 → Fin 4 × Fin 4
  | 0 => (2, 3)
  | 1 => (1, 3)
  | 2 => (1, 2)
  | 3 => (0, 3)
  | 4 => (0, 2)
  | 5 => (0, 1)

theorem pairIdx_lt (k : Fin 6) : (pairIdx k).1 < (pairIdx k).2 := by
  fin_cases k <;> decide

theorem pairIdx_ne (k : Fin 6) : (pairIdx k).1 ≠ (pairIdx k).2 :=
  (pairIdx_lt k).ne

theorem oppIdx_lt (k : Fin 6) : (oppIdx k).1 < (oppIdx k).2 := by
  fin_cases k <;> decide

theorem oppIdx_ne (k : Fin 6) : (oppIdx k).1 ≠ (oppIdx k).2 :=
  (oppIdx_lt k).ne

/-- Symmetric 4×4 matrix with unit diagonal parametrized by `x : Fin 6 → ℝ`. -/
def symUnitMat (x : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,   x 0, x 1, x 2;
     x 0, 1,   x 3, x 4;
     x 1, x 3, 1,   x 5;
     x 2, x 4, x 5, 1]

/-- Explicit polynomial adjugate of `symUnitMat x`. -/
def symUnitAdj (x : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let a := x 0; let b := x 1; let c := x 2
  let d := x 3; let e := x 4; let f := x 5
  let m00 := 1 - d^2 - e^2 - f^2 + 2*d*e*f
  let m11 := 1 - b^2 - c^2 - f^2 + 2*b*c*f
  let m22 := 1 - a^2 - c^2 - e^2 + 2*a*c*e
  let m33 := 1 - a^2 - b^2 - d^2 + 2*a*b*d
  let m01 := -a + a*f^2 + b*d + c*e - b*e*f - c*d*f
  let m02 := -b + b*e^2 + a*d + c*f - a*e*f - c*d*e
  let m03 := -c + c*d^2 + a*e + b*f - a*d*f - b*d*e
  let m12 := -d + d*c^2 + a*b + e*f - b*c*e - a*c*f
  let m13 := -e + e*b^2 + a*c + d*f - a*b*f - b*c*d
  let m23 := -f + f*a^2 + b*c + d*e - a*b*e - a*c*d
  !![m00, m01, m02, m03;
     m01, m11, m12, m13;
     m02, m12, m22, m23;
     m03, m13, m23, m33]

/-- Explicit inverse of `symUnitMat x` (valid whenever `(symUnitMat x).det ≠ 0`). -/
def symUnitInv (x : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ((symUnitMat x).det)⁻¹ • symUnitAdj x

theorem symUnitMat_symm (x : Fin 6 → ℝ) (i j : Fin 4) :
    symUnitMat x i j = symUnitMat x j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem symUnitAdj_symm (x : Fin 6 → ℝ) (i j : Fin 4) :
    symUnitAdj x i j = symUnitAdj x j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem symUnitInv_symm (x : Fin 6 → ℝ) (i j : Fin 4) :
    symUnitInv x i j = symUnitInv x j i := by
  simp [symUnitInv, symUnitAdj_symm]

theorem symUnitMat_pairIdx (x : Fin 6 → ℝ) (k : Fin 6) :
    symUnitMat x (pairIdx k).1 (pairIdx k).2 = x k := by
  fin_cases k <;> rfl

theorem symUnitMat_mul_adj (x : Fin 6 → ℝ) :
    symUnitMat x * symUnitAdj x = (symUnitMat x).det • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp only [symUnitMat, symUnitAdj, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_four]
  eval_det
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem symUnitAdj_mul_mat (x : Fin 6 → ℝ) :
    symUnitAdj x * symUnitMat x = (symUnitMat x).det • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp only [symUnitMat, symUnitAdj, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_four]
  eval_det
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem symUnitMat_mul_inv (x : Fin 6 → ℝ) (hdet : (symUnitMat x).det ≠ 0) :
    symUnitMat x * symUnitInv x = 1 := by
  unfold symUnitInv
  rw [Matrix.mul_smul, symUnitMat_mul_adj, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem symUnitInv_mul_mat (x : Fin 6 → ℝ) (hdet : (symUnitMat x).det ≠ 0) :
    symUnitInv x * symUnitMat x = 1 := by
  unfold symUnitInv
  rw [Matrix.smul_mul, symUnitAdj_mul_mat, smul_smul, inv_mul_cancel₀ hdet, one_smul]

/-- Explicit Jacobi 2×2 complementary minor identity for all six coordinate pairs. -/
theorem symUnitAdj_jacobi (x : Fin 6 → ℝ) (k : Fin 6) :
    let (p, q) := pairIdx k
    let (i, j) := oppIdx k
    symUnitAdj x i i * symUnitAdj x j j - symUnitAdj x i j ^ 2 =
      (symUnitMat x).det * (1 - symUnitMat x p q ^ 2) := by
  fin_cases k <;> simp [pairIdx, oppIdx, symUnitMat, symUnitAdj] <;> eval_det <;> ring

/-- Pure polynomial identity equating the dual-height adjugate combination at vertex `i`
to the `(p, q)`-derivative factor of the spherical face link around vertex `i`. -/
theorem symUnitAdj_area_identity_fst (x : Fin 6 → ℝ) (k : Fin 6) :
    let (p, q) := pairIdx k
    let (i, j) := oppIdx k
    let M := symUnitAdj x
    let G := symUnitMat x
    (∑ l : Fin 4, (M i i * M l j - M i j * M l i)) =
      G.det * (1 - G p q) * (1 + G p q - G p j - G q j) := by
  fin_cases k <;> simp [pairIdx, oppIdx, symUnitMat, symUnitAdj, Fin.sum_univ_four] <;>
    eval_det <;> ring

/-- Symmetric counterpart of `symUnitAdj_area_identity_fst` at the opposite vertex `j`. -/
theorem symUnitAdj_area_identity_snd (x : Fin 6 → ℝ) (k : Fin 6) :
    let (p, q) := pairIdx k
    let (i, j) := oppIdx k
    let M := symUnitAdj x
    let G := symUnitMat x
    (∑ l : Fin 4, (M j j * M l i - M i j * M l j)) =
      G.det * (1 - G p q) * (1 + G p q - G p i - G q i) := by
  fin_cases k <;> simp [pairIdx, oppIdx, symUnitMat, symUnitAdj, Fin.sum_univ_four] <;>
    eval_det <;> ring

/-- Each diagonal entry of `symUnitAdj` equals the 3×3 spherical triangle Gram determinant
of the three normals incident to that vertex. -/
theorem symUnitAdj_diag_eq_minor3 (x : Fin 6 → ℝ) (k : Fin 6) :
    let (p, q) := pairIdx k
    let (i, j) := oppIdx k
    let G := symUnitMat x
    1 - G p q ^ 2 - G p j ^ 2 - G q j ^ 2 + 2 * G p q * G p j * G q j = symUnitAdj x i i := by
  fin_cases k <;> simp [pairIdx, oppIdx, symUnitMat, symUnitAdj] <;> ring

/-- Symmetric counterpart at `j`. -/
theorem symUnitAdj_diag_eq_minor3_snd (x : Fin 6 → ℝ) (k : Fin 6) :
    let (p, q) := pairIdx k
    let (i, j) := oppIdx k
    let G := symUnitMat x
    1 - G p q ^ 2 - G p i ^ 2 - G q i ^ 2 + 2 * G p q * G p i * G q i = symUnitAdj x j j := by
  fin_cases k <;> simp [pairIdx, oppIdx, symUnitMat, symUnitAdj] <;> ring

/-- Explicit polynomial expression for `(symUnitMat x).det`. -/
def symUnitDetPoly (x : Fin 6 → ℝ) : ℝ :=
  1 - x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 - x 4 ^ 2 - x 5 ^ 2
    + 2 * x 0 * x 1 * x 3 + 2 * x 0 * x 2 * x 4 + 2 * x 1 * x 2 * x 5 + 2 * x 3 * x 4 * x 5
    + x 0 ^ 2 * x 5 ^ 2 + x 1 ^ 2 * x 4 ^ 2 + x 2 ^ 2 * x 3 ^ 2
    - 2 * x 0 * x 2 * x 3 * x 5 - 2 * x 0 * x 1 * x 4 * x 5 - 2 * x 1 * x 2 * x 3 * x 4

theorem symUnitMat_det_eq_poly (x : Fin 6 → ℝ) :
    (symUnitMat x).det = symUnitDetPoly x := by
  unfold symUnitMat symUnitDetPoly
  eval_det
  ring

private lemma hasDerivAt_quadratic_zero (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2) b 0 := by
  refine HasDerivAt.congr_deriv
    ((((hasDerivAt_id (0 : ℝ)).const_mul b).const_add a).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul c)) ?_
  simp

theorem symUnitMat_det_deriv_coord (x : Fin 6 → ℝ) (k : Fin 6) :
    HasDerivAt (fun t : ℝ => (symUnitMat (x + t • Pi.single k 1)).det)
      (2 * symUnitAdj x (pairIdx k).1 (pairIdx k).2) 0 := by
  simp_rw [symUnitMat_det_eq_poly]
  fin_cases k
  · refine (hasDerivAt_quadratic_zero (symUnitDetPoly x)
        (2 * symUnitAdj x (pairIdx 0).1 (pairIdx 0).2) (x 5 ^ 2 - 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [symUnitDetPoly, symUnitAdj, pairIdx]; ring
  · refine (hasDerivAt_quadratic_zero (symUnitDetPoly x)
        (2 * symUnitAdj x (pairIdx 1).1 (pairIdx 1).2) (x 4 ^ 2 - 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [symUnitDetPoly, symUnitAdj, pairIdx]; ring
  · refine (hasDerivAt_quadratic_zero (symUnitDetPoly x)
        (2 * symUnitAdj x (pairIdx 2).1 (pairIdx 2).2) (x 3 ^ 2 - 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [symUnitDetPoly, symUnitAdj, pairIdx]; ring
  · refine (hasDerivAt_quadratic_zero (symUnitDetPoly x)
        (2 * symUnitAdj x (pairIdx 3).1 (pairIdx 3).2) (x 2 ^ 2 - 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [symUnitDetPoly, symUnitAdj, pairIdx]; ring
  · refine (hasDerivAt_quadratic_zero (symUnitDetPoly x)
        (2 * symUnitAdj x (pairIdx 4).1 (pairIdx 4).2) (x 1 ^ 2 - 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [symUnitDetPoly, symUnitAdj, pairIdx]; ring
  · refine (hasDerivAt_quadratic_zero (symUnitDetPoly x)
        (2 * symUnitAdj x (pairIdx 5).1 (pairIdx 5).2) (x 0 ^ 2 - 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [symUnitDetPoly, symUnitAdj, pairIdx]; ring

/-- Leading 2×2 principal minor of `symUnitMat x`. -/
def gramDet2 (x : Fin 6 → ℝ) : ℝ := 1 - x 0 ^ 2

/-- Leading 3×3 principal minor of `symUnitMat x`. -/
def gramDet3 (x : Fin 6 → ℝ) : ℝ :=
  1 - x 0 ^ 2 - x 1 ^ 2 - x 3 ^ 2 + 2 * x 0 * x 1 * x 3

/-- Full 4×4 determinant of `symUnitMat x`. -/
def gramDet4 (x : Fin 6 → ℝ) : ℝ := (symUnitMat x).det

/-- Open Sylvester domain in `Fin 6 → ℝ` of positive-definite unit-diagonal Gram matrices. -/
def gramOpen : Set (Fin 6 → ℝ) :=
  {x | 0 < gramDet2 x ∧ 0 < gramDet3 x ∧ 0 < gramDet4 x}

theorem isOpen_gramOpen : IsOpen gramOpen := by
  have h2 : Continuous gramDet2 := by unfold gramDet2; fun_prop
  have h3 : Continuous gramDet3 := by unfold gramDet3; fun_prop
  have h4 : Continuous gramDet4 := by
    unfold gramDet4
    simp_rw [symUnitMat_det_eq_poly]
    unfold symUnitDetPoly
    fun_prop
  exact (isOpen_lt continuous_const h2).inter
    ((isOpen_lt continuous_const h3).inter (isOpen_lt continuous_const h4))

theorem gramOpen_det_pos {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    0 < (symUnitMat x).det := hx.2.2

theorem gramOpen_det_ne_zero {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    (symUnitMat x).det ≠ 0 := (gramOpen_det_pos hx).ne'

/-- Lower-triangular Cholesky factor of `symUnitMat x`. -/
def cholMat (x : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let s1 := Real.sqrt (gramDet2 x)
  let s2 := Real.sqrt (gramDet3 x / gramDet2 x)
  let s3 := Real.sqrt (gramDet4 x / gramDet3 x)
  let b21 := (x 3 - x 0 * x 1) / s1
  let b31 := (x 4 - x 0 * x 2) / s1
  let b32 := (x 5 - x 1 * x 2 - b21 * b31) / s2
  !![1,   0,   0,   0;
     x 0, s1,  0,   0;
     x 1, b21, s2,  0;
     x 2, b31, b32, s3]

/-- Four vectors in `E4` given by the rows of `cholMat x`. -/
def cholVec (x : Fin 6 → ℝ) (i : Fin 4) : E4 :=
  WithLp.toLp 2 (cholMat x i)

private theorem chol_poly_row3 (x : Fin 6 → ℝ) :
    let p32 := gramDet2 x * (x 5 - x 1 * x 2) - (x 3 - x 0 * x 1) * (x 4 - x 0 * x 2)
    gramDet2 x * gramDet3 x * (1 - x 2 ^ 2) - gramDet3 x * (x 4 - x 0 * x 2) ^ 2 - p32 ^ 2 =
      gramDet2 x * gramDet4 x := by
  dsimp [gramDet2, gramDet3, gramDet4]
  rw [symUnitMat_det_eq_poly]
  unfold symUnitDetPoly
  ring

theorem cholMat_mul_transpose {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    cholMat x * (cholMat x)ᵀ = symUnitMat x := by
  rcases hx with ⟨h2, h3, h4⟩
  have hs1 : 0 < Real.sqrt (gramDet2 x) := Real.sqrt_pos.mpr h2
  have hs2 : 0 < Real.sqrt (gramDet3 x / gramDet2 x) := Real.sqrt_pos.mpr (div_pos h3 h2)
  have hs3 : 0 < Real.sqrt (gramDet4 x / gramDet3 x) := Real.sqrt_pos.mpr (div_pos h4 h3)
  have hsq1 : Real.sqrt (gramDet2 x) ^ 2 = gramDet2 x := Real.sq_sqrt h2.le
  have hsq2 : Real.sqrt (gramDet3 x / gramDet2 x) ^ 2 = gramDet3 x / gramDet2 x :=
    Real.sq_sqrt (div_pos h3 h2).le
  have hsq3 : Real.sqrt (gramDet4 x / gramDet3 x) ^ 2 = gramDet4 x / gramDet3 x :=
    Real.sq_sqrt (div_pos h4 h3).le
  have h2ne : gramDet2 x ≠ 0 := h2.ne'
  have h3ne : gramDet3 x ≠ 0 := h3.ne'
  have hs1ne : Real.sqrt (gramDet2 x) ≠ 0 := hs1.ne'
  have hs2ne : Real.sqrt (gramDet3 x / gramDet2 x) ≠ 0 := hs2.ne'
  have hrow2 :
      x 1 ^ 2 + ((x 3 - x 0 * x 1) / Real.sqrt (gramDet2 x)) ^ 2 +
          Real.sqrt (gramDet3 x / gramDet2 x) ^ 2 = 1 := by
    rw [div_pow, hsq1, hsq2]
    dsimp [gramDet2, gramDet3] at h2ne ⊢
    field_simp [h2ne]
    ring
  have hrow3 :
      let s1 := Real.sqrt (gramDet2 x)
      let s2 := Real.sqrt (gramDet3 x / gramDet2 x)
      let b21 := (x 3 - x 0 * x 1) / s1
      let b31 := (x 4 - x 0 * x 2) / s1
      let b32 := (x 5 - x 1 * x 2 - b21 * b31) / s2
      x 2 ^ 2 + b31 ^ 2 + b32 ^ 2 + Real.sqrt (gramDet4 x / gramDet3 x) ^ 2 = 1 := by
    dsimp
    have hp := chol_poly_row3 x
    dsimp at hp
    have hb2131 :
        ((x 3 - x 0 * x 1) / Real.sqrt (gramDet2 x)) *
            ((x 4 - x 0 * x 2) / Real.sqrt (gramDet2 x)) =
          (x 3 - x 0 * x 1) * (x 4 - x 0 * x 2) / gramDet2 x := by
      rw [div_mul_div_comm, ← sq, hsq1]
    rw [hb2131, div_pow, hsq1, div_pow, hsq2, hsq3]
    field_simp [h2ne, h3ne]
    linear_combination -hp
  ext i j
  simp only [cholMat, symUnitMat, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp
  · linarith [hsq1, show gramDet2 x = 1 - x 0 ^ 2 from rfl]
  · field_simp [hs1ne]; ring
  · field_simp [hs1ne]; ring
  · field_simp [hs1ne]; ring
  · simp_rw [← sq] at hrow2 ⊢
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hrow2
  · field_simp [hs1ne, hs2ne]; ring
  · field_simp [hs1ne]; ring
  · field_simp [hs1ne, hs2ne]; ring
  · simp_rw [← sq] at hrow3 ⊢
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hrow3

theorem cholVec_inner {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (i j : Fin 4) :
    ⟪cholVec x i, cholVec x j⟫_ℝ = symUnitMat x i j := by
  have hmul := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) (cholMat_mul_transpose hx)
  rw [PiLp.inner_apply]
  simpa [cholVec, Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using hmul

theorem cholVec_norm {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (i : Fin 4) :
    ‖cholVec x i‖ = 1 := by
  have hsq : ‖cholVec x i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, cholVec_inner hx i i]
    fin_cases i <;> rfl
  nlinarith [norm_nonneg (cholVec x i)]

theorem cholMat_det_pos {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    0 < (cholMat x).det := by
  rcases hx with ⟨h2, h3, h4⟩
  have hs1 : 0 < Real.sqrt (gramDet2 x) := Real.sqrt_pos.mpr h2
  have hs2 : 0 < Real.sqrt (gramDet3 x / gramDet2 x) := Real.sqrt_pos.mpr (div_pos h3 h2)
  have hs3 : 0 < Real.sqrt (gramDet4 x / gramDet3 x) := Real.sqrt_pos.mpr (div_pos h4 h3)
  have hdet :
      (cholMat x).det =
        Real.sqrt (gramDet2 x) *
          Real.sqrt (gramDet3 x / gramDet2 x) *
          Real.sqrt (gramDet4 x / gramDet3 x) := by
    unfold cholMat
    eval_det
  rw [hdet]
  positivity

theorem cholVec_linearIndependent {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    LinearIndependent ℝ (cholVec x) := by
  have hrows : LinearIndependent ℝ (fun i => cholMat x i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (cholMat_det_pos hx).ne'
  let e : (Fin 4 → ℝ) ≃ₗ[ℝ] E4 := (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm
  exact hrows.map' e.toLinearMap e.ker

/-- Genuine `SphericalTetrahedron` realizing any Gram point `x ∈ gramOpen`. -/
def tetOf (x : Fin 6 → ℝ) (hx : x ∈ gramOpen) : SphericalTetrahedron where
  normal := cholVec x
  unit := cholVec_norm hx
  independent := cholVec_linearIndependent hx

theorem tetOf_normal_inner {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (i j : Fin 4) :
    ⟪(tetOf x hx).normal i, (tetOf x hx).normal j⟫_ℝ = symUnitMat x i j :=
  cholVec_inner hx i j

/-- Extract the 6-tuple of pairwise normal inner products of a spherical tetrahedron. -/
def gramPoint (T : SphericalTetrahedron) : Fin 6 → ℝ :=
  ![⟪T.normal 0, T.normal 1⟫_ℝ,
    ⟪T.normal 0, T.normal 2⟫_ℝ,
    ⟪T.normal 0, T.normal 3⟫_ℝ,
    ⟪T.normal 1, T.normal 2⟫_ℝ,
    ⟪T.normal 1, T.normal 3⟫_ℝ,
    ⟪T.normal 2, T.normal 3⟫_ℝ]

theorem symUnitMat_gramPoint (T : SphericalTetrahedron) (i j : Fin 4) :
    symUnitMat (gramPoint T) i j = ⟪T.normal i, T.normal j⟫_ℝ := by
  fin_cases i <;> fin_cases j <;>
    simp [symUnitMat, gramPoint, T.unit] <;>
    exact real_inner_comm _ _

theorem gramPoint_tetOf {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) :
    gramPoint (tetOf x hx) = x := by
  ext k
  fin_cases k <;> simp [gramPoint, tetOf_normal_inner hx, symUnitMat]

private theorem gram_quadratic_pos (T : SphericalTetrahedron) (v : Fin 4 → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (symUnitMat (gramPoint T) *ᵥ v) := by
  have hlin : (∑ i : Fin 4, v i • T.normal i) ≠ 0 := by
    intro hz
    have hcoeff := (linearIndependent_iff'.mp T.independent) Finset.univ v hz
    apply hv
    ext i
    exact hcoeff i (Finset.mem_univ i)
  have hnorm : 0 < ‖∑ i : Fin 4, v i • T.normal i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hlin)
  have hquad :
      v ⬝ᵥ (symUnitMat (gramPoint T) *ᵥ v) = ‖∑ i : Fin 4, v i • T.normal i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, ← symUnitMat_gramPoint T]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
    ring
  rw [hquad]
  exact hnorm

theorem gramPoint_mem_gramOpen (T : SphericalTetrahedron) : gramPoint T ∈ gramOpen := by
  let x := gramPoint T
  let G := symUnitMat x
  have hv2_ne : (![-x 0, 1, 0, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  have hq2 := gram_quadratic_pos T ![-(x 0), 1, 0, 0] hv2_ne
  have hdet2_eq : (![-(x 0), 1, 0, 0] : Fin 4 → ℝ) ⬝ᵥ (G *ᵥ ![-(x 0), 1, 0, 0]) = gramDet2 x := by
    simp [G, x, gramDet2, symUnitMat, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
    ring
  have hdet2 : 0 < gramDet2 x := hdet2_eq ▸ hq2
  let v3 : Fin 4 → ℝ := ![x 0 * x 3 - x 1, x 0 * x 1 - x 3, gramDet2 x, 0]
  have hv3_ne : v3 ≠ 0 := by
    intro h
    have := congrFun h 2
    simp [v3] at this
    exact hdet2.ne' this
  have hq3 := gram_quadratic_pos T v3 hv3_ne
  have hdet3_eq : v3 ⬝ᵥ (G *ᵥ v3) = gramDet2 x * gramDet3 x := by
    simp [v3, G, x, gramDet2, gramDet3, symUnitMat, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
    ring
  have hdet3 : 0 < gramDet3 x := by
    rw [hdet3_eq] at hq3
    exact pos_of_mul_pos_right hq3 hdet2.le
  let v4 : Fin 4 → ℝ := fun i => symUnitAdj x i 3
  have hv4_3 : v4 3 = gramDet3 x := by
    simp [v4, symUnitAdj, gramDet3]
  have hv4_ne : v4 ≠ 0 := by
    intro h
    have h3 := congrFun h 3
    simp [hv4_3] at h3
    exact hdet3.ne' h3
  have hq4 := gram_quadratic_pos T v4 hv4_ne
  have hGmul : ∀ i : Fin 4, (G *ᵥ v4) i = if i = 3 then gramDet4 x else 0 := by
    intro i
    have hmul := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i 3) (symUnitMat_mul_adj x)
    simpa [G, v4, gramDet4, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      Matrix.one_apply, eq_comm] using hmul
  have hdet4_eq : v4 ⬝ᵥ (G *ᵥ v4) = gramDet3 x * gramDet4 x := by
    simp [dotProduct, hGmul, hv4_3]
  have hdet4 : 0 < gramDet4 x := by
    rw [hdet4_eq] at hq4
    exact pos_of_mul_pos_right hq4 hdet3.le
  exact ⟨hdet2, hdet3, hdet4⟩

theorem gramOpen_inv_diag_pos {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (i : Fin 4) :
    0 < symUnitInv x i i := by
  let T := tetOf x hx
  have hgm : gramPoint T = x := gramPoint_tetOf hx
  let w : Fin 4 → ℝ := fun k => symUnitInv x k i
  have hwmul : symUnitMat x *ᵥ w = Pi.single i (1 : ℝ) := by
    ext r
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M r i)
      (symUnitMat_mul_inv x (gramOpen_det_ne_zero hx))
    simpa [w, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
      eq_comm] using h
  have hw_ne : w ≠ 0 := by
    intro hz
    rw [hz, Matrix.mulVec_zero] at hwmul
    have := congrFun hwmul i
    simp at this
  have hpos := gram_quadratic_pos T w hw_ne
  rw [hgm] at hpos
  have hdot : w ⬝ᵥ (symUnitMat x *ᵥ w) = symUnitInv x i i := by
    rw [hwmul]
    simp [dotProduct, w, Pi.single_apply]
  rwa [hdot] at hpos

theorem gramOpen_adj_diag_pos {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (i : Fin 4) :
    0 < symUnitAdj x i i := by
  have hinv := gramOpen_inv_diag_pos hx i
  have hdet := gramOpen_det_pos hx
  have heq : symUnitAdj x i i = (symUnitMat x).det * symUnitInv x i i := by
    unfold symUnitInv
    simp [hdet.ne']
  rw [heq]
  exact mul_pos hdet hinv

theorem gramOpen_offdiag_abs_lt_one {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (k : Fin 6) :
    |x k| < 1 := by
  let T := tetOf x hx
  let p := (pairIdx k).1
  let q := (pairIdx k).2
  have hpq : p ≠ q := pairIdx_ne k
  have hsub : |⟪T.normal p, T.normal q⟫_ℝ| < 1 := by
    have hp_unit := T.unit p
    have hq_unit := T.unit q
    have hne : T.normal p ≠ T.normal q ∧ T.normal p ≠ -T.normal q := by
      constructor
      · intro heq
        exact hpq (T.independent.injective heq)
      · intro heq
        have hlin := linearIndependent_iff'.mp T.independent {p, q}
          (fun r => if r = p then 1 else if r = q then 1 else 0) ?_ p (by simp)
        · simp at hlin
        · rw [Finset.sum_pair hpq]
          simp [hpq.symm, heq]
    have hcs := abs_real_inner_le_norm (T.normal p) (T.normal q)
    rw [hp_unit, hq_unit, mul_one] at hcs
    rcases lt_or_eq_of_le hcs with hlt | heq
    · exact hlt
    · exfalso
      rcases abs_eq zero_le_one |>.mp heq with h1 | hm1
      · have hzero : ‖T.normal p - T.normal q‖ ^ 2 = 0 := by
          rw [norm_sub_sq_real, hp_unit, hq_unit, h1]
          ring
        have : T.normal p = T.normal q := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
        exact hne.1 this
      · have hzero : ‖T.normal p + T.normal q‖ ^ 2 = 0 := by
          rw [norm_add_sq_real, hp_unit, hq_unit, hm1]
          ring
        have : T.normal p = -T.normal q :=
          eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
        exact hne.2 this
  have hinner : ⟪T.normal p, T.normal q⟫_ℝ = x k := by
    rw [tetOf_normal_inner hx p q, symUnitMat_pairIdx]
  rwa [← hinner]

theorem gramOpen_jacobi_pos {x : Fin 6 → ℝ} (hx : x ∈ gramOpen) (k : Fin 6) :
    let (i, j) := oppIdx k
    0 < symUnitAdj x i i * symUnitAdj x j j - symUnitAdj x i j ^ 2 := by
  dsimp
  have hj := symUnitAdj_jacobi x k
  dsimp only at hj
  rw [hj]
  have h1 : 0 < 1 - symUnitMat x (pairIdx k).1 (pairIdx k).2 ^ 2 := by
    rw [symUnitMat_pairIdx]
    nlinarith [abs_lt.mp (gramOpen_offdiag_abs_lt_one hx k)]
  exact mul_pos (gramOpen_det_pos hx) h1

/-- Normal dual ray expanded in the inward-normal basis via `symUnitInv`. -/
theorem normalDualRay_eq_sum_inv (T : SphericalTetrahedron) (j : Fin 4) :
    T.normalDualRay j = ∑ l : Fin 4, symUnitInv (gramPoint T) l j • T.normal l := by
  set x := gramPoint T
  apply sub_eq_zero.mp
  apply T.eq_zero_of_all_normal_inner_zero
  intro k
  rw [inner_sub_right, T.normalDualRay_inner k j, inner_sum]
  simp_rw [real_inner_smul_right, ← symUnitMat_gramPoint T]
  have hmul := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M k j)
    (symUnitMat_mul_inv x (gramOpen_det_ne_zero (gramPoint_mem_gramOpen T)))
  have hsum : (∑ l : Fin 4, symUnitInv x l j * symUnitMat x k l) = if k = j then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using hmul
  rw [hsum, sub_self]

theorem normalDualRay_inner_eq_inv (T : SphericalTetrahedron) (i j : Fin 4) :
    ⟪T.normalDualRay i, T.normalDualRay j⟫_ℝ = symUnitInv (gramPoint T) i j := by
  rw [T.normalDualRay_eq_sum_inv i, sum_inner]
  simp_rw [real_inner_smul_left, T.normalDualRay_inner]
  simp [symUnitInv_symm]

theorem normalDualRay_norm_eq_sqrt_inv (T : SphericalTetrahedron) (i : Fin 4) :
    ‖T.normalDualRay i‖ = Real.sqrt (symUnitInv (gramPoint T) i i) := by
  have hsq : ‖T.normalDualRay i‖ ^ 2 = symUnitInv (gramPoint T) i i := by
    rw [← real_inner_self_eq_norm_sq, T.normalDualRay_inner_eq_inv i i]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem dualVertex_inner_eq_inv (T : SphericalTetrahedron) (i j : Fin 4) :
    ⟪T.dualVertex i, T.dualVertex j⟫_ℝ =
      symUnitInv (gramPoint T) i j /
        Real.sqrt (symUnitInv (gramPoint T) i i * symUnitInv (gramPoint T) j j) := by
  have hi : 0 < symUnitInv (gramPoint T) i i :=
    gramOpen_inv_diag_pos (gramPoint_mem_gramOpen T) i
  have hj : 0 < symUnitInv (gramPoint T) j j :=
    gramOpen_inv_diag_pos (gramPoint_mem_gramOpen T) j
  have hsi : Real.sqrt (symUnitInv (gramPoint T) i i) ≠ 0 := (Real.sqrt_pos.mpr hi).ne'
  have hsj : Real.sqrt (symUnitInv (gramPoint T) j j) ≠ 0 := (Real.sqrt_pos.mpr hj).ne'
  unfold dualVertex
  rw [real_inner_smul_left, real_inner_smul_right,
    T.normalDualRay_inner_eq_inv i j,
    T.normalDualRay_norm_eq_sqrt_inv i,
    T.normalDualRay_norm_eq_sqrt_inv j]
  rw [Real.sqrt_mul hi.le]
  field_simp [hsi, hsj]

theorem dualVertex_inner_eq_adj (T : SphericalTetrahedron) (i j : Fin 4) :
    ⟪T.dualVertex i, T.dualVertex j⟫_ℝ =
      symUnitAdj (gramPoint T) i j /
        Real.sqrt (symUnitAdj (gramPoint T) i i * symUnitAdj (gramPoint T) j j) := by
  rw [T.dualVertex_inner_eq_inv i j]
  set x := gramPoint T
  have hdet : 0 < (symUnitMat x).det := gramOpen_det_pos (gramPoint_mem_gramOpen T)
  have hi : 0 < symUnitAdj x i i := gramOpen_adj_diag_pos (gramPoint_mem_gramOpen T) i
  have hj : 0 < symUnitAdj x j j := gramOpen_adj_diag_pos (gramPoint_mem_gramOpen T) j
  have hinv_ij : symUnitInv x i j = symUnitAdj x i j / (symUnitMat x).det := by
    unfold symUnitInv; simp [div_eq_inv_mul]
  have hinv_ii : symUnitInv x i i = symUnitAdj x i i / (symUnitMat x).det := by
    unfold symUnitInv; simp [div_eq_inv_mul]
  have hinv_jj : symUnitInv x j j = symUnitAdj x j j / (symUnitMat x).det := by
    unfold symUnitInv; simp [div_eq_inv_mul]
  rw [hinv_ij, hinv_ii, hinv_jj]
  have hmul :
      (symUnitAdj x i i / (symUnitMat x).det) * (symUnitAdj x j j / (symUnitMat x).det) =
        (symUnitAdj x i i * symUnitAdj x j j) / (symUnitMat x).det ^ 2 := by ring
  rw [hmul, Real.sqrt_div (mul_nonneg hi.le hj.le), Real.sqrt_sq hdet.le]
  have hden : Real.sqrt (symUnitAdj x i i * symUnitAdj x j j) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hi hj)).ne'
  field_simp [hdet.ne', hden]

theorem dualHeight_eq_adj (T : SphericalTetrahedron) (i : Fin 4) :
    ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ =
      (∑ k : Fin 4, symUnitAdj (gramPoint T) k i) /
        Real.sqrt ((symUnitMat (gramPoint T)).det * symUnitAdj (gramPoint T) i i) := by
  rw [T.normalDualAxis_eq_sum_normalDualRay, sum_inner]
  have hterm : ∀ k : Fin 4,
      ⟪T.normalDualRay k, T.dualVertex i⟫_ℝ =
        symUnitInv (gramPoint T) k i / Real.sqrt (symUnitInv (gramPoint T) i i) := by
    intro k
    unfold dualVertex
    rw [real_inner_smul_right, T.normalDualRay_inner_eq_inv k i,
      T.normalDualRay_norm_eq_sqrt_inv i, div_eq_inv_mul, mul_comm]
  simp_rw [hterm, ← Finset.sum_div]
  set x := gramPoint T
  have hdet : 0 < (symUnitMat x).det := gramOpen_det_pos (gramPoint_mem_gramOpen T)
  have hi : 0 < symUnitAdj x i i := gramOpen_adj_diag_pos (gramPoint_mem_gramOpen T) i
  have hinv_sum : (∑ k : Fin 4, symUnitInv x k i) =
      (∑ k : Fin 4, symUnitAdj x k i) / (symUnitMat x).det := by
    simp_rw [symUnitInv, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, div_eq_inv_mul]
  have hinv_ii : symUnitInv x i i = symUnitAdj x i i / (symUnitMat x).det := by
    unfold symUnitInv; simp [div_eq_inv_mul]
  rw [hinv_sum, hinv_ii, Real.sqrt_div hi.le]
  have hmul : Real.sqrt ((symUnitMat x).det * symUnitAdj x i i) =
      Real.sqrt (symUnitMat x).det * Real.sqrt (symUnitAdj x i i) :=
    Real.sqrt_mul hdet.le _
  rw [hmul]
  have hsdet : Real.sqrt (symUnitMat x).det ≠ 0 := (Real.sqrt_pos.mpr hdet).ne'
  have hsi : Real.sqrt (symUnitAdj x i i) ≠ 0 := (Real.sqrt_pos.mpr hi).ne'
  have hsq : Real.sqrt (symUnitMat x).det ^ 2 = (symUnitMat x).det := Real.sq_sqrt hdet.le
  field_simp [hdet.ne', hsdet, hsi]
  rw [hsq]

end SphericalTetrahedron
