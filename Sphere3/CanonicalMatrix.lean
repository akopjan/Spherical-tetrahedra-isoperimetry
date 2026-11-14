module

public import Sphere3.CanonicalGram

@[expose] public section

/-!
# The canonical normal matrix

Rows are the four unnormalized inward facet normals in `R^4`.
The determinant computation is a short exact algebraic certificate;
for `t > 0` the normals are independent.
-/

namespace Sphere3

/-- Four inward facet normals, as rows of a 4-by-4 matrix. -/
def canonicalNormalMatrix (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 1,  1,  1, t;
      1, -1, -1, t;
     -1,  1, -1, t;
     -1, -1,  1, t]

/-- The determinant is positive precisely when the height parameter
is positive. -/
theorem canonicalNormalMatrix_det (t : ℝ) :
    (canonicalNormalMatrix t).det = 16 * t := by
  unfold canonicalNormalMatrix
  eval_det
  ring

/-- The raw canonical normal matrix has nonzero determinant for `t > 0`. -/
theorem canonicalNormalMatrix_det_ne_zero (t : ℝ) (ht : 0 < t) :
    (canonicalNormalMatrix t).det ≠ 0 := by
  rw [canonicalNormalMatrix_det]
  positivity

/-- The raw canonical normal matrix has positive determinant for `t > 0`. -/
theorem canonicalNormalMatrix_det_pos (t : ℝ) (ht : 0 < t) :
    0 < (canonicalNormalMatrix t).det := by
  rw [canonicalNormalMatrix_det]
  positivity

/-- The four canonical raw inward normals form a basis of `R^4`
for every positive parameter. -/
theorem canonicalNormalMatrix_rows_independent (t : ℝ) (ht : 0 < t) :
    LinearIndependent ℝ (canonicalNormalMatrix t).row := by
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (canonicalNormalMatrix_det_ne_zero t ht)

end Sphere3
