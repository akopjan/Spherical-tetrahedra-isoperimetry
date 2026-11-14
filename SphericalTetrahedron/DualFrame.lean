module

public import SphericalTetrahedron.AffineChart

@[expose] public section

/-!
# Canonical dual vertices and an intrinsic stationarity equation

The four normal coordinates of any spherical tetrahedron give explicit,
canonically determined dual vertices: the unit vectors lying on the four
coordinate rays.  The orthogonality, positivity and unit-length conditions
in `T.Stationary` force any witnesses `v i` to be these very vertices.
Likewise the witness `q` is the inverse image of the all-ones coordinate
vector.  Hence stationarity reduces to four fixed vertices and one real
multiplier, instead of introducing five unconstrained geometric witnesses.

The analytic first variation is established separately in
`ManuscriptFirstVariation`.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- The inverse image of the `i`-th nonnegative coordinate ray. -/
def normalDualRay (T : SphericalTetrahedron) (j : Fin 4) : E4 :=
  T.normalCoordinatesEquiv.symm
    (fun i : Fin 4 => if i = j then 1 else 0)

/-- The normal-coordinate matrix of the four dual rays is the identity. -/
theorem normalDualRay_inner (T : SphericalTetrahedron) (i j : Fin 4) :
    ⟪T.normal i, T.normalDualRay j⟫_ℝ =
      (if i = j then 1 else 0) := by
  have h := congrFun
    (T.normalCoordinatesLinear_symm_apply
      (fun k : Fin 4 => if k = j then (1 : ℝ) else 0)) i
  exact h

/-- Each dual ray is nonzero, with positive norm. -/
theorem normalDualRay_ne_zero (T : SphericalTetrahedron) (j : Fin 4) :
    T.normalDualRay j ≠ 0 := by
  intro hz
  have h := T.normalDualRay_inner j j
  rw [hz, inner_zero_right] at h
  norm_num at h

/-- The unique unit vector in the positive dual coordinate ray. -/
def dualVertex (T : SphericalTetrahedron) (j : Fin 4) : E4 :=
  (‖T.normalDualRay j‖⁻¹ : ℝ) • T.normalDualRay j

/-- The canonical dual vertices have norm one. -/
theorem dualVertex_norm (T : SphericalTetrahedron) (j : Fin 4) :
    ‖T.dualVertex j‖ = 1 := by
  have hp : 0 < ‖T.normalDualRay j‖ :=
    norm_pos_iff.mpr (T.normalDualRay_ne_zero j)
  unfold dualVertex
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ hp.ne'

/-- A dual vertex is orthogonal to all normal vectors with different indices. -/
theorem dualVertex_offdiag (T : SphericalTetrahedron)
    (i j : Fin 4) (hij : i ≠ j) :
    ⟪T.normal i, T.dualVertex j⟫_ℝ = 0 := by
  unfold dualVertex
  rw [real_inner_smul_right, T.normalDualRay_inner]
  simp [hij]

/-- The diagonal pairing of normal and dual vertex is strictly positive. -/
theorem dualVertex_diagonal_pos (T : SphericalTetrahedron) (i : Fin 4) :
    0 < ⟪T.normal i, T.dualVertex i⟫_ℝ := by
  have hp : 0 < ‖T.normalDualRay i‖ :=
    norm_pos_iff.mpr (T.normalDualRay_ne_zero i)
  unfold dualVertex
  rw [real_inner_smul_right, T.normalDualRay_inner]
  simpa using (inv_pos.mpr hp)

/-- Each canonical dual unit vector is an actual vertex of the spherical
body, rather than an auxiliary vector in an unrelated model. -/
theorem dualVertex_mem_body (T : SphericalTetrahedron) (j : Fin 4) :
    T.dualVertex j ∈ T.body := by
  change ‖T.dualVertex j‖ = 1 ∧
    ∀ i : Fin 4, 0 ≤ ⟪T.normal i, T.dualVertex j⟫_ℝ
  refine ⟨T.dualVertex_norm j, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    exact le_of_lt (T.dualVertex_diagonal_pos j)
  · rw [T.dualVertex_offdiag i j hij]

/-- Dual vertex `j` lies on exactly the three facets indexed by
`i ≠ j`; this direction establishes incidence with every such facet. -/
theorem dualVertex_mem_face (T : SphericalTetrahedron)
    {i j : Fin 4} (hij : i ≠ j) :
    T.dualVertex j ∈ T.face i := by
  exact ⟨T.dualVertex_mem_body j, T.dualVertex_offdiag i j hij⟩

/-- The dual vertices are pairwise distinct, by their normal-coordinate
pairings. -/
theorem dualVertex_injective (T : SphericalTetrahedron) :
    Function.Injective T.dualVertex := by
  intro i j hEq
  by_contra hij
  have hp := T.dualVertex_diagonal_pos i
  have hz := T.dualVertex_offdiag i j hij
  rw [← hEq] at hz
  exact (ne_of_gt hp) hz

/-- Normal-coordinate height one in every coordinate picks a unique
distinguished dual axis `q`, independent of stationarity. -/
def normalDualAxis (T : SphericalTetrahedron) : E4 :=
  T.normalCoordinatesEquiv.symm (fun _ : Fin 4 => 1)

theorem normalDualAxis_inner (T : SphericalTetrahedron) (i : Fin 4) :
    ⟪T.normal i, T.normalDualAxis⟫_ℝ = 1 := by
  have h := congrFun
    (T.normalCoordinatesLinear_symm_apply (fun _ : Fin 4 => (1 : ℝ))) i
  exact h

/-- Every vector that pairs to one with all four normals is the
distinguished dual axis. -/
theorem normalDualAxis_unique (T : SphericalTetrahedron) (q : E4)
    (hq : ∀ i : Fin 4, ⟪T.normal i, q⟫_ℝ = 1) :
    q = T.normalDualAxis := by
  apply T.normalCoordinatesLinear_injective
  funext i
  exact (hq i).trans (T.normalDualAxis_inner i).symm

/-- The distinguished dual axis is the sum of the four dual rays.
This identifies the abstract witness `q` with an explicit basis sum. -/
theorem normalDualAxis_eq_sum_normalDualRay (T : SphericalTetrahedron) :
    T.normalDualAxis = ∑ j : Fin 4, T.normalDualRay j := by
  apply T.normalCoordinatesLinear_injective
  funext i
  change ⟪T.normal i, T.normalDualAxis⟫_ℝ =
    ⟪T.normal i, ∑ j : Fin 4, T.normalDualRay j⟫_ℝ
  rw [T.normalDualAxis_inner, inner_sum]
  simp [T.normalDualRay_inner]

/-- The dual axis has normal-coordinate height exactly four. -/
theorem normalDualAxis_sum_inner (T : SphericalTetrahedron) :
    ⟪T.normalSum, T.normalDualAxis⟫_ℝ = 4 := by
  rw [normalSum, sum_inner]
  simp [T.normalDualAxis_inner, Fin.sum_univ_succ]

/-- A quarter of the dual axis is the affine simplex barycenter:
all its normal coordinates are equal to `1/4`. -/
theorem normalDualAxis_quarter_mem_affineSection (T : SphericalTetrahedron) :
    ((4 : ℝ)⁻¹ • T.normalDualAxis) ∈ T.affineSection := by
  change (∀ i : Fin 4,
      0 ≤ ⟪T.normal i, ((4 : ℝ)⁻¹ • T.normalDualAxis)⟫_ℝ) ∧
    ⟪T.normalSum, ((4 : ℝ)⁻¹ • T.normalDualAxis)⟫_ℝ = 1
  constructor
  · intro i
    rw [real_inner_smul_right, T.normalDualAxis_inner]
    norm_num
  · rw [real_inner_smul_right, T.normalDualAxis_sum_inner]
    norm_num

/-- The positive dual axis provides an explicit point of the
nondegenerate spherical tetrahedron, with *all* facet inequalities strict. -/
theorem normalDualAxis_radial_interior (T : SphericalTetrahedron) :
    radialNormalize T.normalDualAxis ∈ T.body ∧
      ∀ i : Fin 4,
        0 < ⟪T.normal i, radialNormalize T.normalDualAxis⟫_ℝ := by
  have hzero : T.normalDualAxis ≠ 0 := by
    intro hz
    have h := T.normalDualAxis_inner (0 : Fin 4)
    rw [hz, inner_zero_right] at h
    norm_num at h
  have hn : 0 < ‖T.normalDualAxis‖ := norm_pos_iff.mpr hzero
  constructor
  · apply T.normalize_mem_body
    · intro i
      rw [T.normalDualAxis_inner]
      norm_num
    · exact hzero
  · intro i
    unfold radialNormalize
    rw [real_inner_smul_right, T.normalDualAxis_inner, mul_one]
    exact inv_pos.mpr hn

/-- Unit, positive, off-diagonal-orthogonal vectors necessarily agree
with the explicit canonical dual vertices. -/
theorem dualVertex_unique (T : SphericalTetrahedron)
    (v : Fin 4 → E4)
    (hUnit : ∀ j : Fin 4, ‖v j‖ = 1)
    (hOff : ∀ i j : Fin 4, i ≠ j →
      ⟪T.normal i, v j⟫_ℝ = 0)
    (hPos : ∀ j : Fin 4, 0 < ⟪T.normal j, v j⟫_ℝ) :
    ∀ j : Fin 4, v j = T.dualVertex j := by
  intro j
  let α : ℝ := ⟪T.normal j, v j⟫_ℝ
  have hα : 0 < α := hPos j
  have hRay : v j = α • T.normalDualRay j := by
    apply T.normalCoordinatesLinear_injective
    funext i
    change ⟪T.normal i, v j⟫_ℝ =
      ⟪T.normal i, α • T.normalDualRay j⟫_ℝ
    rw [real_inner_smul_right, T.normalDualRay_inner]
    by_cases hij : i = j
    · subst i
      simp [α]
    · rw [if_neg hij, mul_zero]
      exact hOff i j hij
  have hRayPos : 0 < ‖T.normalDualRay j‖ :=
    norm_pos_iff.mpr (T.normalDualRay_ne_zero j)
  have hScaledNorm : ‖α • T.normalDualRay j‖ =
      α * ‖T.normalDualRay j‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
  have hEq : α * ‖T.normalDualRay j‖ = 1 := by
    calc
      α * ‖T.normalDualRay j‖ = ‖α • T.normalDualRay j‖ :=
        hScaledNorm.symm
      _ = ‖v j‖ := by rw [hRay]
      _ = 1 := hUnit j
  have hScalar : α = ‖T.normalDualRay j‖⁻¹ := by
    apply mul_right_cancel₀ hRayPos.ne'
    exact hEq.trans (inv_mul_cancel₀ hRayPos.ne').symm
  calc
    v j = α • T.normalDualRay j := hRay
    _ = T.dualVertex j := by rw [hScalar]; rfl

/-- The abstract `Stationary` predicate is equivalent to one explicit
system on the canonically determined dual vertices and a single
nonzero real multiplier. This removes the existential geometric witness
ambiguity from the rigidity problem. -/
theorem stationary_iff_dualVertex_equations (T : SphericalTetrahedron) :
    T.Stationary ↔
      ∃ c : ℝ, c ≠ 0 ∧
        ∀ i j : Fin 4, i ≠ j →
          ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ +
            ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ =
              c * stationaryKernel
                ⟪T.dualVertex i, T.dualVertex j⟫_ℝ := by
  constructor
  · rintro ⟨v, q, c, hc, hUnit, hOff, hPos, hq, hEq⟩
    have hV : ∀ i, v i = T.dualVertex i :=
      T.dualVertex_unique v hUnit hOff hPos
    have hQ : q = T.normalDualAxis := T.normalDualAxis_unique q hq
    refine ⟨c, hc, ?_⟩
    intro i j hij
    simpa only [hQ, hV] using hEq i j hij
  · rintro ⟨c, hc, hEq⟩
    refine ⟨T.dualVertex, T.normalDualAxis, c, hc, ?_, ?_, ?_, ?_, ?_⟩
    · exact T.dualVertex_norm
    · intro i j hij
      exact T.dualVertex_offdiag i j hij
    · exact T.dualVertex_diagonal_pos
    · exact T.normalDualAxis_inner
    · exact hEq

end SphericalTetrahedron
