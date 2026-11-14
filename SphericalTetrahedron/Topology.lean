module

public import SolutionCore

@[expose] public section

/-!
# Basic topology of the actual spherical tetrahedron

These lemmas concern `SphericalTetrahedron.body` and `.face` from
`Solution.lean`, rather than a separately parameterized surrogate.
They provide the compactness and measurability needed in the measure
comparison and geometric limits.

The compactness proved here is for each individual nondegenerate
spherical tetrahedron. It does NOT imply compactness of the moduli
space of nondegenerate tetrahedra or existence of an optimizer.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- The intersection of the four closed inward hemispheres with the
unit sphere is closed in the ambient Euclidean four-space. -/
theorem body_isClosed (T : SphericalTetrahedron) : IsClosed T.body := by
  have hsphere : IsClosed {x : E4 | ‖x‖ = 1} :=
    isClosed_singleton.preimage continuous_norm
  have hhalf (i : Fin 4) :
      IsClosed {x : E4 | 0 ≤ ⟪T.normal i, x⟫_ℝ} :=
    isClosed_le continuous_const (by fun_prop)
  have hEq : T.body =
      {x : E4 | ‖x‖ = 1} ∩
        ⋂ i : Fin 4, {x : E4 | 0 ≤ ⟪T.normal i, x⟫_ℝ} := by
    ext x
    simp only [body, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hEq]
  exact hsphere.inter (isClosed_iInter hhalf)

/-- The actual body lies on the unit sphere in `E4`. -/
theorem body_subset_sphere (T : SphericalTetrahedron) :
    T.body ⊆ Metric.sphere (0 : E4) 1 := by
  intro x hx
  change dist x (0 : E4) = 1
  simpa only [dist_zero_right] using hx.1

/-- Every nondegenerate spherical tetrahedron is compact as a set in `E4`. -/
theorem body_isCompact (T : SphericalTetrahedron) : IsCompact T.body := by
  exact (isCompact_sphere (0 : E4) 1).of_isClosed_subset
    (body_isClosed T) (body_subset_sphere T)

/-- Every closed face is closed in the ambient Euclidean four-space. -/
theorem face_isClosed (T : SphericalTetrahedron) (i : Fin 4) :
    IsClosed (T.face i) := by
  have hplane : IsClosed {x : E4 | ⟪T.normal i, x⟫_ℝ = 0} :=
    isClosed_singleton.preimage (by fun_prop)
  have hEq : T.face i =
      T.body ∩ {x : E4 | ⟪T.normal i, x⟫_ℝ = 0} := by
    rfl
  rw [hEq]
  exact (body_isClosed T).inter hplane

/-- Each face is compact as a closed subset of the compact body. -/
theorem face_isCompact (T : SphericalTetrahedron) (i : Fin 4) :
    IsCompact (T.face i) := by
  exact (body_isCompact T).of_isClosed_subset (face_isClosed T i)
    (fun x hx => hx.1)

/-- Spherical tetrahedron bodies are Borel-measurable for Hausdorff measures. -/
theorem body_measurableSet (T : SphericalTetrahedron) :
    MeasurableSet T.body :=
  (body_isClosed T).measurableSet

/-- The faces are Borel-measurable for Hausdorff measures. -/
theorem face_measurableSet (T : SphericalTetrahedron) (i : Fin 4) :
    MeasurableSet (T.face i) :=
  (face_isClosed T i).measurableSet

/-- The real-valued spherical volume in the challenge is nonnegative. -/
theorem volume_nonneg (T : SphericalTetrahedron) : 0 ≤ T.volume :=
  ENNReal.toReal_nonneg

/-- The sum of Hausdorff measures of the four faces is nonnegative. -/
theorem area_nonneg (T : SphericalTetrahedron) : 0 ≤ T.area := by
  unfold area
  apply Finset.sum_nonneg
  intro i hi
  exact ENNReal.toReal_nonneg

end SphericalTetrahedron

namespace SphericalTetrahedron

/-- The closed convex cone defined by the four inward normals. -/
def normalCone (T : SphericalTetrahedron) : Set E4 :=
  {x | ∀ i : Fin 4, 0 ≤ ⟪T.normal i, x⟫_ℝ}

/-- The actual spherical body is the section of the normal cone by `S³`. -/
theorem body_eq_sphere_inter_cone (T : SphericalTetrahedron) :
    T.body = Metric.sphere (0 : E4) 1 ∩ T.normalCone := by
  ext x
  simp only [body, normalCone, Set.mem_inter_iff,
    Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right]

/-- The cone of a spherical tetrahedron is a closed set. -/
theorem normalCone_isClosed (T : SphericalTetrahedron) :
    IsClosed T.normalCone := by
  have hhalf (i : Fin 4) :
      IsClosed {x : E4 | 0 ≤ ⟪T.normal i, x⟫_ℝ} :=
    isClosed_le continuous_const (by fun_prop)
  have hEq : T.normalCone =
      ⋂ i : Fin 4, {x : E4 | 0 ≤ ⟪T.normal i, x⟫_ℝ} := by
    ext x
    simp only [normalCone, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hEq]
  exact isClosed_iInter hhalf

/-- Positive scalar multiplication preserves the defining cone. -/
theorem normalCone_smul {T : SphericalTetrahedron} {x : E4}
    (hx : x ∈ T.normalCone) (r : ℝ) (hr : 0 ≤ r) :
    r • x ∈ T.normalCone := by
  change ∀ i : Fin 4, 0 ≤ ⟪T.normal i, r • x⟫_ℝ
  intro i
  rw [real_inner_smul_right]
  exact mul_nonneg hr (hx i)

/-- The cone defined by inward normals is convex. -/
theorem normalCone_convex (T : SphericalTetrahedron) :
    Convex ℝ T.normalCone := by
  intro x hx y hy a b ha hb hab
  change ∀ i : Fin 4, 0 ≤ ⟪T.normal i, a • x + b • y⟫_ℝ
  intro i
  simp only [inner_add_right, real_inner_smul_right]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- The sum of the inward normals is a distinguished interior direction
of the polar cone. -/
def normalSum (T : SphericalTetrahedron) : E4 :=
  ∑ i : Fin 4, T.normal i

/-- Four independent normals cannot all be orthogonal to a nonzero vector. -/
theorem eq_zero_of_all_normal_inner_zero (T : SphericalTetrahedron)
    (x : E4) (hx : ∀ i : Fin 4, ⟪T.normal i, x⟫_ℝ = 0) :
    x = 0 := by
  classical
  have hdim : Fintype.card (Fin 4) = Module.finrank ℝ E4 := by
    simp [E4]
  let B : Module.Basis (Fin 4) ℝ E4 :=
    basisOfLinearIndependentOfCardEqFinrank T.independent hdim
  have hb (i : Fin 4) : B i = T.normal i := by
    simp [B]
  have hrepr : (∑ i : Fin 4, (B.repr x i) • T.normal i) = x := by
    calc
      (∑ i : Fin 4, (B.repr x i) • T.normal i)
          = ∑ i : Fin 4, (B.repr x i) • B i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hb i]
      _ = x := B.sum_repr x
  have hinner : ⟪x, x⟫_ℝ = 0 := by
    calc
      ⟪x, x⟫_ℝ
          = ⟪∑ i : Fin 4, (B.repr x i) • T.normal i, x⟫_ℝ := by
              rw [hrepr]
      _ = ∑ i : Fin 4, (B.repr x i) * ⟪T.normal i, x⟫_ℝ := by
              simp only [sum_inner, real_inner_smul_left]
      _ = 0 := by simp [hx]
  have hsq : ‖x‖ ^ 2 = 0 := (real_inner_self_eq_norm_sq x).symm.trans hinner
  have hn : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hn

/-- The four inner products with the facet normals, as a linear map
between two real four-dimensional vector spaces. -/
def normalCoordinatesLinear (T : SphericalTetrahedron) :
    E4 →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x i := ⟪T.normal i, x⟫_ℝ
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, inner_add_right]
  map_smul' r x := by
    funext i
    simp only [Pi.smul_apply, real_inner_smul_right, RingHom.id_apply, smul_eq_mul]

/-- The normal-coordinate linear map is injective because the normals
form a basis. -/
theorem normalCoordinatesLinear_injective (T : SphericalTetrahedron) :
    Function.Injective T.normalCoordinatesLinear := by
  intro x y hxy
  have hz : x - y = 0 := by
    apply T.eq_zero_of_all_normal_inner_zero (x - y)
    intro i
    have hi := congrFun hxy i
    change ⟪T.normal i, x⟫_ℝ = ⟪T.normal i, y⟫_ℝ at hi
    rw [inner_sub_right]
    exact sub_eq_zero.mpr hi
  exact sub_eq_zero.mp hz

/-- Linear equivalence between normal coordinates and ambient
coordinates, mapping the general spherical tetrahedron cone to the
standard Euclidean orthant. -/
noncomputable def normalCoordinatesEquiv (T : SphericalTetrahedron) :
    E4 ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofInjectiveOfFinrankEq T.normalCoordinatesLinear
    T.normalCoordinatesLinear_injective (by
      simp [E4, finrank_euclideanSpace_fin])

/-- A cone cut out by a full-rank system of inward normals is
pointed: it contains no nontrivial line. -/
theorem normalCone_pointed (T : SphericalTetrahedron) (x : E4)
    (hx : x ∈ T.normalCone) (hneg : -x ∈ T.normalCone) : x = 0 := by
  apply T.eq_zero_of_all_normal_inner_zero x
  intro i
  have hpos : 0 ≤ ⟪T.normal i, x⟫_ℝ := hx i
  have hneg_i : 0 ≤ ⟪T.normal i, -x⟫_ℝ := hneg i
  rw [inner_neg_right] at hneg_i
  linarith

/-- An actual nondegenerate spherical tetrahedron contains no pair
of antipodal points.  This property may fail in a rank-deficient limit. -/
theorem body_no_antipodal (T : SphericalTetrahedron) {x : E4}
    (hx : x ∈ T.body) : -x ∉ T.body := by
  intro hy
  have hxcone : x ∈ T.normalCone := hx.2
  have hycone : -x ∈ T.normalCone := hy.2
  have hzero : x = 0 := T.normalCone_pointed x hxcone hycone
  have hnorm : ‖x‖ = 0 := by rw [hzero]; exact norm_zero
  have hone : (1 : ℝ) = 0 := hx.1.symm.trans hnorm
  norm_num at hone

/-- All four defining inequalities are simultaneously strict for a
uniformly chosen dual hemisphere direction: the sum of the normals. -/
theorem normalSum_inner_pos (T : SphericalTetrahedron)
    {x : E4} (hx : x ∈ T.body) :
    0 < ⟪T.normalSum, x⟫_ℝ := by
  classical
  have hsum : ⟪T.normalSum, x⟫_ℝ =
      ∑ i : Fin 4, ⟪T.normal i, x⟫_ℝ := by
    simp only [normalSum, sum_inner]
  have hnonneg : 0 ≤ ⟪T.normalSum, x⟫_ℝ := by
    rw [hsum]
    exact Finset.sum_nonneg (fun i _ => hx.2 i)
  rcases eq_or_lt_of_le hnonneg with heq | hpos
  · have hzeroSum : (∑ i : Fin 4, ⟪T.normal i, x⟫_ℝ) = 0 := by
      rw [← hsum]
      exact heq.symm
    have hzero (i : Fin 4) : ⟪T.normal i, x⟫_ℝ = 0 := by
      have hi : ⟪T.normal i, x⟫_ℝ ≤
          ∑ j : Fin 4, ⟪T.normal j, x⟫_ℝ :=
        Finset.single_le_sum (s := Finset.univ)
          (fun j _ => hx.2 j) (Finset.mem_univ i)
      exact le_antisymm (hi.trans_eq hzeroSum) (hx.2 i)
    have hxzero : x = 0 := eq_zero_of_all_normal_inner_zero T x hzero
    have hnormzero : ‖x‖ = 0 := by rw [hxzero]; exact norm_zero
    have : (1 : ℝ) = 0 := hx.1.symm.trans hnormzero
    norm_num at this
  · exact hpos


/-- Every *individual* nondegenerate spherical tetrahedron lies a
positive, uniform distance away from the equator perpendicular to
its sum of inward normals.

Unlike the mere pointwise positivity of the support height, this
is useful for taking a bounded gnomonic chart of the full body.
It does not give a margin uniform across degenerating tetrahedra. -/
theorem normalSum_uniform_pos (T : SphericalTetrahedron) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ T.body, δ ≤ ⟪T.normalSum, x⟫_ℝ := by
  have hcont : ContinuousOn (fun x : E4 => ⟪T.normalSum, x⟫_ℝ) T.body := by
    fun_prop
  exact (T.body_isCompact).exists_forall_le' hcont
    (fun x hx => T.normalSum_inner_pos hx)

/-- A convenient consequence used in future gnomonic-chart proofs. -/
theorem body_subset_strict_hemisphere (T : SphericalTetrahedron) :
    T.body ⊆ {x : E4 | 0 < ⟪T.normalSum, x⟫_ℝ} := by
  intro x hx
  exact T.normalSum_inner_pos hx


/-- Intersecting the cone with the affine hyperplane orthogonal to the
sum of normals gives the Euclidean (gnomonic) model of `T`. -/
def affineSection (T : SphericalTetrahedron) : Set E4 :=
  {z | z ∈ T.normalCone ∧ ⟪T.normalSum, z⟫_ℝ = 1}

/-- The four normal coordinates of every point in the affine section
are nonnegative and sum to one.  Thus the affine section is the
inverse image of the standard Euclidean three-simplex under a linear
coordinate map. -/
theorem affineSection_simplex_coordinates (T : SphericalTetrahedron)
    {z : E4} (hz : z ∈ T.affineSection) :
    (∀ i : Fin 4, 0 ≤ ⟪T.normal i, z⟫_ℝ) ∧
      (∑ i : Fin 4, ⟪T.normal i, z⟫_ℝ) = 1 := by
  refine ⟨hz.1, ?_⟩
  have h := hz.2
  simpa only [normalSum, sum_inner] using h

/-- Radial normalization sends every nonzero point of the cone
into the original spherical body. -/
theorem normalize_mem_body (T : SphericalTetrahedron)
    {z : E4} (hz : z ∈ T.normalCone) (hz0 : z ≠ 0) :
    (‖z‖⁻¹ : ℝ) • z ∈ T.body := by
  change ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 ∧
    ∀ i : Fin 4, 0 ≤ ⟪T.normal i, (‖z‖⁻¹ : ℝ) • z⟫_ℝ
  refine ⟨norm_smul_inv_norm hz0, ?_⟩
  intro i
  rw [real_inner_smul_right]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg z)) (hz i)

/-- The affine section maps back to the spherical body by radial
normalization. -/
theorem affineSection_to_body (T : SphericalTetrahedron)
    {z : E4} (hz : z ∈ T.affineSection) :
    (‖z‖⁻¹ : ℝ) • z ∈ T.body := by
  have hz0 : z ≠ 0 := by
    intro heq
    have hh := hz.2
    rw [heq, inner_zero_right] at hh
    norm_num at hh
  exact T.normalize_mem_body hz.1 hz0

/-- A spherical point maps to the affine hyperplane by dividing by
its strictly positive support height. -/
theorem body_to_affineSection (T : SphericalTetrahedron)
    {x : E4} (hx : x ∈ T.body) :
    (⟪T.normalSum, x⟫_ℝ)⁻¹ • x ∈ T.affineSection := by
  have hpos : 0 < ⟪T.normalSum, x⟫_ℝ := T.normalSum_inner_pos hx
  change (⟪T.normalSum, x⟫_ℝ)⁻¹ • x ∈ T.normalCone ∧
    ⟪T.normalSum, (⟪T.normalSum, x⟫_ℝ)⁻¹ • x⟫_ℝ = 1
  constructor
  · exact T.normalCone_smul hx.2 _ (inv_nonneg.mpr hpos.le)
  · rw [real_inner_smul_right]
    exact inv_mul_cancel₀ hpos.ne'


/-- The invertibility of the four normal coordinates supplies a
point in the spherical tetrahedron. In fact the constructed point has
all four defining inequalities *strict*. -/
theorem body_has_strict_point (T : SphericalTetrahedron) :
    ∃ x ∈ T.body, ∀ i : Fin 4, 0 < ⟪T.normal i, x⟫_ℝ := by
  classical
  let u : Fin 4 → ℝ := fun _ => 1
  let z : E4 := T.normalCoordinatesEquiv.symm u
  have hmap : T.normalCoordinatesLinear z = u := by
    change T.normalCoordinatesEquiv z = u
    exact T.normalCoordinatesEquiv.apply_symm_apply u
  have hzcoordinate (i : Fin 4) : ⟪T.normal i, z⟫_ℝ = 1 := by
    have hi := congrFun hmap i
    change ⟪T.normal i, z⟫_ℝ = 1 at hi
    exact hi
  have hzcone : z ∈ T.normalCone := by
    intro i
    rw [hzcoordinate i]
    norm_num
  have hz0 : z ≠ 0 := by
    intro hzero
    have hh := hzcoordinate (0 : Fin 4)
    rw [hzero, inner_zero_right] at hh
    norm_num at hh
  refine ⟨(‖z‖⁻¹ : ℝ) • z, T.normalize_mem_body hzcone hz0, ?_⟩
  intro i
  rw [real_inner_smul_right, hzcoordinate i, mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr hz0)

/-- Every tetrahedron described by independent unit facet normals has
a nonempty spherical body. -/
theorem body_nonempty (T : SphericalTetrahedron) : T.body.Nonempty := by
  obtain ⟨x, hx, _⟩ := T.body_has_strict_point
  exact ⟨x, hx⟩

/-- Its affine (normal-coordinate) section is nonempty as well. -/
theorem affineSection_nonempty (T : SphericalTetrahedron) :
    T.affineSection.Nonempty := by
  obtain ⟨x, hx⟩ := T.body_nonempty
  exact ⟨_, T.body_to_affineSection hx⟩


/-- The standard 3-simplex in the affine hyperplane `Σ uᵢ = 1`
inside the four-dimensional coordinate space. -/
def standardSimplex4 : Set (Fin 4 → ℝ) :=
  {u | (∀ i : Fin 4, 0 ≤ u i) ∧ (∑ i : Fin 4, u i) = 1}

/-- A point belongs to the tetrahedron's affine section precisely when
its normal-coordinate vector belongs to the standard simplex. -/
theorem mem_affineSection_iff_standardSimplex4
    (T : SphericalTetrahedron) (z : E4) :
    z ∈ T.affineSection ↔
      T.normalCoordinatesLinear z ∈ standardSimplex4 := by
  change
    ((∀ i : Fin 4, 0 ≤ ⟪T.normal i, z⟫_ℝ) ∧
      ⟪T.normalSum, z⟫_ℝ = 1) ↔
    ((∀ i : Fin 4, 0 ≤ ⟪T.normal i, z⟫_ℝ) ∧
      (∑ i : Fin 4, ⟪T.normal i, z⟫_ℝ) = 1)
  simp only [normalSum, sum_inner]

/-- Every point of the standard simplex is the normal-coordinate
vector of a point in the tetrahedron's affine section. -/
theorem standardSimplex4_has_affine_preimage (T : SphericalTetrahedron)
    {u : Fin 4 → ℝ} (hu : u ∈ standardSimplex4) :
    ∃ z ∈ T.affineSection, T.normalCoordinatesLinear z = u := by
  let z : E4 := T.normalCoordinatesEquiv.symm u
  have hmap : T.normalCoordinatesLinear z = u := by
    change T.normalCoordinatesEquiv z = u
    exact T.normalCoordinatesEquiv.apply_symm_apply u
  refine ⟨z, ?_, hmap⟩
  apply (T.mem_affineSection_iff_standardSimplex4 z).2
  rw [hmap]
  exact hu


/-- Any ℓ¹ lower frame bound for the system of inward normals
immediately gives a quantitative hemisphere margin. In particular,
one may later take the least singular value of the invertible
normal-coordinate map as the constant `c`. -/
theorem normalSum_ge_of_coordinate_frame_bound
    (T : SphericalTetrahedron) (c : ℝ)
    (hframe : ∀ x : E4,
      c * ‖x‖ ≤ ∑ i : Fin 4, |⟪T.normal i, x⟫_ℝ|)
    {x : E4} (hx : x ∈ T.body) :
    c ≤ ⟪T.normalSum, x⟫_ℝ := by
  have habs : (∑ i : Fin 4, |⟪T.normal i, x⟫_ℝ|) =
      ∑ i : Fin 4, ⟪T.normal i, x⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (hx.2 i)
  have h := hframe x
  rw [habs, hx.1] at h
  simpa only [mul_one, normalSum, sum_inner] using h

end SphericalTetrahedron
