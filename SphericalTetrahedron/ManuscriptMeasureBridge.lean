module

public import Mathlib
public import Sphere3.GirardAlgebra
public import SphericalTetrahedron.DualFrame
public import SphericalTetrahedron.DualPolarity

@[expose] public section

/-!
# Measure Bridge: Hausdorff Measure, `toSphere`, Lune Measure, and Girard's Formula

This module connects the raw unnormalized Hausdorff measures `(Measure.hausdorffMeasure 3 : Measure E4)`
and `(Measure.hausdorffMeasure 2 : Measure E4)` used in `SolutionCore` / `Challenge.lean` to Mathlib's
spherical Haar measure `Measure.toSphere` via compact `O(n)` Haar uniqueness:

1. `OGroup n := Matrix.orthogonalGroup (Fin n) ℝ` is compact and second-countable; its Haar measure
   is bi-invariant and acts transitively on `Metric.sphere (0 : E n) 1` via Householder reflections.
2. Any two `O(n)`-invariant finite Borel measures on `Metric.sphere (0 : E n) 1` are constant
   multiples of each other (`ortho_invariant_sphere_measure_eq`).
3. For `1 ≤ d`, `0 < μH[d] (Metric.sphere (0 : E (d + 1)) 1) < ⊤`, giving scale constants
   `sphereScale d > 0` (`d = 2, 3`) relating `μH[d]` to `(MeasureTheory.volume : Measure (E (d + 1))).toSphere`.
4. Exact spherical lune measure via rotational partitions of `[0, 2π]` and Girard's formula
   (`measure_face_eq_faceScale_mul_stdFaceArea`), plus `stdArea T < 4 * Real.pi` via vertex link duals.
-/

noncomputable section

open scoped InnerProductSpace BigOperators Matrix ENNReal NNReal Pointwise
open MeasureTheory

namespace SphericalTetrahedron

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev E3 := E 3
abbrev OGroup (n : ℕ) := Matrix.orthogonalGroup (Fin n) ℝ

section OrthogonalGroupHaar

instance instSecondCountableMatrix (m n : Type*) [Finite m] [Finite n] :
    SecondCountableTopology (Matrix m n ℝ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℝ))

instance instSecondCountableOGroup (n : ℕ) : SecondCountableTopology (OGroup n) :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

instance instCompactOGroup (n : ℕ) : CompactSpace (OGroup n) := by
  have hClosed : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A * Aᵀ = 1} :=
    isClosed_eq (Continuous.matrix_mul continuous_id continuous_id.matrix_transpose) continuous_const
  have hEq : (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) =
      {A : Matrix (Fin n) (Fin n) ℝ | A * Aᵀ = 1} := by
    ext A
    exact Matrix.mem_orthogonalGroup_iff (Fin n) ℝ
  have hSub : (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) ⊆
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1 := by
    intro A hA i _ j _
    simpa [Real.norm_eq_abs, abs_le] using entry_norm_bound_of_unitary hA i j
  have hK : IsCompact (Set.pi Set.univ fun (_ : Fin n) =>
      Set.pi Set.univ fun (_ : Fin n) => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  exact isCompact_iff_compactSpace.mp (hK.of_isClosed_subset (hEq ▸ hClosed) hSub)

theorem isMulRightInvariant_haar_oGroup (n : ℕ) :
    (Measure.haar : Measure (OGroup n)).IsMulRightInvariant := by
  constructor
  intro g
  let μ : Measure (OGroup n) := Measure.haar
  let μ' : Measure (OGroup n) := Measure.map (· * g) μ
  have hcont : Continuous (fun x : OGroup n => x * g) := continuous_id.mul continuous_const
  have hLeft : μ'.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    have hm1 : Measurable (fun x : OGroup n => h * x) :=
      (continuous_const.mul continuous_id).measurable
    have hm2 : Measurable (fun x : OGroup n => x * g) := hcont.measurable
    dsimp [μ']
    have hcomp : (fun x : OGroup n => h * x) ∘ (fun x : OGroup n => x * g) =
        (fun x : OGroup n => x * g) ∘ (fun x : OGroup n => h * x) := by
      ext x
      simp [mul_assoc]
    calc Measure.map (fun x => h * x) (Measure.map (fun x => x * g) μ)
        = Measure.map ((fun x => h * x) ∘ (fun x => x * g)) μ := Measure.map_map hm1 hm2
      _ = Measure.map ((fun x => x * g) ∘ (fun x => h * x)) μ := by rw [hcomp]
      _ = Measure.map (fun x => x * g) (Measure.map (fun x => h * x) μ) :=
            (Measure.map_map hm2 hm1).symm
      _ = Measure.map (fun x => x * g) μ := by rw [MeasureTheory.map_mul_left_eq_self μ h]
  have hFin : IsFiniteMeasureOnCompacts μ' := by
    refine ⟨fun K _ => ?_⟩
    calc μ' K ≤ μ' Set.univ := measure_mono (Set.subset_univ _)
      _ = μ ((· * g) ⁻¹' Set.univ) := Measure.map_apply hcont.measurable MeasurableSet.univ
      _ = μ Set.univ := by simp
      _ < ⊤ := measure_lt_top μ Set.univ
  have hEq := Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ
  let c : ℝ≥0 := μ'.haarScalarFactor μ
  have hcEq : μ' = c • μ := hEq
  have hUniv : μ' Set.univ = (c : ℝ≥0∞) * μ Set.univ := by
    rw [hcEq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hUnivL : μ' Set.univ = μ Set.univ := by
    rw [Measure.map_apply hcont.measurable MeasurableSet.univ]
    simp
  rw [hUnivL] at hUniv
  have hPos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have hTop : μ Set.univ ≠ ⊤ := (measure_lt_top μ Set.univ).ne
  have hScalar : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hPos hTop).mp (by simpa [one_mul] using hUniv.symm)
  have hc1 : c = 1 := ENNReal.coe_eq_one.mp hScalar
  change μ' = μ
  rw [hcEq, hc1, one_smul]

/-- Normalized Haar probability measure on `OGroup n`. -/
def haarOGroup (n : ℕ) : Measure (OGroup n) :=
  ((Measure.haar : Measure (OGroup n)) Set.univ)⁻¹ • (Measure.haar : Measure (OGroup n))

instance instIsProbabilityMeasure_haarOGroup (n : ℕ) : IsProbabilityMeasure (haarOGroup n) := by
  refine ⟨?_⟩
  have hPos : (Measure.haar : Measure (OGroup n)) Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have hTop : (Measure.haar : Measure (OGroup n)) Set.univ ≠ ⊤ :=
    (measure_lt_top _ Set.univ).ne
  simp [haarOGroup, ENNReal.inv_mul_cancel hPos hTop]

instance instIsMulRightInvariant_haarOGroup (n : ℕ) :
    (haarOGroup n).IsMulRightInvariant := by
  haveI := isMulRightInvariant_haar_oGroup n
  dsimp [haarOGroup]
  infer_instance

/-- Matrix action of `Matrix (Fin n) (Fin n) ℝ` on `EuclideanSpace ℝ (Fin n)`. -/
def mulVecE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : E n) : E n :=
  WithLp.toLp 2 (Matrix.mulVec A x.ofLp)

@[simp]
theorem mulVecE_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : E n) (i : Fin n) :
    mulVecE A x i = ∑ j, A i j * x j := rfl

theorem continuous_mulVecE {n : ℕ} :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × E n => mulVecE p.1 p.2) := by
  change Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × E n =>
    WithLp.toLp 2 (fun i : Fin n => ∑ j : Fin n, p.1 i j * p.2 j))
  refine (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp ?_
  refine continuous_pi fun i => continuous_finset_sum Finset.univ fun j _ => ?_
  have hA : Continuous (fun q : Matrix (Fin n) (Fin n) ℝ × E n => q.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hx : Continuous (fun q : Matrix (Fin n) (Fin n) ℝ × E n => q.2 j) :=
    (continuous_apply j).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp continuous_snd)
  exact hA.mul hx

theorem ortho_mulVecE_inner {n : ℕ} (g : OGroup n) (x y : E n) :
    ⟪mulVecE g.1 x, mulVecE g.1 y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have hg : g.1ᵀ * g.1 = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp g.2
  simp only [PiLp.inner_apply, mulVecE_apply, RCLike.inner_apply, conj_trivial]
  calc ∑ i : Fin n, (∑ j : Fin n, g.1 i j * y j) * (∑ k : Fin n, g.1 i k * x k)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (g.1 i j * g.1 i k) * (y j * x k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ j : Fin n, ∑ k : Fin n,
          (∑ i : Fin n, g.1 i j * g.1 i k) * (y j * x k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ j : Fin n, ∑ k : Fin n, (if j = k then (1 : ℝ) else 0) * (y j * x k) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          have hjk := congrFun (congrFun hg j) k
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hjk
          rw [hjk]
    _ = ∑ i : Fin n, y i * x i := by simp

theorem ortho_mulVecE_mul {n : ℕ} (g h : OGroup n) (x : E n) :
    mulVecE (g * h).1 x = mulVecE g.1 (mulVecE h.1 x) := by
  ext i
  simp only [mulVecE_apply, Submonoid.coe_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

theorem ortho_mulVecE_one {n : ℕ} (x : E n) :
    mulVecE (1 : OGroup n).1 x = x := by
  ext i
  simp [mulVecE_apply, Matrix.one_apply]

/-- Linear isometric equivalence induced by an orthogonal matrix `g : OGroup n`. -/
def orthoEquiv {n : ℕ} (g : OGroup n) : E n ≃ₗᵢ[ℝ] E n :=
  let L : E n ≃ₗ[ℝ] E n :=
    { toFun := mulVecE g.1
      invFun := mulVecE (g⁻¹).1
      map_add' := fun x y => by ext i; simp [mulVecE_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext i
        simp only [mulVecE_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl fun j _ => by ring
      left_inv := fun x => by
        change mulVecE (g⁻¹).1 (mulVecE g.1 x) = x
        rw [← ortho_mulVecE_mul, inv_mul_cancel, ortho_mulVecE_one]
      right_inv := fun x => by
        change mulVecE g.1 (mulVecE (g⁻¹).1 x) = x
        rw [← ortho_mulVecE_mul, mul_inv_cancel, ortho_mulVecE_one] }
  L.isometryOfInner (ortho_mulVecE_inner g)

@[simp]
theorem orthoEquiv_apply {n : ℕ} (g : OGroup n) (x : E n) :
    orthoEquiv g x = mulVecE g.1 x := rfl

@[simp]
theorem orthoEquiv_one {n : ℕ} (x : E n) :
    orthoEquiv (1 : OGroup n) x = x :=
  ortho_mulVecE_one x

@[simp]
theorem orthoEquiv_mul {n : ℕ} (g h : OGroup n) (x : E n) :
    orthoEquiv (g * h) x = orthoEquiv g (orthoEquiv h x) :=
  ortho_mulVecE_mul g h x

/-- Action of `OGroup n` as a self-homeomorphism of the unit sphere `Metric.sphere (0 : E n) 1`. -/
def orthoSphereAct {n : ℕ} (g : OGroup n) :
    Metric.sphere (0 : E n) 1 ≃ₜ Metric.sphere (0 : E n) 1 where
  toFun x := ⟨orthoEquiv g x.1, by
    rw [Metric.mem_sphere, dist_zero_right, (orthoEquiv g).norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using x.2⟩
  invFun x := ⟨orthoEquiv g⁻¹ x.1, by
    rw [Metric.mem_sphere, dist_zero_right, (orthoEquiv g⁻¹).norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using x.2⟩
  left_inv x := Subtype.ext <| by
    change orthoEquiv g⁻¹ (orthoEquiv g x.1) = x.1
    rw [← orthoEquiv_mul, inv_mul_cancel]
    exact ortho_mulVecE_one x.1
  right_inv x := Subtype.ext <| by
    change orthoEquiv g (orthoEquiv g⁻¹ x.1) = x.1
    rw [← orthoEquiv_mul, mul_inv_cancel]
    exact ortho_mulVecE_one x.1
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_mulVecE.comp (continuous_const.prodMk continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_mulVecE.comp (continuous_const.prodMk continuous_subtype_val)

@[simp]
theorem orthoSphereAct_val {n : ℕ} (g : OGroup n) (x : Metric.sphere (0 : E n) 1) :
    (orthoSphereAct g x).1 = orthoEquiv g x.1 := rfl

theorem continuous_orthoSphereAct_uncurry {n : ℕ} :
    Continuous (fun p : OGroup n × Metric.sphere (0 : E n) 1 => orthoSphereAct p.1 p.2) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_mulVecE.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

/-- Householder reflection across hyperplane `u^⊥` for a unit vector `u`. -/
def householderMatrix {n : ℕ} (u : E n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - 2 * u i * u j

theorem householderMatrix_mem_oGroup {n : ℕ} {u : E n} (hu : ‖u‖ = 1) :
    householderMatrix u ∈ OGroup n := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  have hnorm : ∑ k : Fin n, u k * u k = 1 := by
    have h : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    rw [PiLp.inner_apply] at h
    simpa only [RCLike.inner_apply, conj_trivial] using h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, householderMatrix, Matrix.of_apply,
    Matrix.one_apply]
  have expand : ∀ k : Fin n,
      ((if i = k then (1 : ℝ) else 0) - 2 * u i * u k) *
        ((if j = k then (1 : ℝ) else 0) - 2 * u j * u k) =
      (if i = k then (if j = k then (1 : ℝ) else 0) else 0) -
        2 * (if i = k then 1 else 0) * (u j * u k) -
        2 * (if j = k then 1 else 0) * (u i * u k) +
        4 * (u i * u j) * (u k * u k) := fun k => by split_ifs <;> ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ k : Fin n, (if i = k then (if j = k then (1 : ℝ) else 0) else 0) =
      if i = j then (1 : ℝ) else 0 := by
    have hs : ∀ k : Fin n, (if i = k then (if j = k then (1 : ℝ) else 0) else 0) =
        if i = k then (if i = j then 1 else 0) else 0 := fun k => by
      by_cases hik : i = k
      · subst hik; by_cases hij : i = j <;> simp [hij, eq_comm]
      · simp [hik]
    simp_rw [hs, Finset.sum_ite_eq]
    simp
  have h2 : ∑ k : Fin n, 2 * (if i = k then (1 : ℝ) else 0) * (u j * u k) =
      2 * (u j * u i) := by
    have : ∀ k : Fin n, 2 * (if i = k then (1 : ℝ) else 0) * (u j * u k) =
        if i = k then 2 * (u j * u k) else 0 := fun k => by split_ifs <;> ring
    simp_rw [this, Finset.sum_ite_eq Finset.univ i]
    simp
  have h3 : ∑ k : Fin n, 2 * (if j = k then (1 : ℝ) else 0) * (u i * u k) =
      2 * (u i * u j) := by
    have : ∀ k : Fin n, 2 * (if j = k then (1 : ℝ) else 0) * (u i * u k) =
        if j = k then 2 * (u i * u k) else 0 := fun k => by split_ifs <;> ring
    simp_rw [this, Finset.sum_ite_eq Finset.univ j]
    simp
  rw [h1, h2, h3, hnorm]
  ring

def householderOGroup {n : ℕ} (u : E n) (hu : ‖u‖ = 1) : OGroup n :=
  ⟨householderMatrix u, householderMatrix_mem_oGroup hu⟩

theorem householder_apply {n : ℕ} (u : E n) (hu : ‖u‖ = 1) (x : E n) :
    orthoEquiv (householderOGroup u hu) x = x - (2 * ⟪u, x⟫_ℝ) • u := by
  ext i
  have hinn : ⟪u, x⟫_ℝ = ∑ j : Fin n, x j * u j := by
    simp [PiLp.inner_apply, RCLike.inner_apply]
  simp only [orthoEquiv_apply, mulVecE_apply, householderOGroup, householderMatrix,
    Matrix.of_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) * x j = x i := by
    have : ∀ j : Fin n, (if i = j then (1 : ℝ) else 0) * x j =
        if i = j then x j else 0 := fun j => by split_ifs <;> ring
    simp_rw [this, Finset.sum_ite_eq Finset.univ i]
    simp
  have h2 : ∑ j : Fin n, 2 * u i * u j * x j = 2 * ⟪u, x⟫_ℝ * u i := by
    rw [hinn]
    calc ∑ j : Fin n, 2 * u i * u j * x j
        = ∑ j : Fin n, (x j * u j) * (2 * u i) :=
            Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j : Fin n, x j * u j) * (2 * u i) := (Finset.sum_mul _ _ _).symm
      _ = 2 * (∑ j : Fin n, x j * u j) * u i := by ring
  rw [h1, h2]

theorem oGroup_transitive_sphere {n : ℕ} (x y : Metric.sphere (0 : E n) 1) :
    ∃ g : OGroup n, orthoSphereAct g x = y := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨1, Subtype.ext (ortho_mulVecE_one x.1)⟩
  · have hne : x.1 - y.1 ≠ 0 := sub_ne_zero.mpr (fun h => hxy (Subtype.ext h))
    have hdn : ‖x.1 - y.1‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    let u : E n := ‖x.1 - y.1‖⁻¹ • (x.1 - y.1)
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn]
    refine ⟨householderOGroup u hu, Subtype.ext ?_⟩
    rw [orthoSphereAct_val, householder_apply u hu x.1]
    have hx1 : ‖x.1‖ = 1 := by simpa using x.2
    have hy1 : ‖y.1‖ = 1 := by simpa using y.2
    have hnormSq : ‖x.1 - y.1‖ ^ 2 = 2 - 2 * ⟪x.1, y.1⟫_ℝ := by
      rw [@norm_sub_sq_real, hx1, hy1]
      ring
    have hdot : ⟪x.1 - y.1, x.1⟫_ℝ = 1 - ⟪x.1, y.1⟫_ℝ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, hx1, real_inner_comm x.1 y.1]
      ring
    have hcoeff : 2 * ⟪u, x.1⟫_ℝ * ‖x.1 - y.1‖⁻¹ = 1 := by
      rw [real_inner_smul_left, hdot]
      have hsq : ‖x.1 - y.1‖ * ‖x.1 - y.1‖ = 2 * (1 - ⟪x.1, y.1⟫_ℝ) := by
        linarith [sq (‖x.1 - y.1‖), hnormSq]
      field_simp [hdn]
      linarith
    have hvec : (2 * ⟪u, x.1⟫_ℝ) • u = x.1 - y.1 := by
      simp only [u, smul_smul, hcoeff, one_smul]
    rw [hvec]
    abel

theorem ortho_invariant_sphere_measure_eq {n : ℕ} [NeZero n]
    (ν₁ ν₂ : Measure (Metric.sphere (0 : E n) 1))
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : ∀ g : OGroup n, Measure.map (orthoSphereAct g) ν₁ = ν₁)
    (h₂ : ∀ g : OGroup n, Measure.map (orthoSphereAct g) ν₂ = ν₂) :
    ENNReal.ofReal (ν₁.real Set.univ) • ν₂ = ENNReal.ofReal (ν₂.real Set.univ) • ν₁ := by
  let S := Metric.sphere (0 : E n) 1
  let e0 : E n := WithLp.toLp 2 (fun i : Fin n => if i = 0 then (1 : ℝ) else 0)
  have he0 : ‖e0‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg e0) two_ne_zero, ← real_inner_self_eq_norm_sq]
    simp only [e0, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, WithLp.ofLp_toLp]
    have : ∀ i : Fin n, (if i = 0 then (1 : ℝ) else 0) * (if i = 0 then (1 : ℝ) else 0) =
        if 0 = i then 1 else 0 := fun i => by by_cases h : i = 0 <;> simp [h, eq_comm]
    simp_rw [this]
    simp
  let e₀ : S := ⟨e0, show e0 ∈ S by simp [S, Metric.mem_sphere, dist_zero_right, he0]⟩
  let μG := haarOGroup n
  have key (ν : Measure S) [IsFiniteMeasure ν]
      (hν : ∀ g : OGroup n, Measure.map (orthoSphereAct g) ν = ν)
      {s : Set S} (hs : MeasurableSet s) :
      ν.real s = μG.real {g : OGroup n | orthoSphereAct g e₀ ∈ s} * ν.real Set.univ := by
    let f : OGroup n → S → ℝ := fun g x => s.indicator (fun _ => (1 : ℝ)) (orthoSphereAct g x)
    have hfMeas : Measurable (Function.uncurry f) :=
      (measurable_const.indicator hs).comp continuous_orthoSphereAct_uncurry.measurable
    have hfBnd : ∀ p : OGroup n × S, ‖Function.uncurry f p‖ ≤ 1 := fun p => by
      by_cases hp : orthoSphereAct p.1 p.2 ∈ s <;> simp [Function.uncurry, f, hp]
    have hfInt : Integrable (Function.uncurry f) (μG.prod ν) :=
      Integrable.of_bound hfMeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hfBnd)
    have hLHS : ∫ g : OGroup n, ∫ x : S, f g x ∂ν ∂μG = ν.real s := by
      have hInner : ∀ g : OGroup n, ∫ x : S, f g x ∂ν = ν.real s := by
        intro g
        have hm := MeasureTheory.integral_map (orthoSphereAct g).continuous.measurable.aemeasurable
          (measurable_const.indicator hs (f := fun _ => (1 : ℝ))).aestronglyMeasurable (μ := ν)
        rw [hν g] at hm
        calc ∫ x : S, f g x ∂ν
            = ∫ y : S, s.indicator (fun _ => (1 : ℝ)) y ∂ν := by simpa [f] using hm.symm
          _ = ν.real s := by
                rw [integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one]
      have hμGuniv : μG.real Set.univ = 1 := by simp [measureReal_def, measure_univ]
      simp_rw [hInner, integral_const, hμGuniv, smul_eq_mul, one_mul]
    have hRHS : ∫ x : S, ∫ g : OGroup n, f g x ∂μG ∂ν =
        μG.real {g : OGroup n | orthoSphereAct g e₀ ∈ s} * ν.real Set.univ := by
      let A : Set (OGroup n) := {g : OGroup n | orthoSphereAct g e₀ ∈ s}
      have hcont0 : Continuous (fun g : OGroup n => orthoSphereAct g e₀) :=
        continuous_orthoSphereAct_uncurry.comp (continuous_id.prodMk continuous_const)
      have hAm : MeasurableSet A := by
        change MeasurableSet ((fun g : OGroup n => orthoSphereAct g e₀) ⁻¹' s)
        exact hcont0.measurable hs
      have hInner : ∀ x : S, ∫ g : OGroup n, f g x ∂μG = μG.real A := by
        intro x
        obtain ⟨hx, hhx⟩ := oGroup_transitive_sphere e₀ x
        have hcomp : ∀ g : OGroup n, f g x = A.indicator (fun _ => (1 : ℝ)) (g * hx) := by
          intro g
          have hact : orthoSphereAct g x = orthoSphereAct (g * hx) e₀ := by
            apply Subtype.ext
            calc (orthoSphereAct g x).1 = orthoEquiv g x.1 := rfl
              _ = orthoEquiv g (orthoEquiv hx e₀.1) := by rw [← hhx]; rfl
              _ = orthoEquiv (g * hx) e₀.1 := (orthoEquiv_mul g hx e₀.1).symm
          by_cases hmem : orthoSphereAct (g * hx) e₀ ∈ s <;> simp [f, A, hact, hmem]
        simp_rw [hcomp]
        rw [integral_mul_right_eq_self (μ := μG) (fun g => A.indicator (fun _ => (1 : ℝ)) g) hx,
          integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_one]
      simp_rw [hInner, integral_const, smul_eq_mul, mul_comm (ν.real Set.univ)]
      rfl
    rw [← hLHS, MeasureTheory.integral_integral_swap hfInt, hRHS]
  ext s hs
  have k1 := key ν₁ h₁ hs
  have k2 := key ν₂ h₂ hs
  have hreal : ν₁.real Set.univ * ν₂.real s = ν₂.real Set.univ * ν₁.real s := by
    rw [k1, k2]
    ring
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ← ENNReal.ofReal_toReal (measure_ne_top ν₂ s),
    ← ENNReal.ofReal_toReal (measure_ne_top ν₁ s),
    ← measureReal_def, ← measureReal_def,
    ← ENNReal.ofReal_mul measureReal_nonneg,
    ← ENNReal.ofReal_mul measureReal_nonneg, hreal]

end OrthogonalGroupHaar

section HausdorffVsToSphere

private theorem hausdorffMeasure_unitSphere_pos {d : ℕ} (hd : 1 ≤ d) :
    (0 : ℝ≥0∞) < (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1)))
      (Metric.sphere (0 : E (d + 1)) 1) := by
  let proj : E (d + 1) → E d := fun x => WithLp.toLp 2 fun i : Fin d => x i.succ
  have hLip : LipschitzWith 1 proj := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L2, PiLp.dist_eq_of_L2]
    refine Real.sqrt_le_sqrt ?_
    have hsum := Fin.sum_univ_succ (f := fun j : Fin (d + 1) => dist (x j) (y j) ^ 2)
    linarith [sq_nonneg (dist (x 0) (y 0))]
  have hBallSub : Metric.ball (0 : E d) (1 / 2) ⊆ proj '' Metric.sphere (0 : E (d + 1)) 1 := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right] at hu
    have hu2 : ‖u‖ ^ 2 < 1 / 4 := by
      have : ‖u‖ ^ 2 < (1 / 2 : ℝ) ^ 2 := sq_lt_sq' (by linarith [norm_nonneg u]) hu
      linarith
    have hnonneg : 0 ≤ 1 - ‖u‖ ^ 2 := by linarith
    let x : E (d + 1) := WithLp.toLp 2 (Fin.cons (Real.sqrt (1 - ‖u‖ ^ 2)) u.ofLp)
    refine ⟨x, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right,
        ← pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero, ← real_inner_self_eq_norm_sq]
      simp only [x, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, WithLp.ofLp_toLp,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have huSq : ∑ i : Fin d, u.ofLp i * u.ofLp i = ‖u‖ ^ 2 := by
        have h : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
        rw [PiLp.inner_apply] at h
        simpa only [RCLike.inner_apply, conj_trivial] using h
      rw [Real.mul_self_sqrt hnonneg, huSq]
      ring
    · ext i
      simp [proj, x]
  haveI : (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)).IsAddHaarMeasure := by
    have hfr : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin
    convert (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := E d)) using 2
    exact congrArg (Nat.cast : ℕ → ℝ) hfr.symm
  have hBallPos : (0 : ℝ≥0∞) < (Measure.hausdorffMeasure (d : ℝ) : Measure (E d))
      (Metric.ball (0 : E d) (1 / 2)) :=
    Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr (by norm_num))
  have hImgLe := hLip.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ (d : ℝ))
    (Metric.sphere (0 : E (d + 1)) 1)
  rw [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hImgLe
  exact lt_of_lt_of_le (lt_of_lt_of_le hBallPos (measure_mono hBallSub)) hImgLe

private theorem hausdorffMeasure_unitSphere_lt_top {d : ℕ} (hd : 1 ≤ d) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1)))
      (Metric.sphere (0 : E (d + 1)) 1) < ⊤ := by
  let c : ℝ := 1 / Real.sqrt ((d : ℝ) + 1)
  have hcPos : 0 < c := by positivity
  let cap (k : Fin (d + 1)) (pos : Bool) : Set (E (d + 1)) :=
    {x ∈ Metric.sphere (0 : E (d + 1)) 1 | (if pos then (1 : ℝ) else -1) * x k ≥ c}
  have hCover : Metric.sphere (0 : E (d + 1)) 1 ⊆ ⋃ k : Fin (d + 1), ⋃ b : Bool, cap k b := by
    intro x hx
    have hxNorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
    have hsum : ∑ k : Fin (d + 1), x k ^ 2 = 1 := by
      have h : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hxNorm, one_pow]
      rw [PiLp.inner_apply] at h
      simpa only [RCLike.inner_apply, conj_trivial, sq] using h
    by_contra hnone
    have hlt : ∀ k : Fin (d + 1), |x k| < c := by
      intro k
      have hp : ¬ (x k ≥ c) := fun h =>
        hnone (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨true, ⟨hx, by simpa using h⟩⟩⟩)
      have hm : ¬ (-x k ≥ c) := fun h =>
        hnone (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨false, ⟨hx, by simpa using h⟩⟩⟩)
      rw [not_le] at hp hm
      exact abs_lt.mpr ⟨by linarith, hp⟩
    have hcsq : c ^ 2 = 1 / ((d : ℝ) + 1) := by
      simp [c, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]
    have hsq : ∀ k : Fin (d + 1), x k ^ 2 < 1 / ((d : ℝ) + 1) := by
      intro k
      have hk := sq_lt_sq' (by linarith [abs_nonneg (x k), hlt k]) (hlt k)
      simpa [sq_abs, hcsq] using hk
    have hSumLt : ∑ k : Fin (d + 1), x k ^ 2 < ∑ _k : Fin (d + 1), (1 : ℝ) / ((d : ℝ) + 1) :=
      Finset.sum_lt_sum (fun k _ => (hsq k).le) ⟨0, Finset.mem_univ _, hsq 0⟩
    have hEq1 : ∑ _k : Fin (d + 1), (1 : ℝ) / ((d : ℝ) + 1) = 1 := by
      simp [Finset.sum_const, Finset.card_univ]
      field_simp
    linarith
  have hCap0Fin : (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) (cap 0 true) < ⊤ := by
    let r : ℝ := Real.sqrt (1 - 1 / ((d : ℝ) + 1))
    let B : Set (E d) := Metric.closedBall 0 r
    let lift : E d → E (d + 1) := fun u =>
      WithLp.toLp 2 (Fin.cons (Real.sqrt (1 - ‖u‖ ^ 2)) u.ofLp)
    have hSub : cap 0 true ⊆ lift '' B := by
      intro x hx
      rcases hx with ⟨hxS, hx0⟩
      have hxNorm1 : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hxS
      simp only [ite_true, one_mul, ge_iff_le] at hx0
      let u : E d := WithLp.toLp 2 fun i : Fin d => x i.succ
      have hxNorm : ∑ j : Fin (d + 1), x j ^ 2 = 1 := by
        have h : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hxNorm1, one_pow]
        rw [PiLp.inner_apply] at h
        simpa only [RCLike.inner_apply, conj_trivial, sq] using h
      have huNormSq : ‖u‖ ^ 2 = 1 - x 0 ^ 2 := by
        have h : ∑ i : Fin d, u.ofLp i * u.ofLp i = ‖u‖ ^ 2 := by
          have h0 := real_inner_self_eq_norm_sq u
          rw [PiLp.inner_apply] at h0
          simpa only [RCLike.inner_apply, conj_trivial] using h0
        simp only [u, WithLp.ofLp_toLp] at h
        rw [Fin.sum_univ_succ] at hxNorm
        have hsq : ∑ i : Fin d, x i.succ * x i.succ = ∑ i : Fin d, x i.succ ^ 2 :=
          Finset.sum_congr rfl fun i _ => by ring
        linarith
      have hx0Sq : 1 / ((d : ℝ) + 1) ≤ x 0 ^ 2 := by
        have hcsq : c ^ 2 = 1 / ((d : ℝ) + 1) := by
          simp [c, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]
        rw [← hcsq]
        nlinarith [hx0, hcPos]
      have huB : u ∈ B := by
        rw [Metric.mem_closedBall, dist_zero_right]
        rw [← Real.sqrt_sq (norm_nonneg u)]
        exact Real.sqrt_le_sqrt (by linarith)
      refine ⟨u, huB, ?_⟩
      ext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [lift, WithLp.ofLp_toLp, Fin.cons_zero, huNormSq]
        have hsq : 1 - (1 - x 0 ^ 2) = x 0 ^ 2 := by ring
        rw [hsq, Real.sqrt_sq (le_trans hcPos.le hx0)]
      · simp [lift, u]
    have hrSq : r ^ 2 = 1 - 1 / ((d : ℝ) + 1) := by
      refine Real.sq_sqrt ?_
      have hd1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith
      rw [sub_nonneg, div_le_one (by positivity)]
      exact hd1
    have hLip : ∃ K : ℝ≥0, LipschitzOnWith K lift B := by
      let L : ℝ := Real.sqrt (1 + ((d : ℝ) + 1))
      refine ⟨⟨L, Real.sqrt_nonneg _⟩, LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hu hv
      have hu2 : ‖u‖ ^ 2 ≤ 1 - 1 / ((d : ℝ) + 1) := by
        have := sq_le_sq' (by linarith [norm_nonneg u, Real.sqrt_nonneg (1 - 1 / ((d : ℝ) + 1))]) hu
        simpa [hrSq] using this
      have hv2 : ‖v‖ ^ 2 ≤ 1 - 1 / ((d : ℝ) + 1) := by
        have := sq_le_sq' (by linarith [norm_nonneg v, Real.sqrt_nonneg (1 - 1 / ((d : ℝ) + 1))]) hv
        simpa [hrSq] using this
      have hInvPos : (0 : ℝ) < 1 / ((d : ℝ) + 1) := by positivity
      have hau : 1 / ((d : ℝ) + 1) ≤ 1 - ‖u‖ ^ 2 := by linarith
      have hav : 1 / ((d : ℝ) + 1) ≤ 1 - ‖v‖ ^ 2 := by linarith
      have huSqLe1 : ‖u‖ ^ 2 ≤ 1 := by linarith
      have hvSqLe1 : ‖v‖ ^ 2 ≤ 1 := by linarith
      have hu1 : ‖u‖ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg u)).mp huSqLe1
      have hv1 : ‖v‖ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg v)).mp hvSqLe1
      have hsqDiff : |Real.sqrt (1 - ‖u‖ ^ 2) - Real.sqrt (1 - ‖v‖ ^ 2)| ≤
          Real.sqrt ((d : ℝ) + 1) * dist u v := by
        set a := 1 - ‖u‖ ^ 2
        set b := 1 - ‖v‖ ^ 2
        have hsqa : 1 / Real.sqrt ((d : ℝ) + 1) ≤ Real.sqrt a := by
          have h := Real.sqrt_le_sqrt hau
          rwa [Real.sqrt_div zero_le_one, Real.sqrt_one] at h
        have hsqb : 1 / Real.sqrt ((d : ℝ) + 1) ≤ Real.sqrt b := by
          have h := Real.sqrt_le_sqrt hav
          rwa [Real.sqrt_div zero_le_one, Real.sqrt_one] at h
        have hsumGe : 2 / Real.sqrt ((d : ℝ) + 1) ≤ Real.sqrt a + Real.sqrt b :=
          (add_le_add hsqa hsqb).trans_eq' (by ring)
        have hdenPos : (0 : ℝ) < 2 / Real.sqrt ((d : ℝ) + 1) := by positivity
        have hsumPos : 0 < Real.sqrt a + Real.sqrt b := lt_of_lt_of_le hdenPos hsumGe
        have hmul : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
          rw [mul_comm, ← sq_sub_sq, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
        have habs : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
          rw [← abs_of_pos hsumPos, ← abs_mul, hmul]
        have habsDiff : |a - b| ≤ 2 * dist u v := by
          have h1 : a - b = (‖v‖ - ‖u‖) * (‖v‖ + ‖u‖) := by dsimp [a, b]; ring
          rw [h1, abs_mul]
          have h2 : |‖v‖ - ‖u‖| ≤ dist u v := by
            rw [dist_comm u v, dist_eq_norm]; exact abs_norm_sub_norm_le v u
          have h3 : |‖v‖ + ‖u‖| ≤ 2 := by
            rw [abs_of_nonneg (add_nonneg (norm_nonneg v) (norm_nonneg u))]
            linarith
          have h2nn : 0 ≤ |‖v‖ - ‖u‖| := abs_nonneg _
          have h3nn : 0 ≤ |‖v‖ + ‖u‖| := abs_nonneg _
          nlinarith [show (0 : ℝ) ≤ dist u v from dist_nonneg]
        calc |Real.sqrt a - Real.sqrt b|
            = |a - b| / (Real.sqrt a + Real.sqrt b) := by
                rw [eq_div_iff hsumPos.ne', habs]
          _ ≤ (2 * dist u v) / (2 / Real.sqrt ((d : ℝ) + 1)) := by
                exact div_le_div₀ (by positivity) habsDiff hdenPos hsumGe
          _ = Real.sqrt ((d : ℝ) + 1) * dist u v := by field_simp
      rw [PiLp.dist_eq_of_L2 (lift u) (lift v)]
      simp only [lift, WithLp.ofLp_toLp, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hdist2 : ∑ i : Fin d, dist (u.ofLp i) (v.ofLp i) ^ 2 = dist u v ^ 2 := by
        rw [PiLp.dist_eq_of_L2 u v, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      have hBound : dist (Real.sqrt (1 - ‖u‖ ^ 2)) (Real.sqrt (1 - ‖v‖ ^ 2)) ^ 2 +
          ∑ i : Fin d, dist (u.ofLp i) (v.ofLp i) ^ 2 ≤
          (1 + ((d : ℝ) + 1)) * dist u v ^ 2 := by
        rw [Real.dist_eq, hdist2]
        have hdn : 0 ≤ dist u v := dist_nonneg
        have hsq' : |Real.sqrt (1 - ‖u‖ ^ 2) - Real.sqrt (1 - ‖v‖ ^ 2)| ^ 2 ≤
            ((d : ℝ) + 1) * dist u v ^ 2 := by
          have hneg : -(Real.sqrt ((d : ℝ) + 1) * dist u v) ≤
              |Real.sqrt (1 - ‖u‖ ^ 2) - Real.sqrt (1 - ‖v‖ ^ 2)| :=
            (neg_nonpos.mpr (mul_nonneg (Real.sqrt_nonneg _) hdn)).trans (abs_nonneg _)
          have := sq_le_sq' hneg hsqDiff
          simpa [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)] using this
        linarith
      calc Real.sqrt (dist (Real.sqrt (1 - ‖u‖ ^ 2)) (Real.sqrt (1 - ‖v‖ ^ 2)) ^ 2 +
              ∑ i : Fin d, dist (u.ofLp i) (v.ofLp i) ^ 2)
          ≤ Real.sqrt ((1 + ((d : ℝ) + 1)) * dist u v ^ 2) := Real.sqrt_le_sqrt hBound
        _ = L * dist u v := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]
        _ = (⟨L, Real.sqrt_nonneg _⟩ : ℝ≥0) * dist u v := rfl
    rcases hLip with ⟨K, hLipK⟩
    haveI : (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)).IsAddHaarMeasure := by
      have hfr : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin
      convert (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := E d)) using 2
      exact congrArg (Nat.cast : ℕ → ℝ) hfr.symm
    have hBFin : (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) B < ⊤ :=
      (isCompact_closedBall (0 : E d) r).measure_lt_top
    have hImgFin := hLipK.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ (d : ℝ))
    have hMulFin : (K : ℝ≥0∞) ^ (d : ℝ) * (Measure.hausdorffMeasure (d : ℝ) : Measure (E d)) B < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) hBFin
    exact lt_of_le_of_lt (measure_mono hSub) (lt_of_le_of_lt hImgFin hMulFin)
  have hCapEq : ∀ k : Fin (d + 1), ∀ b : Bool,
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) (cap k b) =
        (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) (cap 0 true) := by
    intro k b
    let ePerm : E (d + 1) ≃ₗᵢ[ℝ] E (d + 1) :=
      { toFun := fun x => WithLp.toLp 2 fun j =>
          (if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j)
        invFun := fun y => WithLp.toLp 2 fun j =>
          (if Equiv.swap 0 k j = k then (if b then (1 : ℝ) else -1) else 1) * y (Equiv.swap 0 k j)
        map_add' := fun x y => by
          ext j
          change (if j = k then (if b then (1 : ℝ) else -1) else 1) *
              (x (Equiv.swap 0 k j) + y (Equiv.swap 0 k j)) =
            (if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j) +
            (if j = k then (if b then (1 : ℝ) else -1) else 1) * y (Equiv.swap 0 k j)
          ring
        map_smul' := fun r x => by
          ext j
          change (if j = k then (if b then (1 : ℝ) else -1) else 1) *
              (r * x (Equiv.swap 0 k j)) =
            r * ((if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j))
          ring
        left_inv := fun x => by
          ext j
          change (if Equiv.swap 0 k j = k then (if b then (1 : ℝ) else -1) else 1) *
              ((if Equiv.swap 0 k j = k then (if b then (1 : ℝ) else -1) else 1) *
                x (Equiv.swap 0 k (Equiv.swap 0 k j))) = x j
          rw [Equiv.swap_apply_self]
          by_cases h : Equiv.swap 0 k j = k
          · cases b <;> simp [h]
          · simp [h]
        right_inv := fun y => by
          ext j
          change (if j = k then (if b then (1 : ℝ) else -1) else 1) *
              ((if Equiv.swap 0 k (Equiv.swap 0 k j) = k then (if b then (1 : ℝ) else -1) else 1) *
                y (Equiv.swap 0 k (Equiv.swap 0 k j))) = y j
          rw [Equiv.swap_apply_self]
          by_cases h : j = k
          · cases b <;> simp [h]
          · simp [h]
        norm_map' := fun x => by
          rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
            ← real_inner_self_eq_norm_sq, PiLp.inner_apply, PiLp.inner_apply]
          simp only [RCLike.inner_apply, conj_trivial]
          change ∑ j : Fin (d + 1),
              ((if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j)) *
                ((if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j)) =
            ∑ j : Fin (d + 1), x j * x j
          have hterm : ∀ j : Fin (d + 1),
              ((if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j)) *
                ((if j = k then (if b then (1 : ℝ) else -1) else 1) * x (Equiv.swap 0 k j)) =
              x (Equiv.swap 0 k j) * x (Equiv.swap 0 k j) := fun j => by
            by_cases h : j = k <;> cases b <;> simp [h]
          simp_rw [hterm]
          exact Equiv.sum_comp (Equiv.swap 0 k) fun j => x j * x j }
    have himg : ePerm '' cap 0 true = cap k b := by
      ext y
      simp only [Set.mem_image, cap, Set.mem_sep_iff, Metric.mem_sphere, dist_zero_right]
      constructor
      · rintro ⟨x, ⟨hx1, hx0⟩, rfl⟩
        refine ⟨by simpa using hx1, ?_⟩
        have h0 : ePerm x k = (if b then (1 : ℝ) else -1) * x 0 := by simp [ePerm]
        rw [h0]
        cases b <;> simpa [mul_assoc] using hx0
      · intro ⟨hy1, hyk⟩
        refine ⟨ePerm.symm y, ⟨by simpa using hy1, ?_⟩, ePerm.apply_symm_apply y⟩
        have h0 : (ePerm.symm y) 0 = (if b then (1 : ℝ) else -1) * y k := by
          change (if Equiv.swap 0 k 0 = k then (if b then (1 : ℝ) else -1) else 1) *
            y (Equiv.swap 0 k 0) = _
          simp
        rw [h0]
        simpa using hyk
    rw [← himg]
    exact ePerm.toIsometryEquiv.hausdorffMeasure_image (d : ℝ) (cap 0 true)
  refine lt_of_le_of_lt (measure_mono hCover) ?_
  calc (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1)))
        (⋃ k : Fin (d + 1), ⋃ b : Bool, cap k b)
      ≤ ∑ k : Fin (d + 1), (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1)))
          (⋃ b : Bool, cap k b) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ k : Fin (d + 1), ∑ b : Bool,
          (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) (cap k b) :=
        Finset.sum_le_sum fun k _ => measure_iUnion_fintype_le _ _
    _ = ∑ _k : Fin (d + 1), ∑ _b : Bool,
          (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) (cap 0 true) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => hCapEq k b
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.sum_lt_top.mpr fun _ _ => hCap0Fin

/-- Unnormalized `d`-Hausdorff measure pulled back to `Metric.sphere (0 : E (d + 1)) 1`. -/
def sphereHausdorff (d : ℕ) : Measure (Metric.sphere (0 : E (d + 1)) 1) :=
  Measure.comap Subtype.val (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1)))

theorem sphereHausdorff_apply (d : ℕ) {s : Set (Metric.sphere (0 : E (d + 1)) 1)}
    (hs : MeasurableSet s) :
    sphereHausdorff d s =
      (Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) (Subtype.val '' s) := by
  have hemb : MeasurableEmbedding (Subtype.val : Metric.sphere (0 : E (d + 1)) 1 → E (d + 1)) :=
    MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet
  exact Measure.comap_apply Subtype.val Subtype.val_injective
    (fun t ht => hemb.measurableSet_image.mpr ht) _ hs

instance instIsFiniteMeasure_sphereHausdorff (d : ℕ) [Fact (1 ≤ d)] :
    IsFiniteMeasure (sphereHausdorff d) := by
  refine ⟨?_⟩
  rw [sphereHausdorff_apply d MeasurableSet.univ, Set.image_univ, Subtype.range_coe_subtype]
  exact hausdorffMeasure_unitSphere_lt_top Fact.out

theorem sphereHausdorff_real_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < (sphereHausdorff d).real Set.univ := by
  have hPos := hausdorffMeasure_unitSphere_pos hd
  have hFin := hausdorffMeasure_unitSphere_lt_top hd
  rw [measureReal_def, sphereHausdorff_apply d MeasurableSet.univ, Set.image_univ,
    Subtype.range_coe_subtype]
  exact ENNReal.toReal_pos hPos.ne' hFin.ne

theorem toSphere_real_univ_pos (n : ℕ) [NeZero n] :
    0 < ((MeasureTheory.volume : Measure (E n)).toSphere).real Set.univ := by
  rw [Measure.toSphere_real_apply_univ]
  have hdim : (0 : ℝ) < Module.finrank ℝ (E n) := by
    rw [finrank_euclideanSpace_fin]
    exact Nat.cast_pos.mpr (NeZero.pos n)
  have hball : 0 < (MeasureTheory.volume : Measure (E n)).real (Metric.ball 0 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos
      (Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr zero_lt_one)).ne'
      (MeasureTheory.measure_ball_lt_top).ne
  exact mul_pos hdim hball

@[simp]
theorem orthoSphereAct_apply_inv {n : ℕ} (g : OGroup n) (y : Metric.sphere (0 : E n) 1) :
    orthoSphereAct g (orthoSphereAct g⁻¹ y) = y := by
  apply Subtype.ext
  change orthoEquiv g (orthoEquiv g⁻¹ y.1) = y.1
  rw [← orthoEquiv_mul, mul_inv_cancel, orthoEquiv_one]

@[simp]
theorem orthoSphereAct_inv_apply {n : ℕ} (g : OGroup n) (y : Metric.sphere (0 : E n) 1) :
    orthoSphereAct g⁻¹ (orthoSphereAct g y) = y := by
  apply Subtype.ext
  change orthoEquiv g⁻¹ (orthoEquiv g y.1) = y.1
  rw [← orthoEquiv_mul, inv_mul_cancel, orthoEquiv_one]

theorem sphereHausdorff_oGroup_invariant (d : ℕ) (g : OGroup (d + 1)) :
    Measure.map (orthoSphereAct g) (sphereHausdorff d) = sphereHausdorff d := by
  ext s hs
  have hs' : MeasurableSet (orthoSphereAct g ⁻¹' s) := (orthoSphereAct g).continuous.measurable hs
  rw [Measure.map_apply (orthoSphereAct g).continuous.measurable hs,
    sphereHausdorff_apply d hs', sphereHausdorff_apply d hs]
  have himg : Subtype.val '' (orthoSphereAct g ⁻¹' s) =
      (orthoEquiv g).symm '' (Subtype.val '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(orthoSphereAct g y).1, ⟨orthoSphereAct g y, hy, rfl⟩, ?_⟩
      rw [orthoSphereAct_val]
      exact (orthoEquiv g).symm_apply_apply y.1
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨orthoSphereAct g⁻¹ w, by simpa [orthoSphereAct_apply_inv] using hw, ?_⟩
      change (orthoEquiv g⁻¹ w.1) = (orthoEquiv g).symm w.1
      change mulVecE (g⁻¹).1 w.1 = mulVecE (g⁻¹).1 w.1
      rfl
  rw [himg]
  exact (orthoEquiv g).symm.toIsometryEquiv.hausdorffMeasure_image (d : ℝ) (Subtype.val '' s)

private theorem measurableSet_Ioo_smul_sphere {n : ℕ}
    {s : Set (Metric.sphere (0 : E n) 1)} (hs : MeasurableSet s) :
    MeasurableSet (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨e₀, _⟩
  · simp
  · let f : E n → E n := fun x => if x = 0 then e₀.1 else ‖x‖⁻¹ • x
    have hfMem : ∀ x : E n, f x ∈ Metric.sphere (0 : E n) 1 := by
      intro x
      by_cases hx : x = 0
      · simpa [f, hx] using e₀.2
      · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
        simp [f, hx, Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
          inv_mul_cancel₀ hnx]
    let uProj : E n → Metric.sphere (0 : E n) 1 := fun x => ⟨f x, hfMem x⟩
    have hfMeas : Measurable f :=
      Measurable.ite (measurableSet_singleton 0) measurable_const
        (continuous_norm.measurable.inv.smul measurable_id)
    have huMeas : Measurable uProj := hfMeas.subtype_mk
    have hEq : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) =
        (Metric.ball (0 : E n) 1 \ {0}) ∩ (uProj ⁻¹' s) := by
      ext x
      constructor
      · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
        have hz1 : ‖z.1‖ = 1 := by simpa using z.2
        have hrxPos : 0 < ‖r • z.1‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hz1, mul_one]
          exact hr.1
        have hrxNe : r • z.1 ≠ 0 := norm_pos_iff.mp hrxPos
        have hnorm : ‖r • z.1‖ = r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hz1, mul_one]
        have huEq : uProj (r • z.1) = z := by
          apply Subtype.ext
          simp only [uProj, f, hrxNe, ↓reduceIte, hnorm, smul_smul, inv_mul_cancel₀ hr.1.ne',
            one_smul]
        refine ⟨⟨?_, hrxNe⟩, ?_⟩
        · simpa [Metric.mem_ball, dist_zero_right, hnorm] using hr.2
        · simpa [huEq] using hz
      · rintro ⟨⟨hxBall, hx0⟩, hxs⟩
        have hxNe : x ≠ 0 := hx0
        have hnxPos : 0 < ‖x‖ := norm_pos_iff.mpr hxNe
        have hnxLt : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hxBall
        refine ⟨‖x‖, ⟨hnxPos, hnxLt⟩, (uProj x).1, ⟨uProj x, hxs, rfl⟩, ?_⟩
        simp [uProj, f, hxNe, smul_smul, mul_inv_cancel₀ hnxPos.ne']
    rw [hEq]
    exact (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0)).inter (huMeas hs)

theorem toSphere_oGroup_invariant (n : ℕ) (g : OGroup n) :
    Measure.map (orthoSphereAct g) ((MeasureTheory.volume : Measure (E n)).toSphere) =
      (MeasureTheory.volume : Measure (E n)).toSphere := by
  ext s hs
  have hs' : MeasurableSet (orthoSphereAct g ⁻¹' s) := (orthoSphereAct g).continuous.measurable hs
  rw [Measure.map_apply (orthoSphereAct g).continuous.measurable hs,
    Measure.toSphere_apply' (MeasureTheory.volume : Measure (E n)) hs',
    Measure.toSphere_apply' (MeasureTheory.volume : Measure (E n)) hs]
  congr 1
  have himg : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (orthoSphereAct g ⁻¹' s)) =
      (orthoEquiv g) ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨r, hr, (orthoSphereAct g z).1, ⟨orthoSphereAct g z, hz, rfl⟩, ?_⟩
      simp [orthoSphereAct, map_smul]
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hx⟩
      refine ⟨r, hr, (orthoSphereAct g⁻¹ z).1,
        ⟨orthoSphereAct g⁻¹ z, by simpa [orthoSphereAct_apply_inv] using hz, rfl⟩, ?_⟩
      change r • (orthoEquiv g⁻¹ z.1) = x
      have hx' : r • z.1 = orthoEquiv g x := hx
      calc r • orthoEquiv g⁻¹ z.1
          = (orthoEquiv g).symm (r • z.1) := by
              rw [map_smul]; rfl
        _ = (orthoEquiv g).symm (orthoEquiv g x) := by rw [hx']
        _ = x := (orthoEquiv g).symm_apply_apply x
  rw [himg, ← Measure.map_apply (orthoEquiv g).continuous.measurable (measurableSet_Ioo_smul_sphere hs),
    ((orthoEquiv g).measurePreserving).map_eq]

/-- Scale factor `κ d > 0` relating `μH[d]` on `S^d ⊂ ℝ^{d+1}` to `volume.toSphere`. -/
def sphereScale (d : ℕ) : ℝ :=
  (sphereHausdorff d).real Set.univ /
    ((MeasureTheory.volume : Measure (E (d + 1))).toSphere).real Set.univ

theorem sphereScale_pos {d : ℕ} (hd : 1 ≤ d) : 0 < sphereScale d :=
  div_pos (sphereHausdorff_real_pos d hd) (toSphere_real_univ_pos (d + 1))

theorem sphereHausdorff_real_eq_scale_mul_toSphere {d : ℕ} (hd : 1 ≤ d)
    {s : Set (Metric.sphere (0 : E (d + 1)) 1)} (hs : MeasurableSet s) :
    (sphereHausdorff d).real s =
      sphereScale d * ((MeasureTheory.volume : Measure (E (d + 1))).toSphere).real s := by
  haveI : Fact (1 ≤ d) := ⟨hd⟩
  have heq := ortho_invariant_sphere_measure_eq (sphereHausdorff d)
    ((MeasureTheory.volume : Measure (E (d + 1))).toSphere)
    (sphereHausdorff_oGroup_invariant d) (toSphere_oGroup_invariant (d + 1))
  have hsEq := congrArg (fun μ : Measure (Metric.sphere (0 : E (d + 1)) 1) => μ.real s) heq
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul] at hsEq
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg] at hsEq
  have h1 : (((MeasureTheory.volume : Measure (E (d + 1))).toSphere).real Set.univ : ℝ) ≠ 0 :=
    (toSphere_real_univ_pos (d + 1)).ne'
  dsimp [sphereScale]
  field_simp [h1]
  simp only [measureReal_def]
  linarith [hsEq]

theorem hausdorffMeasure_real_eq_scale_mul_toSphere {d : ℕ} (hd : 1 ≤ d)
    {B : Set (E (d + 1))} (hBSub : B ⊆ Metric.sphere (0 : E (d + 1)) 1)
    (hBMeas : MeasurableSet B) :
    ((Measure.hausdorffMeasure (d : ℝ) : Measure (E (d + 1))) B).toReal =
      sphereScale d *
        ((MeasureTheory.volume : Measure (E (d + 1))).toSphere).real (Subtype.val ⁻¹' B) := by
  have hs : MeasurableSet (Subtype.val ⁻¹' B : Set (Metric.sphere (0 : E (d + 1)) 1)) :=
    hBMeas.preimage measurable_subtype_coe
  have h := sphereHausdorff_real_eq_scale_mul_toSphere hd hs
  have himg : Subtype.val '' (Subtype.val ⁻¹' B : Set (Metric.sphere (0 : E (d + 1)) 1)) = B := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Subtype.exists]
    exact ⟨fun ⟨y, _, hyB, hxy⟩ => hxy ▸ hyB, fun hx => ⟨x, hBSub hx, hx, rfl⟩⟩
  rw [measureReal_def, sphereHausdorff_apply d hs, himg] at h
  exact h

/-- `T.volume` in terms of `(MeasureTheory.volume : Measure E4).toSphere` and `sphereScale 3`. -/
theorem volume_eq_sphereScale_mul_toSphere (T : SphericalTetrahedron) :
    T.volume =
      sphereScale 3 * ((MeasureTheory.volume : Measure E4).toSphere).real (Subtype.val ⁻¹' T.body) := by
  have hSub : T.body ⊆ Metric.sphere (0 : E4) 1 := fun x hx => by
    simpa [Metric.mem_sphere, dist_zero_right] using hx.1
  have hClosed : IsClosed T.body := by
    have h1 : IsClosed {x : E4 | ‖x‖ = 1} := isClosed_eq continuous_norm continuous_const
    have h2 : IsClosed {x : E4 | ∀ i : Fin 4, 0 ≤ ⟪T.normal i, x⟫_ℝ} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun i =>
        isClosed_le continuous_const (continuous_const.inner continuous_id)
    exact h1.inter h2
  exact hausdorffMeasure_real_eq_scale_mul_toSphere (by norm_num) hSub hClosed.measurableSet

/-- Lebesgue ball-cone formula for `SphericalTetrahedron.measure 3 B` (`B ⊆ S³`). -/
theorem measure_three_eq_four_sphereScale_mul_ballCone
    {B : Set E4} (hBSub : B ⊆ Metric.sphere (0 : E4) 1) (hBMeas : MeasurableSet B) :
    SphericalTetrahedron.measure 3 B =
      (4 * sphereScale 3) * (MeasureTheory.volume : Measure E4).real (Set.Ioo (0 : ℝ) 1 • B) := by
  have hs : MeasurableSet (Subtype.val ⁻¹' B : Set (Metric.sphere (0 : E4) 1)) :=
    hBMeas.preimage measurable_subtype_coe
  have h := hausdorffMeasure_real_eq_scale_mul_toSphere (d := 3) (by norm_num) hBSub hBMeas
  have himg : Subtype.val '' (Subtype.val ⁻¹' B : Set (Metric.sphere (0 : E4) 1)) = B := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Subtype.exists]
    exact ⟨fun ⟨y, _, hyB, hxy⟩ => hxy ▸ hyB, fun hx => ⟨x, hBSub hx, hx, rfl⟩⟩
  have hSphere := Measure.toSphere_apply' (MeasureTheory.volume : Measure E4) hs
  rw [himg] at hSphere
  have hReal : ((MeasureTheory.volume : Measure E4).toSphere).real (Subtype.val ⁻¹' B) =
      4 * (MeasureTheory.volume : Measure E4).real (Set.Ioo (0 : ℝ) 1 • B) := by
    rw [measureReal_def, hSphere, finrank_euclideanSpace_fin]
    simp [measureReal_def]
  have h' : SphericalTetrahedron.measure 3 B =
      sphereScale 3 * ((MeasureTheory.volume : Measure E4).toSphere).real (Subtype.val ⁻¹' B) := by
    simpa [SphericalTetrahedron.measure] using h
  rw [h', hReal]
  ring

end HausdorffVsToSphere

section LuneAndGirard

theorem volume_toSphere_hyperplane_eq_zero {n : ℕ} {w : E n} (hw : w ≠ 0) :
    ((MeasureTheory.volume : Measure (E n)).toSphere)
      {y : Metric.sphere (0 : E n) 1 | ⟪w, y.1⟫_ℝ = 0} = 0 := by
  let H : Submodule ℝ (E n) :=
    { carrier := {x : E n | ⟪w, x⟫_ℝ = 0}
      add_mem' := fun hx hy => by dsimp at hx hy ⊢; simp [inner_add_right, hx, hy]
      zero_mem' := by simp
      smul_mem' := fun c _ hx => by dsimp at hx ⊢; simp [inner_smul_right, hx] }
  have hHne : H ≠ ⊤ := by
    intro htop
    have hwmem : w ∈ H := htop ▸ Submodule.mem_top
    have h0 : ⟪w, w⟫_ℝ = 0 := hwmem
    rw [real_inner_self_eq_norm_sq] at h0
    exact hw (norm_eq_zero.mp (sq_eq_zero_iff.mp h0))
  have hHm : MeasurableSet ({y : Metric.sphere (0 : E n) 1 | ⟪w, y.1⟫_ℝ = 0}) :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [Measure.toSphere_apply' (MeasureTheory.volume : Measure (E n)) hHm]
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Metric.sphere (0 : E n) 1 | ⟪w, y.1⟫_ℝ = 0})
      ⊆ (H : Set (E n)) := by
    rintro x ⟨r, _, y, ⟨z, hz0, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, H, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hz0 ⊢
    simp [inner_smul_right, hz0]
  have hVol0 : (MeasureTheory.volume : Measure (E n)) (H : Set (E n)) = 0 :=
    Measure.addHaar_submodule MeasureTheory.volume H hHne
  rw [measure_mono_null hsub hVol0, mul_zero]

/-- Rotation in the `(0, 1)` coordinate plane of `E3`. -/
def rotZ (α : ℝ) : OGroup 3 :=
  ⟨Matrix.of ![![Real.cos α, -Real.sin α, 0],
               ![Real.sin α, Real.cos α, 0],
               ![0, 0, 1]], by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
      nlinarith [Real.sin_sq_add_cos_sq α]⟩

theorem rotZ_apply (α : ℝ) (y : E3) :
    orthoEquiv (rotZ α) y =
      WithLp.toLp 2 ![Real.cos α * y 0 - Real.sin α * y 1,
                     Real.sin α * y 0 + Real.cos α * y 1,
                     y 2] := by
  ext i
  fin_cases i <;> simp [rotZ, mulVecE_apply, Fin.sum_univ_three] <;> ring

/-- Compact spherical wedge on `S² ⊂ E3` spanning azimuthal angle `[0, θ]`. -/
def sectorClosed (θ : ℝ) : Set (Metric.sphere (0 : E3) 1) :=
  {y | ∃ φ ∈ Set.Icc (0 : ℝ) θ, ∃ z ∈ Set.Icc (-1 : ℝ) 1,
    y.1 = WithLp.toLp 2 ![Real.sqrt (1 - z ^ 2) * Real.cos φ,
                          Real.sqrt (1 - z ^ 2) * Real.sin φ,
                          z]}

theorem sectorClosed_measurableSet (θ : ℝ) : MeasurableSet (sectorClosed θ) := by
  let f : ℝ × ℝ → E3 := fun p =>
    WithLp.toLp 2 ![Real.sqrt (1 - p.2 ^ 2) * Real.cos p.1,
                  Real.sqrt (1 - p.2 ^ 2) * Real.sin p.1,
                  p.2]
  have hfCont : Continuous f := by
    change Continuous (fun p : ℝ × ℝ =>
      WithLp.toLp 2 ![Real.sqrt (1 - p.2 ^ 2) * Real.cos p.1,
                    Real.sqrt (1 - p.2 ^ 2) * Real.sin p.1,
                    p.2])
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_snd.pow 2))).mul
        (Real.continuous_cos.comp continuous_fst))
    · exact ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_snd.pow 2))).mul
        (Real.continuous_sin.comp continuous_fst))
    · exact continuous_snd
  have hK : IsCompact (f '' (Set.Icc (0 : ℝ) θ ×ˢ Set.Icc (-1 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hfCont
  have hPre : sectorClosed θ = Subtype.val ⁻¹' (f '' (Set.Icc (0 : ℝ) θ ×ˢ Set.Icc (-1 : ℝ) 1)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image, sectorClosed, Set.mem_setOf_eq, Set.mem_prod]
    constructor
    · rintro ⟨φ, hφ, z, hz, hy⟩
      exact ⟨(φ, z), ⟨hφ, hz⟩, hy.symm⟩
    · rintro ⟨⟨φ, z⟩, ⟨hφ, hz⟩, hy⟩
      exact ⟨φ, hφ, z, hz, hy.symm⟩
  rw [hPre]
  exact (hK.isClosed.preimage continuous_subtype_val).measurableSet

theorem sectorClosed_mono {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) : sectorClosed θ₁ ⊆ sectorClosed θ₂ := by
  intro y ⟨φ, hφ, z, hz, hy⟩
  exact ⟨φ, ⟨hφ.1, hφ.2.trans h⟩, z, hz, hy⟩

theorem sectorClosed_two_pi : sectorClosed (2 * Real.pi) = Set.univ := by
  ext y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have hyNorm : ‖y.1‖ = 1 := by simpa using y.2
  have hsq : y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 = 1 := by
    have h : ⟪y.1, y.1⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hyNorm, one_pow]
    rw [PiLp.inner_apply] at h
    simpa only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, sq] using h
  have hz : y.1 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have : y.1 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y.1 0), sq_nonneg (y.1 1)]
    exact abs_le.mp ((sq_le_one_iff₀ (abs_nonneg _)).mp (by simpa [sq_abs] using this))
  set r := Real.sqrt (1 - y.1 2 ^ 2)
  have hrSq : r ^ 2 = y.1 0 ^ 2 + y.1 1 ^ 2 := by
    rw [Real.sq_sqrt (by linarith [hsq, sq_nonneg (y.1 0), sq_nonneg (y.1 1)])]
    linarith
  by_cases hr0 : r = 0
  · have hxy0 : y.1 0 = 0 ∧ y.1 1 = 0 := by
      have : y.1 0 ^ 2 + y.1 1 ^ 2 = 0 := by rw [← hrSq, hr0]; norm_num
      exact ⟨sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (y.1 1)]),
             sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (y.1 0)])⟩
    refine ⟨0, ⟨le_rfl, by positivity⟩, y.1 2, hz, ?_⟩
    have hr0' : Real.sqrt (1 - y.1 2 ^ 2) = 0 := hr0
    ext i
    fin_cases i <;> simp [hr0', hxy0.1, hxy0.2]
  · have hrPos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
    have hunit : (y.1 0 / r) ^ 2 + (y.1 1 / r) ^ 2 = 1 := by
      field_simp [hrPos.ne']
      linarith
    have hcosBnd : y.1 0 / r ∈ Set.Icc (-1 : ℝ) 1 := by
      have : (y.1 0 / r) ^ 2 ≤ 1 := by linarith [sq_nonneg (y.1 1 / r)]
      exact abs_le.mp ((sq_le_one_iff₀ (abs_nonneg _)).mp (by simpa [sq_abs] using this))
    by_cases hy1 : 0 ≤ y.1 1
    · let φ := Real.arccos (y.1 0 / r)
      refine ⟨φ, ⟨Real.arccos_nonneg _, le_trans (Real.arccos_le_pi _) (by linarith [Real.pi_pos])⟩,
        y.1 2, hz, ?_⟩
      have hcos : Real.cos φ = y.1 0 / r := Real.cos_arccos hcosBnd.1 hcosBnd.2
      have hsin : Real.sin φ = y.1 1 / r := by
        rw [Real.sin_arccos]
        have : 1 - (y.1 0 / r) ^ 2 = (y.1 1 / r) ^ 2 := by linarith
        rw [this, Real.sqrt_sq (div_nonneg hy1 hrPos.le)]
      ext i
      fin_cases i
      · simp [r, hcos, mul_div_cancel₀ _ hrPos.ne']
      · simp [r, hsin, mul_div_cancel₀ _ hrPos.ne']
      · rfl
    · let α := Real.arccos (y.1 0 / r)
      let φ := 2 * Real.pi - α
      have hαBnd : 0 ≤ α ∧ α ≤ Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      refine ⟨φ, ⟨by linarith, by linarith⟩, y.1 2, hz, ?_⟩
      have hcos : Real.cos φ = y.1 0 / r := by
        simp [φ, α, Real.cos_two_pi_sub, Real.cos_arccos hcosBnd.1 hcosBnd.2]
      have hsin : Real.sin φ = y.1 1 / r := by
        simp only [φ, Real.sin_two_pi_sub, α, Real.sin_arccos]
        have : 1 - (y.1 0 / r) ^ 2 = (y.1 1 / r) ^ 2 := by linarith
        rw [this, Real.sqrt_sq_eq_abs, abs_of_neg (div_neg_of_neg_of_pos (lt_of_not_ge hy1) hrPos)]
        ring
      ext i
      fin_cases i
      · simp [r, hcos, mul_div_cancel₀ _ hrPos.ne']
      · simp [r, hsin, mul_div_cancel₀ _ hrPos.ne']
      · rfl

private theorem rotZ_image_sectorClosed (α θ : ℝ) :
    orthoSphereAct (rotZ α) '' sectorClosed θ =
      {y : Metric.sphere (0 : E3) 1 |
        ∃ φ ∈ Set.Icc α (α + θ), ∃ z ∈ Set.Icc (-1 : ℝ) 1,
          y.1 = WithLp.toLp 2 ![Real.sqrt (1 - z ^ 2) * Real.cos φ,
                                Real.sqrt (1 - z ^ 2) * Real.sin φ,
                                z]} := by
  ext y
  simp only [Set.mem_image, sectorClosed, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨ψ, hψ, z, hz, hx⟩, rfl⟩
    refine ⟨α + ψ, ⟨by linarith [hψ.1], by linarith [hψ.2]⟩, z, hz, ?_⟩
    rw [orthoSphereAct_val, rotZ_apply, hx]
    ext i
    fin_cases i
    · simp [Real.cos_add]; ring
    · simp [Real.sin_add]; ring
    · simp
  · rintro ⟨φ, hφ, z, hz, hy⟩
    have hnorm : ‖WithLp.toLp 2 ![Real.sqrt (1 - z ^ 2) * Real.cos (φ - α),
        Real.sqrt (1 - z ^ 2) * Real.sin (φ - α), z]‖ = 1 := by
      rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq]
      have hz1 : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_three]
      nlinarith [Real.mul_self_sqrt hz1, Real.sin_sq_add_cos_sq (φ - α)]
    let x : Metric.sphere (0 : E3) 1 := ⟨_, by simpa [Metric.mem_sphere, dist_zero_right] using hnorm⟩
    refine ⟨x, ⟨φ - α, ⟨by linarith [hφ.1], by linarith [hφ.2]⟩, z, hz, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [orthoSphereAct_val, rotZ_apply, hy]
    ext i
    fin_cases i
    · have hc : Real.cos φ = Real.cos α * Real.cos (φ - α) - Real.sin α * Real.sin (φ - α) := by
        simpa [add_sub_cancel] using Real.cos_add α (φ - α)
      simp [x, hc]; ring
    · have hs : Real.sin φ = Real.sin α * Real.cos (φ - α) + Real.cos α * Real.sin (φ - α) := by
        simpa [add_sub_cancel] using Real.sin_add α (φ - α)
      simp [x, hs]; ring
    · simp [x]

private theorem toSphere_sectorClosed_zero :
    ((MeasureTheory.volume : Measure E3).toSphere) (sectorClosed 0) = 0 := by
  let w : E3 := WithLp.toLp 2 ![0, 1, 0]
  have hw : w ≠ 0 := by
    intro h
    have : w 1 = 0 := by rw [h]; rfl
    simp [w] at this
  have hsub : sectorClosed 0 ⊆ {y : Metric.sphere (0 : E3) 1 | ⟪w, y.1⟫_ℝ = 0} := by
    rintro y ⟨φ, hφ, z, _, hy⟩
    have hφ0 : φ = 0 := le_antisymm hφ.2 hφ.1
    rw [Set.mem_ofPred_eq, hy, hφ0]
    simp [w, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  exact measure_mono_null hsub (volume_toSphere_hyperplane_eq_zero hw)

theorem toSphere_sectorClosed_mul_nat {θ : ℝ} (hθ0 : 0 ≤ θ) (q : ℕ) (hq : (q : ℝ) * θ ≤ 2 * Real.pi)
    (p : ℕ) (hp : p ≤ q) :
    ((MeasureTheory.volume : Measure E3).toSphere).real (sectorClosed ((p : ℝ) * θ)) =
      (p : ℝ) * ((MeasureTheory.volume : Measure E3).toSphere).real (sectorClosed θ) := by
  let ν := (MeasureTheory.volume : Measure E3).toSphere
  induction p with
  | zero =>
    simp [measureReal_def, toSphere_sectorClosed_zero]
  | succ k ih =>
    have hk : k ≤ q := Nat.le_of_succ_le hp
    have ihk := ih hk
    have hUnion : sectorClosed (((k + 1 : ℕ) : ℝ) * θ) =
        sectorClosed ((k : ℝ) * θ) ∪ orthoSphereAct (rotZ ((k : ℝ) * θ)) '' sectorClosed θ := by
      have hsucc : (((k + 1 : ℕ) : ℝ) * θ) = (k : ℝ) * θ + θ := by push_cast; ring
      rw [hsucc, rotZ_image_sectorClosed]
      ext y
      simp only [Set.mem_union, sectorClosed, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨φ, hφ, z, hz, hy⟩
        by_cases hsplit : φ ≤ (k : ℝ) * θ
        · exact Or.inl ⟨φ, ⟨hφ.1, hsplit⟩, z, hz, hy⟩
        · exact Or.inr ⟨φ, ⟨(not_le.mp hsplit).le, hφ.2⟩, z, hz, hy⟩
      · rintro (⟨φ, hφ, z, hz, hy⟩ | ⟨φ, hφ, z, hz, hy⟩)
        · exact ⟨φ, ⟨hφ.1, hφ.2.trans (by linarith)⟩, z, hz, hy⟩
        · exact ⟨φ, ⟨(by positivity : (0 : ℝ) ≤ (k : ℝ) * θ).trans hφ.1, hφ.2⟩, z, hz, hy⟩
    have hInter0 : ν (sectorClosed ((k : ℝ) * θ) ∩
        orthoSphereAct (rotZ ((k : ℝ) * θ)) '' sectorClosed θ) = 0 := by
      let w1 : E3 := WithLp.toLp 2 ![-Real.sin ((k : ℝ) * θ), Real.cos ((k : ℝ) * θ), 0]
      let w2 : E3 := WithLp.toLp 2 ![0, 1, 0]
      have hw1 : w1 ≠ 0 := by
        intro h
        have h0 := congrArg (fun v : E3 => v 0 ^ 2 + v 1 ^ 2) h
        simp only [w1, PiLp.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq] at h0
        have := Real.sin_sq_add_cos_sq ((k : ℝ) * θ)
        linarith
      have hw2 : w2 ≠ 0 := by
        intro h
        have : w2 1 = 0 := by rw [h]; rfl
        simp [w2] at this
      have hSub : sectorClosed ((k : ℝ) * θ) ∩
          orthoSphereAct (rotZ ((k : ℝ) * θ)) '' sectorClosed θ ⊆
          {y : Metric.sphere (0 : E3) 1 | ⟪w1, y.1⟫_ℝ = 0} ∪
          {y : Metric.sphere (0 : E3) 1 | ⟪w2, y.1⟫_ℝ = 0} := by
        rw [rotZ_image_sectorClosed]
        rintro y ⟨⟨φ₁, hφ₁, z₁, _, hy₁⟩, ⟨φ₂, hφ₂, z₂, _, hy₂⟩⟩
        have hzEq : z₁ = z₂ := by
          have := congrArg (fun v : E3 => v 2) (hy₁.symm.trans hy₂)
          simpa using this
        subst hzEq
        set r := Real.sqrt (1 - z₁ ^ 2)
        by_cases hr0 : r = 0
        · refine Or.inr ?_
          rw [Set.mem_ofPred_eq, hy₁]
          change ∑ i : Fin 3, _ = 0
          simp [w2, hr0, r, Fin.sum_univ_three]
        · have hx0 : Real.cos φ₁ = Real.cos φ₂ := by
            have := congrArg (fun v : E3 => v 0) (hy₁.symm.trans hy₂)
            exact mul_left_cancel₀ hr0 this
          have hx1 : Real.sin φ₁ = Real.sin φ₂ := by
            have := congrArg (fun v : E3 => v 1) (hy₁.symm.trans hy₂)
            exact mul_left_cancel₀ hr0 this
          have hcosDiff : Real.cos (φ₂ - φ₁) = 1 := by
            rw [Real.cos_sub, hx0, hx1]
            nlinarith [Real.sin_sq_add_cos_sq φ₂]
          have hd0 : 0 ≤ φ₂ - φ₁ := by linarith [hφ₁.2, hφ₂.1]
          have hkq : ((k + 1 : ℕ) : ℝ) * θ ≤ 2 * Real.pi := by
            exact le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hp) hθ0) hq
          have hd2pi : φ₂ - φ₁ ≤ 2 * Real.pi := by
            have hsum : (k : ℝ) * θ + θ = ((k + 1 : ℕ) : ℝ) * θ := by push_cast; ring
            linarith [hφ₁.1, hφ₂.2, hsum, hkq]
          have hcos_lt : ∀ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi), Real.cos t < 1 := by
            intro t ht
            by_cases htp : t ≤ Real.pi
            · exact lt_of_le_of_ne (Real.cos_le_one t) fun h =>
                by have := Real.injOn_cos ⟨ht.1.le, htp⟩ ⟨le_rfl, Real.pi_pos.le⟩ (h.trans Real.cos_zero.symm); linarith [ht.1]
            · have ht2 : 2 * Real.pi - t ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨by linarith [ht.2], by linarith [not_le.mp htp]⟩
              rw [← Real.cos_two_pi_sub t]
              exact lt_of_le_of_ne (Real.cos_le_one _) fun h =>
                by have := Real.injOn_cos ⟨ht2.1.le, ht2.2.le⟩ ⟨le_rfl, Real.pi_pos.le⟩ (h.trans Real.cos_zero.symm); linarith [ht2.1]
          by_cases heq : φ₂ - φ₁ = 0
          · refine Or.inl ?_
            have hφeq : φ₁ = (k : ℝ) * θ := by linarith [hφ₁.2, hφ₂.1, heq]
            rw [Set.mem_ofPred_eq, hy₁, hφeq, PiLp.inner_apply]
            simp [w1, RCLike.inner_apply, Fin.sum_univ_three]
            ring
          · have hgt : 0 < φ₂ - φ₁ := lt_of_le_of_ne hd0 (Ne.symm heq)
            have h2pi : φ₂ - φ₁ = 2 * Real.pi := by
              by_contra hne
              have := hcos_lt (φ₂ - φ₁) ⟨hgt, lt_of_le_of_ne hd2pi hne⟩
              linarith
            have hφ0 : φ₁ = 0 := by
              have hsum : (k : ℝ) * θ + θ = ((k + 1 : ℕ) : ℝ) * θ := by push_cast; ring
              linarith [hφ₁.1, hφ₂.2, hsum, hkq, h2pi]
            refine Or.inr ?_
            rw [Set.mem_ofPred_eq, hy₁, hφ0]
            simp [w2, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
      exact measure_mono_null hSub (by simp [ν, volume_toSphere_hyperplane_eq_zero hw1,
        volume_toSphere_hyperplane_eq_zero hw2])
    have hPiece : ν (orthoSphereAct (rotZ ((k : ℝ) * θ)) '' sectorClosed θ) = ν (sectorClosed θ) := by
      let g := rotZ ((k : ℝ) * θ)
      have heq : orthoSphereAct g '' sectorClosed θ = orthoSphereAct g⁻¹ ⁻¹' sectorClosed θ := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · exact fun hy => ⟨orthoSphereAct g⁻¹ y, hy, orthoSphereAct_apply_inv g y⟩
      rw [heq, ← Measure.map_apply (orthoSphereAct g⁻¹).continuous.measurable
        (sectorClosed_measurableSet θ), toSphere_oGroup_invariant 3 g⁻¹]
    have hAdd : ν (sectorClosed (((k + 1 : ℕ) : ℝ) * θ)) =
        ν (sectorClosed ((k : ℝ) * θ)) + ν (sectorClosed θ) := by
      have hm2 : MeasurableSet (orthoSphereAct (rotZ ((k : ℝ) * θ)) '' sectorClosed θ) :=
        (orthoSphereAct (rotZ _)).measurableEmbedding.measurableSet_image.mpr
          (sectorClosed_measurableSet θ)
      have hmi := measure_union_add_inter (μ := ν) (sectorClosed ((k : ℝ) * θ)) hm2
      rw [← hUnion] at hmi
      rw [hInter0, add_zero, hPiece] at hmi
      exact hmi
    rw [measureReal_def, hAdd, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [← measureReal_def, ← measureReal_def, ihk]
    push_cast
    ring

private lemma rat_natAbs_div_den {qrat : ℚ} (hqPos : 0 < qrat) (hqLe1 : qrat ≤ 1) :
    qrat.num.natAbs ≤ qrat.den ∧ (qrat : ℝ) = (qrat.num.natAbs : ℝ) / (qrat.den : ℝ) := by
  have hnumPos : (0 : ℤ) < qrat.num := Rat.num_pos.mpr hqPos
  have hdiv : (qrat.num : ℚ) / (qrat.den : ℚ) ≤ 1 := by rwa [Rat.num_div_den qrat]
  have hdenPos : (0 : ℚ) < qrat.den := Nat.cast_pos.mpr qrat.den_pos
  have hle : qrat.num ≤ (qrat.den : ℤ) := by exact_mod_cast (div_le_one hdenPos).mp hdiv
  have hqp : qrat.num.natAbs ≤ qrat.den := by omega
  refine ⟨hqp, ?_⟩
  have hnatZ : qrat.num = (qrat.num.natAbs : ℤ) := (Int.natAbs_of_nonneg hnumPos.le).symm
  have hnat : (qrat.num : ℝ) = (qrat.num.natAbs : ℝ) := by
    calc (qrat.num : ℝ) = ((qrat.num.natAbs : ℤ) : ℝ) := congrArg Int.cast hnatZ
      _ = (qrat.num.natAbs : ℝ) := Int.cast_natCast _
  rw [Rat.cast_def, hnat]

theorem toSphere_sectorClosed_eq {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2pi : θ ≤ 2 * Real.pi) :
    ((MeasureTheory.volume : Measure E3).toSphere).real (sectorClosed θ) =
      (θ / (2 * Real.pi)) * ((MeasureTheory.volume : Measure E3).toSphere).real Set.univ := by
  let ν := (MeasureTheory.volume : Measure E3).toSphere
  let M := ν.real Set.univ
  have hM : 0 < M := toSphere_real_univ_pos 3
  have hRat : ∀ (p q : ℕ), 0 < q → p ≤ q →
      ν.real (sectorClosed (((p : ℝ) / (q : ℝ)) * (2 * Real.pi))) =
        ((p : ℝ) / (q : ℝ)) * M := by
    intro p q hq hpq
    have hθ : 0 ≤ (2 * Real.pi) / (q : ℝ) := by positivity
    have hqle : (q : ℝ) * ((2 * Real.pi) / (q : ℝ)) ≤ 2 * Real.pi := by
      rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hq.ne')]
    have hp := toSphere_sectorClosed_mul_nat hθ q hqle p hpq
    have hqFull := toSphere_sectorClosed_mul_nat hθ q hqle q le_rfl
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hq.ne'), sectorClosed_two_pi] at hqFull
    have hp' : ν.real (sectorClosed (((p : ℝ) / (q : ℝ)) * (2 * Real.pi))) =
        (p : ℝ) * ν.real (sectorClosed ((2 * Real.pi) / (q : ℝ))) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hp
    have hdiv : ν.real (sectorClosed ((2 * Real.pi) / (q : ℝ))) = M / (q : ℝ) := by
      field_simp [Nat.cast_ne_zero.mpr hq.ne']
      linarith
    rw [hp', hdiv]
    ring
  apply le_antisymm
  · by_contra hgt
    rw [not_le] at hgt
    let t := θ / (2 * Real.pi)
    let r := min 1 (ν.real (sectorClosed θ) / M)
    have htr : t < r := lt_min (by
      by_cases h2 : θ = 2 * Real.pi
      · subst h2
        exfalso
        rw [sectorClosed_two_pi, div_self (by positivity : 2 * Real.pi ≠ 0), one_mul] at hgt
        exact lt_irrefl _ hgt
      · exact (div_lt_one (by positivity)).mpr (lt_of_le_of_ne hθ2pi h2))
      ((lt_div_iff₀ hM).mpr hgt)
    obtain ⟨qrat, hq1, hq2⟩ := exists_rat_btwn htr
    have hqPos : (0 : ℚ) < qrat := by
      exact_mod_cast lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ t) hq1
    have hqLe1 : qrat ≤ 1 := by
      have : (qrat : ℝ) ≤ 1 := le_trans hq2.le (min_le_left _ _)
      exact_mod_cast this
    obtain ⟨hqp, hqeq⟩ := rat_natAbs_div_den hqPos hqLe1
    let p := qrat.num.natAbs
    let q := qrat.den
    have hq_pos_nat : 0 < q := qrat.den_pos
    have hθlt : θ < ((p : ℝ) / (q : ℝ)) * (2 * Real.pi) := by
      rw [← hqeq]
      exact (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hq1
    have hMono : ν.real (sectorClosed θ) ≤
        ν.real (sectorClosed (((p : ℝ) / (q : ℝ)) * (2 * Real.pi))) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (sectorClosed_mono hθlt.le))
    rw [hRat p q hq_pos_nat hqp, ← hqeq] at hMono
    have hcontra : (qrat : ℝ) * M < ν.real (sectorClosed θ) := by
      have h1 : (qrat : ℝ) < ν.real (sectorClosed θ) / M := lt_of_lt_of_le hq2 (min_le_right _ _)
      exact (lt_div_iff₀ hM).mp h1
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    let t := θ / (2 * Real.pi)
    let r := ν.real (sectorClosed θ) / M
    have hrt : r < t := (div_lt_iff₀ hM).mpr hlt
    obtain ⟨qrat, hq1, hq2⟩ := exists_rat_btwn hrt
    have hqPos : (0 : ℚ) < qrat := by
      have hrnn : 0 ≤ r := div_nonneg measureReal_nonneg hM.le
      exact_mod_cast (lt_of_le_of_lt hrnn hq1)
    have hqLe1 : qrat ≤ 1 := by
      have : (qrat : ℝ) ≤ 1 := le_trans hq2.le ((div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr hθ2pi)
      exact_mod_cast this
    obtain ⟨hqp, hqeq⟩ := rat_natAbs_div_den hqPos hqLe1
    let p := qrat.num.natAbs
    let q := qrat.den
    have hq_pos_nat : 0 < q := qrat.den_pos
    have hθgt : ((p : ℝ) / (q : ℝ)) * (2 * Real.pi) < θ := by
      rw [← hqeq]
      exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hq2
    have hMono : ν.real (sectorClosed (((p : ℝ) / (q : ℝ)) * (2 * Real.pi))) ≤
        ν.real (sectorClosed θ) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (sectorClosed_mono hθgt.le))
    rw [hRat p q hq_pos_nat hqp, ← hqeq] at hMono
    have hcontra : ν.real (sectorClosed θ) < (qrat : ℝ) * M := (div_lt_iff₀ hM).mp hq1
    linarith

/-- Closed spherical lune on `S² ⊂ E3` bounded by inward unit normals `u, v`. -/
def lune (u v : Metric.sphere (0 : E3) 1) : Set (Metric.sphere (0 : E3) 1) :=
  {y | 0 ≤ ⟪u.1, y.1⟫_ℝ ∧ 0 ≤ ⟪v.1, y.1⟫_ℝ}

theorem lune_measurableSet (u v : Metric.sphere (0 : E3) 1) : MeasurableSet (lune u v) := by
  change MeasurableSet ({y : Metric.sphere (0 : E3) 1 | 0 ≤ ⟪u.1, y.1⟫_ℝ} ∩
    {y : Metric.sphere (0 : E3) 1 | 0 ≤ ⟪v.1, y.1⟫_ℝ})
  exact ((isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)).inter
    (isClosed_le continuous_const (continuous_const.inner continuous_subtype_val))).measurableSet

/-- Interior dihedral angle `arccos (-⟪u, v⟫)` of `lune u v` (in `[0, π]`). -/
def luneAngle (u v : Metric.sphere (0 : E3) 1) : ℝ :=
  Real.arccos (-⟪u.1, v.1⟫_ℝ)

private def cross3 (a b : E3) : E3 :=
  WithLp.toLp 2 ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

private theorem cross3_orthog_left (a b : E3) : ⟪a, cross3 a b⟫_ℝ = 0 := by
  simp [cross3, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring

private theorem cross3_orthog_right (a b : E3) : ⟪b, cross3 a b⟫_ℝ = 0 := by
  simp [cross3, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]; ring

private theorem cross3_norm_one (a b : E3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫_ℝ = 0) :
    ‖cross3 a b‖ = 1 := by
  have h1 : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1 := by
    have h : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
    rw [PiLp.inner_apply] at h
    simpa only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, sq] using h
  have h2 : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 1 := by
    have h : ⟪b, b⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hb, one_pow]
    rw [PiLp.inner_apply] at h
    simpa only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, sq] using h
  have h3 : a 0 * b 0 + a 1 * b 1 + a 2 * b 2 = 0 := by
    rw [PiLp.inner_apply] at hab
    simpa only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, mul_comm] using hab
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
    PiLp.inner_apply]
  simp [cross3, Fin.sum_univ_three]
  nlinarith [sq (a 0 * b 0 + a 1 * b 1 + a 2 * b 2)]

theorem toSphere_real_lune (u v : Metric.sphere (0 : E3) 1) :
    ((MeasureTheory.volume : Measure E3).toSphere).real (lune u v) =
      (luneAngle u v / (2 * Real.pi)) *
        ((MeasureTheory.volume : Measure E3).toSphere).real Set.univ := by
  let θ := luneAngle u v
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθpi : θ ≤ Real.pi := Real.arccos_le_pi _
  have hu1 : ‖u.1‖ = 1 := by simpa using u.2
  have hv1 : ‖v.1‖ = 1 := by simpa using v.2
  have hinnerBnd : -⟪u.1, v.1⟫_ℝ ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := abs_real_inner_le_norm u.1 v.1
    rw [hu1, hv1, mul_one] at h
    exact abs_le.mp (by simpa [abs_neg] using h)
  have hcosθ : Real.cos θ = -⟪u.1, v.1⟫_ℝ := Real.cos_arccos hinnerBnd.1 hinnerBnd.2
  by_cases hθZero : θ = 0
  · have hvu : v.1 = -u.1 := by
      have hcos1 : -⟪u.1, v.1⟫_ℝ = 1 := by rw [← hcosθ, hθZero, Real.cos_zero]
      have hsq : ‖u.1 + v.1‖ ^ 2 = 0 := by
        rw [@norm_add_sq_real, hu1, hv1]
        linarith
      exact eq_neg_of_add_eq_zero_right (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    have hsub : lune u v ⊆ {y : Metric.sphere (0 : E3) 1 | ⟪u.1, y.1⟫_ℝ = 0} := by
      rintro y ⟨hy1, hy2⟩
      rw [hvu, inner_neg_left] at hy2
      exact le_antisymm (by linarith) hy1
    have huNe : u.1 ≠ 0 := fun h => by rw [h, norm_zero] at hu1; norm_num at hu1
    have hm0 := measure_mono_null hsub (volume_toSphere_hyperplane_eq_zero huNe)
    have hlune0 : luneAngle u v = 0 := hθZero
    rw [measureReal_def, hm0, ENNReal.toReal_zero, hlune0, zero_div, zero_mul]
  · have hθPos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθZero)
    let u₀vec : E3 := WithLp.toLp 2 ![1, 0, 0]
    let v₀vec : E3 := WithLp.toLp 2 ![-Real.cos θ, Real.sin θ, 0]
    have hu₀norm : ‖u₀vec‖ = 1 := by
      rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
        PiLp.inner_apply]
      simp [u₀vec, Fin.sum_univ_three]
    have hv₀norm : ‖v₀vec‖ = 1 := by
      rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
        PiLp.inner_apply]
      simp [v₀vec, Fin.sum_univ_three]
    let u₀ : Metric.sphere (0 : E3) 1 :=
      ⟨u₀vec, by simpa [Metric.mem_sphere, dist_zero_right] using hu₀norm⟩
    let v₀ : Metric.sphere (0 : E3) 1 :=
      ⟨v₀vec, by simpa [Metric.mem_sphere, dist_zero_right] using hv₀norm⟩
    have hStandard : lune u₀ v₀ =
        orthoSphereAct (rotZ (Real.pi / 2 - θ)) '' sectorClosed θ := by
      rw [rotZ_image_sectorClosed]
      ext y
      simp only [lune, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hy0, hy1⟩
        rw [PiLp.inner_apply] at hy0 hy1
        simp [u₀, u₀vec, Fin.sum_univ_three] at hy0
        simp [v₀, v₀vec, Fin.sum_univ_three] at hy1
        have hy0' : 0 ≤ y.1 0 := hy0
        have hy1' : 0 ≤ -Real.cos θ * y.1 0 + Real.sin θ * y.1 1 := by linarith
        have hyNorm : ‖y.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
        have hsq : y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2 = 1 := by
          have h : ⟪y.1, y.1⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hyNorm, one_pow]
          rw [PiLp.inner_apply] at h
          simpa only [RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, sq] using h
        have hz : y.1 2 ∈ Set.Icc (-1 : ℝ) 1 := by
          have : y.1 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y.1 0), sq_nonneg (y.1 1)]
          exact abs_le.mp ((sq_le_one_iff₀ (abs_nonneg _)).mp (by simpa [sq_abs] using this))
        set r := Real.sqrt (1 - y.1 2 ^ 2)
        have hrSq : r ^ 2 = y.1 0 ^ 2 + y.1 1 ^ 2 := by
          rw [Real.sq_sqrt (by linarith [hsq, sq_nonneg (y.1 0), sq_nonneg (y.1 1)])]
          linarith
        by_cases hr0 : r = 0
        · have hxy0 : y.1 0 = 0 ∧ y.1 1 = 0 := by
            have : y.1 0 ^ 2 + y.1 1 ^ 2 = 0 := by rw [← hrSq, hr0]; norm_num
            exact ⟨sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (y.1 1)]),
                   sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (y.1 0)])⟩
          refine ⟨Real.pi / 2 - θ, ⟨le_rfl, by linarith⟩, y.1 2, hz, ?_⟩
          have hr0' : Real.sqrt (1 - y.1 2 ^ 2) = 0 := hr0
          ext i
          fin_cases i <;> simp [hr0', hxy0.1, hxy0.2]
        · have hrPos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
          have hunit : (y.1 0 / r) ^ 2 + (y.1 1 / r) ^ 2 = 1 := by
            field_simp [hrPos.ne']; linarith
          have h0Bnd : 0 ≤ y.1 0 / r ∧ y.1 0 / r ≤ 1 := by
            have hle : (y.1 0 / r) ^ 2 ≤ 1 := by linarith [sq_nonneg (y.1 1 / r)]
            exact ⟨div_nonneg hy0' hrPos.le,
              (abs_le.mp ((sq_le_one_iff₀ (abs_nonneg _)).mp (by simpa [sq_abs] using hle))).2⟩
          let φ := if 0 ≤ y.1 1 then Real.arccos (y.1 0 / r) else -Real.arccos (y.1 0 / r)
          have hcosφ : Real.cos φ = y.1 0 / r := by
            by_cases h : 0 ≤ y.1 1
            · simp [φ, h, Real.cos_arccos (by linarith [h0Bnd.1]) h0Bnd.2]
            · simp [φ, h, Real.cos_neg, Real.cos_arccos (by linarith [h0Bnd.1]) h0Bnd.2]
          have hsinφ : Real.sin φ = y.1 1 / r := by
            have hs : Real.sin (Real.arccos (y.1 0 / r)) = |y.1 1 / r| := by
              rw [Real.sin_arccos]
              have : 1 - (y.1 0 / r) ^ 2 = (y.1 1 / r) ^ 2 := by linarith
              rw [this, Real.sqrt_sq_eq_abs]
            by_cases h : 0 ≤ y.1 1
            · simp [φ, h, hs, abs_of_nonneg (div_nonneg h hrPos.le)]
            · simp [φ, h, Real.sin_neg, hs, abs_of_neg (div_neg_of_neg_of_pos (lt_of_not_ge h) hrPos)]
          have hφIcc : φ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
            have harc : Real.arccos (y.1 0 / r) ≤ Real.pi / 2 := by
              rw [← Real.arccos_zero]
              exact Real.arccos_le_arccos (by linarith [h0Bnd.1])
            have harc0 : 0 ≤ Real.arccos (y.1 0 / r) := Real.arccos_nonneg _
            by_cases h : 0 ≤ y.1 1 <;> simp only [φ, h, ↓reduceIte, Set.mem_Icc] <;>
              constructor <;> linarith
          have hcosSum : Real.cos (θ + φ) ≤ 0 := by
            have hadd : -Real.cos (θ + φ) = -Real.cos θ * (y.1 0 / r) + Real.sin θ * (y.1 1 / r) := by
              rw [Real.cos_add, hcosφ, hsinφ]; ring
            have hnn : 0 ≤ -Real.cos (θ + φ) := by
              rw [hadd]
              have : -Real.cos θ * (y.1 0 / r) + Real.sin θ * (y.1 1 / r) =
                  (-Real.cos θ * y.1 0 + Real.sin θ * y.1 1) / r := by ring
              rw [this]
              exact div_nonneg hy1' hrPos.le
            linarith
          have hφLower : Real.pi / 2 - θ ≤ φ := by
            by_contra hlt
            rw [not_le] at hlt
            have hmem : θ + φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
              ⟨by linarith [hφIcc.1, hθPos], by linarith⟩
            have hpos := Real.cos_pos_of_mem_Ioo hmem
            linarith
          refine ⟨φ, ⟨hφLower, by linarith [hφIcc.2]⟩, y.1 2, hz, ?_⟩
          ext i
          fin_cases i
          · simp [r, hcosφ, mul_div_cancel₀ _ hrPos.ne']
          · simp [r, hsinφ, mul_div_cancel₀ _ hrPos.ne']
          · rfl
      · rintro ⟨φ, ⟨hφ1, hφ2⟩, z, hz, hy⟩
        have hφ2' : φ ≤ Real.pi / 2 := by linarith [hφ2]
        have hrz : 0 ≤ Real.sqrt (1 - z ^ 2) := Real.sqrt_nonneg _
        have hcos_nn : 0 ≤ Real.cos φ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ1, hθpi], hφ2'⟩
        let ψ := θ + φ - Real.pi / 2
        have hψ : 0 ≤ ψ ∧ ψ ≤ Real.pi :=
          ⟨by dsimp [ψ]; linarith [hφ1], by dsimp [ψ]; linarith [hφ2', hθpi]⟩
        have hsin_nn : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 hψ.2
        have hcos_neg : -Real.cos (θ + φ) = Real.sin ψ := by
          have : θ + φ = Real.pi / 2 + ψ := by dsimp [ψ]; ring
          rw [this, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
          ring
        have hy0_nn : 0 ≤ Real.sqrt (1 - z ^ 2) * Real.cos φ := mul_nonneg hrz hcos_nn
        have hy1_nn : 0 ≤ Real.sqrt (1 - z ^ 2) * (-Real.cos (θ + φ)) :=
          mul_nonneg hrz (by linarith [hcos_neg, hsin_nn])
        rw [PiLp.inner_apply, PiLp.inner_apply, hy]
        constructor
        · simp [u₀, u₀vec, Fin.sum_univ_three]
          exact hy0_nn
        · simp [v₀, v₀vec, Fin.sum_univ_three]
          have hid : Real.sqrt (1 - z ^ 2) * Real.cos φ * (-Real.cos θ) +
              Real.sqrt (1 - z ^ 2) * Real.sin φ * Real.sin θ =
              Real.sqrt (1 - z ^ 2) * (-Real.cos (θ + φ)) := by
            rw [Real.cos_add]
            ring
          linarith [hid, hy1_nn]
    have hEqStd : ∃ g : OGroup 3, orthoSphereAct g u₀ = u ∧ orthoSphereAct g v₀ = v := by
      by_cases hθPi : θ = Real.pi
      · have huv : v = u := by
          have hcos1 : ⟪u.1, v.1⟫_ℝ = 1 := by
            have := hcosθ
            rw [hθPi, Real.cos_pi] at this
            linarith
          have hsq : ‖u.1 - v.1‖ ^ 2 = 0 := by
            rw [@norm_sub_sq_real, hu1, hv1, hcos1]
            ring
          exact Subtype.ext (eq_of_sub_eq_zero (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))).symm
        obtain ⟨g, hg⟩ := oGroup_transitive_sphere u₀ u
        refine ⟨g, hg, ?_⟩
        rw [huv, ← hg]
        congr 1
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [u₀, v₀, u₀vec, v₀vec, hθPi]
      · have hθLtPi : θ < Real.pi := lt_of_le_of_ne hθpi hθPi
        have hsinPos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθPos hθLtPi
        let e0 : E3 := u.1
        let e1 : E3 := (Real.sin θ)⁻¹ • (v.1 + Real.cos θ • u.1)
        let e2 : E3 := cross3 e0 e1
        have he0 : ‖e0‖ = 1 := hu1
        have huvCos : ⟪u.1, v.1⟫_ℝ = -Real.cos θ := by linarith [hcosθ]
        have he01 : ⟪e0, e1⟫_ℝ = 0 := by
          simp only [e0, e1, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
            hu1, one_pow, huvCos, mul_one, neg_add_cancel, mul_zero]
        have he1 : ‖e1‖ = 1 := by
          have hvv : ⟪v.1 + Real.cos θ • u.1, v.1 + Real.cos θ • u.1⟫_ℝ = Real.sin θ ^ 2 := by
            have hvuCos : ⟪v.1, u.1⟫_ℝ = -Real.cos θ := by rw [real_inner_comm]; exact huvCos
            have huu : ⟪u.1, u.1⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu1, one_pow]
            have hvv1 : ⟪v.1, v.1⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hv1, one_pow]
            simp only [inner_add_left, inner_add_right, real_inner_smul_left,
              real_inner_smul_right, huu, hvv1, huvCos, hvuCos]
            nlinarith [Real.sin_sq_add_cos_sq θ]
          rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq]
          simp only [e1, real_inner_smul_left, real_inner_smul_right, hvv]
          field_simp [hsinPos.ne']
        have he2 : ‖e2‖ = 1 := cross3_norm_one e0 e1 he0 he1 he01
        have he02 : ⟪e0, e2⟫_ℝ = 0 := cross3_orthog_left e0 e1
        have he12 : ⟪e1, e2⟫_ℝ = 0 := cross3_orthog_right e0 e1
        let basis : Fin 3 → E3 := fun p => match p with | 0 => e0 | 1 => e1 | 2 => e2
        have hOrtho : ∀ a b : Fin 3, ⟪basis a, basis b⟫_ℝ = if a = b then 1 else 0 := by
          have he00 : ⟪e0, e0⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he0, one_pow]
          have he11 : ⟪e1, e1⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he1, one_pow]
          have he22 : ⟪e2, e2⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he2, one_pow]
          have h10 : ⟪e1, e0⟫_ℝ = 0 := by rw [real_inner_comm]; exact he01
          have h20 : ⟪e2, e0⟫_ℝ = 0 := by rw [real_inner_comm]; exact he02
          have h21 : ⟪e2, e1⟫_ℝ = 0 := by rw [real_inner_comm]; exact he12
          intro a b
          fin_cases a <;> fin_cases b <;>
            simp only [basis, he00, he11, he22, he01, he02, he12, h10, h20, h21] <;> simp
        let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => basis j i
        have hMO : M ∈ OGroup 3 := by
          rw [Matrix.mem_orthogonalGroup_iff']
          ext a b
          simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.of_apply, Matrix.one_apply]
          have hsum : ∑ i : Fin 3, basis a i * basis b i = ⟪basis a, basis b⟫_ℝ := by
            rw [PiLp.inner_apply]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [RCLike.inner_apply, mul_comm]
          rw [hsum, hOrtho a b]
        let g : OGroup 3 := ⟨M, hMO⟩
        refine ⟨g, Subtype.ext ?_, Subtype.ext ?_⟩
        · ext i
          simp [g, orthoSphereAct_val, mulVecE_apply, Fin.sum_univ_three, u₀, u₀vec, M, basis, e0]
        · have hvRep : (-Real.cos θ) • e0 + (Real.sin θ) • e1 = v.1 := by
            dsimp [e1]
            rw [smul_smul, mul_inv_cancel₀ hsinPos.ne', one_smul]
            module
          rw [← hvRep]
          ext i
          simp [g, orthoSphereAct_val, mulVecE_apply, Fin.sum_univ_three, v₀, v₀vec, M, basis]
          ring
    rcases hEqStd with ⟨g, hgu, hgv⟩
    have hluneImg : orthoSphereAct g '' lune u₀ v₀ = lune u v := by
      ext y
      simp only [Set.mem_image, lune, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
        have h0 : ⟪u.1, (orthoSphereAct g x).1⟫_ℝ = ⟪u₀.1, x.1⟫_ℝ := by
          rw [← hgu, orthoSphereAct_val, orthoSphereAct_val, (orthoEquiv g).inner_map_map]
        have h1 : ⟪v.1, (orthoSphereAct g x).1⟫_ℝ = ⟪v₀.1, x.1⟫_ℝ := by
          rw [← hgv, orthoSphereAct_val, orthoSphereAct_val, (orthoEquiv g).inner_map_map]
        exact ⟨h0 ▸ hx0, h1 ▸ hx1⟩
      · rintro ⟨hy0, hy1⟩
        refine ⟨orthoSphereAct g⁻¹ y, ?_, orthoSphereAct_apply_inv g y⟩
        have h0 : ⟪u₀.1, (orthoSphereAct g⁻¹ y).1⟫_ℝ = ⟪u.1, y.1⟫_ℝ := by
          have hu' : orthoEquiv g⁻¹ u.1 = u₀.1 := by
            rw [← hgu, orthoSphereAct_val, ← orthoEquiv_mul, inv_mul_cancel, orthoEquiv_one]
          rw [← hu', orthoSphereAct_val, (orthoEquiv g⁻¹).inner_map_map]
        have h1 : ⟪v₀.1, (orthoSphereAct g⁻¹ y).1⟫_ℝ = ⟪v.1, y.1⟫_ℝ := by
          have hv' : orthoEquiv g⁻¹ v.1 = v₀.1 := by
            rw [← hgv, orthoSphereAct_val, ← orthoEquiv_mul, inv_mul_cancel, orthoEquiv_one]
          rw [← hv', orthoSphereAct_val, (orthoEquiv g⁻¹).inner_map_map]
        exact ⟨h0 ▸ hy0, h1 ▸ hy1⟩
    have meas_image_oGroup : ∀ (k : OGroup 3) {s : Set (Metric.sphere (0 : E3) 1)}
        (hs : MeasurableSet s),
        ((MeasureTheory.volume : Measure E3).toSphere).real (orthoSphereAct k '' s) =
          ((MeasureTheory.volume : Measure E3).toSphere).real s := by
      intro k s hs
      have heq : orthoSphereAct k '' s = orthoSphereAct k⁻¹ ⁻¹' s := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · exact fun hy => ⟨orthoSphereAct k⁻¹ y, hy, orthoSphereAct_apply_inv k y⟩
      rw [heq, measureReal_def,
        ← Measure.map_apply (orthoSphereAct k⁻¹).continuous.measurable hs,
        toSphere_oGroup_invariant 3 k⁻¹]
      rfl
    rw [← hluneImg, meas_image_oGroup g (lune_measurableSet u₀ v₀), hStandard,
      meas_image_oGroup (rotZ (Real.pi / 2 - θ)) (sectorClosed_measurableSet θ),
      toSphere_sectorClosed_eq hθ0 (by linarith [hθpi, Real.pi_pos])]

/-- Spherical triangle on `S² ⊂ E3` cut out by 3 inward unit normals `w : Fin 3 → S²`. -/
def triSet (w : Fin 3 → Metric.sphere (0 : E3) 1) : Set (Metric.sphere (0 : E3) 1) :=
  {y | ∀ k : Fin 3, 0 ≤ ⟪(w k).1, y.1⟫_ℝ}

/-- Standard `S²` excess area `α₀₁ + α₁₂ + α₂₀ - π`. -/
def stdTriArea (w : Fin 3 → Metric.sphere (0 : E3) 1) : ℝ :=
  luneAngle (w 0) (w 1) + luneAngle (w 1) (w 2) + luneAngle (w 2) (w 0) - Real.pi

theorem triSet_measurableSet (w : Fin 3 → Metric.sphere (0 : E3) 1) :
    MeasurableSet (triSet w) := by
  have hClosed : IsClosed (triSet w) := by
    change IsClosed {y : Metric.sphere (0 : E3) 1 | ∀ k : Fin 3, 0 ≤ ⟪(w k).1, y.1⟫_ℝ}
    rw [Set.setOf_forall]
    exact isClosed_iInter fun k =>
      isClosed_le continuous_const (continuous_const.inner continuous_subtype_val)
  exact hClosed.measurableSet

private def negOGroup (n : ℕ) : OGroup n :=
  ⟨-1, by rw [Matrix.mem_orthogonalGroup_iff]; simp⟩

private theorem orthoSphereAct_negOGroup_val {n : ℕ} (y : Metric.sphere (0 : E n) 1) :
    (orthoSphereAct (negOGroup n) y).1 = -y.1 := by
  ext i
  simp [negOGroup, orthoSphereAct_val, mulVecE_apply, Matrix.one_apply]

theorem toSphere_real_triSet (w : Fin 3 → Metric.sphere (0 : E3) 1)
    (hw : LinearIndependent ℝ (fun k : Fin 3 => (w k).1)) :
    ((MeasureTheory.volume : Measure E3).toSphere).real (triSet w) =
      (((MeasureTheory.volume : Measure E3).toSphere).real Set.univ / (4 * Real.pi)) *
        stdTriArea w := by
  let ν := (MeasureTheory.volume : Measure E3).toSphere
  let M := ν.real Set.univ
  let neg (u : Metric.sphere (0 : E3) 1) : Metric.sphere (0 : E3) 1 :=
    orthoSphereAct (negOGroup 3) u
  have hnegVal (u : Metric.sphere (0 : E3) 1) : (neg u).1 = -u.1 :=
    orthoSphereAct_negOGroup_val u
  let wNeg : Fin 3 → Metric.sphere (0 : E3) 1 := fun k => neg (w k)
  let dbl (u v : Metric.sphere (0 : E3) 1) : Set (Metric.sphere (0 : E3) 1) :=
    lune u v ∪ lune (neg u) (neg v)
  have hmeasDbl (u v : Metric.sphere (0 : E3) 1) : MeasurableSet (dbl u v) :=
    (lune_measurableSet u v).union (lune_measurableSet (neg u) (neg v))
  have hmeasNegTri : MeasurableSet (triSet wNeg) := triSet_measurableSet wNeg
  have hnegImg (s : Set (Metric.sphere (0 : E3) 1)) (hs : MeasurableSet s) :
      ν.real (orthoSphereAct (negOGroup 3) ⁻¹' s) = ν.real s := by
    rw [measureReal_def, ← Measure.map_apply (orthoSphereAct (negOGroup 3)).continuous.measurable hs,
      toSphere_oGroup_invariant 3 (negOGroup 3)]
    rfl
  have hNegTriEq : ν.real (triSet wNeg) = ν.real (triSet w) := by
    have heq : triSet wNeg = orthoSphereAct (negOGroup 3) ⁻¹' triSet w := by
      ext y
      simp only [triSet, Set.mem_setOf_eq, Set.mem_preimage, hnegVal, orthoSphereAct_negOGroup_val,
        inner_neg_left, inner_neg_right, neg_neg, wNeg]
    rw [heq]
    exact hnegImg (triSet w) (triSet_measurableSet w)
  have hDblReal (u v : Metric.sphere (0 : E3) 1) :
      ν.real (dbl u v) = 2 * ν.real (lune u v) := by
    have hLuneNeg : ν.real (lune (neg u) (neg v)) = ν.real (lune u v) := by
      have heq : lune (neg u) (neg v) = orthoSphereAct (negOGroup 3) ⁻¹' lune u v := by
        ext y
        simp only [lune, Set.mem_setOf_eq, Set.mem_preimage, hnegVal, orthoSphereAct_negOGroup_val,
          inner_neg_left, inner_neg_right, neg_neg]
      rw [heq]
      exact hnegImg (lune u v) (lune_measurableSet u v)
    have hInter : ν (lune u v ∩ lune (neg u) (neg v)) = 0 := by
      have hsub : lune u v ∩ lune (neg u) (neg v) ⊆
          {y : Metric.sphere (0 : E3) 1 | ⟪u.1, y.1⟫_ℝ = 0} := by
        rintro y ⟨⟨hy1, _⟩, ⟨hy2, _⟩⟩
        rw [hnegVal, inner_neg_left] at hy2
        exact le_antisymm (by linarith) hy1
      have huNe : u.1 ≠ 0 := by
        have h : ‖u.1‖ = 1 := by simpa using u.2
        intro hz; rw [hz, norm_zero] at h; norm_num at h
      exact measure_mono_null hsub (volume_toSphere_hyperplane_eq_zero huNe)
    have hmi := measure_union_add_inter (μ := ν) (lune u v) (lune_measurableSet (neg u) (neg v))
    rw [hInter, add_zero] at hmi
    change ν (dbl u v) = ν (lune u v) + ν (lune (neg u) (neg v)) at hmi
    rw [measureReal_def, hmi, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← measureReal_def, ← measureReal_def, hLuneNeg]
    ring
  let bdry : Set (Metric.sphere (0 : E3) 1) :=
    ⋃ k : Fin 3, {y : Metric.sphere (0 : E3) 1 | ⟪(w k).1, y.1⟫_ℝ = 0}
  have hBdry0 : ν bdry = 0 := by
    refine measure_iUnion_null fun k => volume_toSphere_hyperplane_eq_zero ?_
    have hk : ‖(w k).1‖ = 1 := by simpa using (w k).2
    intro hz; rw [hz, norm_zero] at hk; norm_num at hk
  let f : Metric.sphere (0 : E3) 1 → ℝ := fun y =>
    (dbl (w 0) (w 1)).indicator (fun _ => 1) y +
    (dbl (w 1) (w 2)).indicator (fun _ => 1) y +
    (dbl (w 2) (w 0)).indicator (fun _ => 1) y
  let g : Metric.sphere (0 : E3) 1 → ℝ := fun y =>
    1 + 2 * (triSet w).indicator (fun _ => 1) y + 2 * (triSet wNeg).indicator (fun _ => 1) y
  have hae : f =ᵐ[ν] g := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun y hy => ?_) hBdry0
    by_contra hnot
    have hne : ∀ k : Fin 3, ⟪(w k).1, y.1⟫_ℝ ≠ 0 := fun k hk =>
      hnot (Set.mem_iUnion.mpr ⟨k, hk⟩)
    apply hy
    have h0ne := hne 0
    have h1ne := hne 1
    have h2ne := hne 2
    have htri : y ∈ triSet w ↔
        (0 ≤ ⟪(w 0).1, y.1⟫_ℝ ∧ 0 ≤ ⟪(w 1).1, y.1⟫_ℝ ∧ 0 ≤ ⟪(w 2).1, y.1⟫_ℝ) := by
      simp only [triSet, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨a, b, c⟩ k => by fin_cases k <;> assumption⟩
    have htriNeg : y ∈ triSet wNeg ↔
        (0 ≤ ⟪(neg (w 0)).1, y.1⟫_ℝ ∧ 0 ≤ ⟪(neg (w 1)).1, y.1⟫_ℝ ∧ 0 ≤ ⟪(neg (w 2)).1, y.1⟫_ℝ) := by
      simp only [triSet, Set.mem_ofPred_eq, wNeg]
      exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨a, b, c⟩ k => by fin_cases k <;> assumption⟩
    have h0' : 0 ≤ ⟪(neg (w 0)).1, y.1⟫_ℝ ↔ ¬ 0 ≤ ⟪(w 0).1, y.1⟫_ℝ := by
      rw [hnegVal, inner_neg_left]; exact ⟨fun h hle => h0ne (by linarith), fun h => by linarith⟩
    have h1' : 0 ≤ ⟪(neg (w 1)).1, y.1⟫_ℝ ↔ ¬ 0 ≤ ⟪(w 1).1, y.1⟫_ℝ := by
      rw [hnegVal, inner_neg_left]; exact ⟨fun h hle => h1ne (by linarith), fun h => by linarith⟩
    have h2' : 0 ≤ ⟪(neg (w 2)).1, y.1⟫_ℝ ↔ ¬ 0 ≤ ⟪(w 2).1, y.1⟫_ℝ := by
      rw [hnegVal, inner_neg_left]; exact ⟨fun h hle => h2ne (by linarith), fun h => by linarith⟩
    classical
    dsimp [f, g]
    have htw : (triSet w).indicator (fun _ => (1 : ℝ)) y = if y ∈ triSet w then 1 else 0 :=
      Set.indicator_apply _ _ _
    have htwn : (triSet wNeg).indicator (fun _ => (1 : ℝ)) y =
        if y ∈ triSet wNeg then 1 else 0 := Set.indicator_apply _ _ _
    rw [htw, htwn]
    simp only [Set.indicator_apply, dbl, lune, Set.mem_union, Set.mem_ofPred_eq, htri, htriNeg]
    by_cases h0 : 0 ≤ ⟪(w 0).1, y.1⟫_ℝ <;>
      by_cases h1 : 0 ≤ ⟪(w 1).1, y.1⟫_ℝ <;>
      by_cases h2 : 0 ≤ ⟪(w 2).1, y.1⟫_ℝ <;>
      simp only [h0, h1, h2, h0', h1', h2', not_true_eq_false, not_false_eq_true,
        true_and, and_true, false_and, and_false, or_self, true_or, or_true, false_or, or_false,
        ↓reduceIte] <;>
      norm_num
  have int_ind (s : Set (Metric.sphere (0 : E3) 1)) (hs : MeasurableSet s) :
      Integrable (s.indicator (fun _ => (1 : ℝ))) ν :=
    Integrable.of_bound ((measurable_const.indicator hs).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun y => by by_cases hy : y ∈ s <;> simp [hy])
  have int_ind_eval (s : Set (Metric.sphere (0 : E3) 1)) (hs : MeasurableSet s) :
      ∫ y, s.indicator (fun _ => (1 : ℝ)) y ∂ν = ν.real s := by
    rw [integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one]
  have hIntEq := integral_congr_ae hae
  have hLHS : ∫ y, f y ∂ν =
      ν.real (dbl (w 0) (w 1)) + ν.real (dbl (w 1) (w 2)) + ν.real (dbl (w 2) (w 0)) := by
    let i01 : Integrable (fun y => (dbl (w 0) (w 1)).indicator (fun _ => (1 : ℝ)) y) ν :=
      int_ind _ (hmeasDbl _ _)
    let i12 : Integrable (fun y => (dbl (w 1) (w 2)).indicator (fun _ => (1 : ℝ)) y) ν :=
      int_ind _ (hmeasDbl _ _)
    let i20 : Integrable (fun y => (dbl (w 2) (w 0)).indicator (fun _ => (1 : ℝ)) y) ν :=
      int_ind _ (hmeasDbl _ _)
    calc ∫ y, f y ∂ν
        = ∫ y, ((dbl (w 0) (w 1)).indicator (fun _ => (1 : ℝ)) y +
              (dbl (w 1) (w 2)).indicator (fun _ => (1 : ℝ)) y) +
              (dbl (w 2) (w 0)).indicator (fun _ => (1 : ℝ)) y ∂ν := rfl
      _ = (∫ y, (dbl (w 0) (w 1)).indicator (fun _ => (1 : ℝ)) y +
              (dbl (w 1) (w 2)).indicator (fun _ => (1 : ℝ)) y ∂ν) +
              ∫ y, (dbl (w 2) (w 0)).indicator (fun _ => (1 : ℝ)) y ∂ν :=
            integral_add (i01.add i12) i20
      _ = (∫ y, (dbl (w 0) (w 1)).indicator (fun _ => (1 : ℝ)) y ∂ν +
              ∫ y, (dbl (w 1) (w 2)).indicator (fun _ => (1 : ℝ)) y ∂ν) +
              ∫ y, (dbl (w 2) (w 0)).indicator (fun _ => (1 : ℝ)) y ∂ν := by
            rw [integral_add i01 i12]
      _ = ν.real (dbl (w 0) (w 1)) + ν.real (dbl (w 1) (w 2)) + ν.real (dbl (w 2) (w 0)) := by
            rw [int_ind_eval _ (hmeasDbl _ _), int_ind_eval _ (hmeasDbl _ _),
              int_ind_eval _ (hmeasDbl _ _)]
  have hRHS : ∫ y, g y ∂ν = M + 4 * ν.real (triSet w) := by
    let i1 : Integrable (fun _ : Metric.sphere (0 : E3) 1 => (1 : ℝ)) ν := integrable_const _
    let i2 : Integrable (fun y => 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y) ν :=
      (int_ind _ (triSet_measurableSet w)).const_mul 2
    let i3 : Integrable (fun y => 2 * (triSet wNeg).indicator (fun _ => (1 : ℝ)) y) ν :=
      (int_ind _ hmeasNegTri).const_mul 2
    have hAdd1 : ∫ y, ((1 : ℝ) + 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y) +
          2 * (triSet wNeg).indicator (fun _ => (1 : ℝ)) y ∂ν =
        (∫ y, (1 : ℝ) + 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y ∂ν) +
          ∫ y, 2 * (triSet wNeg).indicator (fun _ => (1 : ℝ)) y ∂ν :=
      integral_add (i1.add i2) i3
    have hAdd2 : ∫ y, (1 : ℝ) + 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y ∂ν =
        (∫ _ : Metric.sphere (0 : E3) 1, (1 : ℝ) ∂ν) +
          ∫ y, 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y ∂ν :=
      integral_add i1 i2
    calc ∫ y, g y ∂ν
        = ∫ y, ((1 : ℝ) + 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y) +
              2 * (triSet wNeg).indicator (fun _ => (1 : ℝ)) y ∂ν := rfl
      _ = (∫ _ : Metric.sphere (0 : E3) 1, (1 : ℝ) ∂ν +
              ∫ y, 2 * (triSet w).indicator (fun _ => (1 : ℝ)) y ∂ν) +
              ∫ y, 2 * (triSet wNeg).indicator (fun _ => (1 : ℝ)) y ∂ν := by
            rw [hAdd1, hAdd2]
      _ = (M + 2 * ν.real (triSet w)) + 2 * ν.real (triSet wNeg) := by
            rw [integral_const, smul_eq_mul, mul_one, integral_const_mul, integral_const_mul,
              int_ind_eval _ (triSet_measurableSet w), int_ind_eval _ hmeasNegTri]
      _ = M + 4 * ν.real (triSet w) := by
            rw [hNegTriEq]; ring
  rw [hLHS, hRHS, hDblReal, hDblReal, hDblReal,
    toSphere_real_lune, toSphere_real_lune, toSphere_real_lune] at hIntEq
  have hGir := Sphere3.girard_algebra_of_lune_count M (ν.real (triSet w))
    (luneAngle (w 0) (w 1)) (luneAngle (w 1) (w 2)) (luneAngle (w 2) (w 0)) (by
      have : 2 * (M * luneAngle (w 0) (w 1) / (2 * Real.pi) +
          M * luneAngle (w 1) (w 2) / (2 * Real.pi) +
          M * luneAngle (w 2) (w 0) / (2 * Real.pi)) =
        2 * (luneAngle (w 0) (w 1) / (2 * Real.pi) * M) +
        2 * (luneAngle (w 1) (w 2) / (2 * Real.pi) * M) +
        2 * (luneAngle (w 2) (w 0) / (2 * Real.pi) * M) := by ring
      linarith [hIntEq])
  dsimp [stdTriArea]
  linarith [hGir]

private lemma dual_basis_pos_E3 (m : Fin 3 → E3) (hm : LinearIndependent ℝ m) :
    ∃ d : Fin 3 → E3, (∀ a : Fin 3, ‖d a‖ = 1) ∧
      (∀ a b : Fin 3, b ≠ a → ⟪m b, d a⟫_ℝ = 0) ∧ (∀ a : Fin 3, 0 < ⟪m a, d a⟫_ℝ) := by
  let φ : E3 →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun x k => ⟪m k, x⟫_ℝ
      map_add' := fun x y => by ext k; exact inner_add_right _ _ _
      map_smul' := fun r x => by ext k; simp [inner_smul_right] }
  have hInj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hperp : ∀ y ∈ Submodule.span ℝ (Set.range m), ⟪y, x⟫_ℝ = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => rcases hz with ⟨k, rfl⟩; exact congrFun hx k
      | zero => simp
      | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
      | smul r a _ ha => simp [inner_smul_left, ha]
    have hTop : Submodule.span ℝ (Set.range m) = ⊤ :=
      hm.span_eq_top_of_card_eq_finrank (by simp [E3])
    have hxSelf : ⟪x, x⟫_ℝ = 0 := hperp x (hTop ▸ Submodule.mem_top)
    rw [real_inner_self_eq_norm_sq] at hxSelf
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hxSelf)
  have hRange : LinearMap.range φ = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hInj).trans (by simp [E3]))
  have hSurj : Function.Surjective φ := LinearMap.range_eq_top.mp hRange
  choose q hq using fun a : Fin 3 => hSurj (fun b : Fin 3 => if b = a then (1 : ℝ) else 0)
  have hqNe : ∀ a : Fin 3, q a ≠ 0 := fun a h => by
    have := congrFun (hq a) a
    simp [φ, h] at this
  refine ⟨fun a => ‖q a‖⁻¹ • q a, ?_, ?_, ?_⟩
  · intro a
    simp [norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hqNe a))]
  · intro a b hba
    rw [real_inner_smul_right]
    have hb0 : ⟪m b, q a⟫_ℝ = 0 := by simpa [φ, hba] using congrFun (hq a) b
    rw [hb0, mul_zero]
  · intro a
    rw [real_inner_smul_right]
    have ha1 : ⟪m a, q a⟫_ℝ = 1 := by simpa [φ] using congrFun (hq a) a
    rw [ha1, mul_one]
    exact inv_pos.mpr (norm_pos_iff.mpr (hqNe a))

theorem stdTriArea_pos (w : Fin 3 → Metric.sphere (0 : E3) 1)
    (hw : LinearIndependent ℝ (fun k : Fin 3 => (w k).1)) :
    0 < stdTriArea w := by
  let ν := (MeasureTheory.volume : Measure E3).toSphere
  have hTri := toSphere_real_triSet w hw
  have hM : 0 < ν.real Set.univ := toSphere_real_univ_pos 3
  obtain ⟨d, _, hd0, hdPos⟩ := dual_basis_pos_E3 (fun k => (w k).1) hw
  let q : E3 := d 0 + d 1 + d 2
  have h0 : 0 < ⟪(w 0).1, q⟫_ℝ := by
    simp only [q, inner_add_right, hd0 1 0 (by decide), hd0 2 0 (by decide), add_zero]
    exact hdPos 0
  have h1 : 0 < ⟪(w 1).1, q⟫_ℝ := by
    simp only [q, inner_add_right, hd0 0 1 (by decide), hd0 2 1 (by decide), zero_add, add_zero]
    exact hdPos 1
  have h2 : 0 < ⟪(w 2).1, q⟫_ℝ := by
    simp only [q, inner_add_right, hd0 0 2 (by decide), hd0 1 2 (by decide), zero_add]
    exact hdPos 2
  have hqkPos : ∀ k : Fin 3, 0 < ⟪(w k).1, q⟫_ℝ := fun k => by
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hqNe : q ≠ 0 := fun h => by
    have := hqkPos 0
    simp [h] at this
  let u : E3 := ‖q‖⁻¹ • q
  have huNorm : ‖u‖ = 1 := by
    simp [u, norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hqNe)]
  have huPos : ∀ k : Fin 3, 0 < ⟪(w k).1, u⟫_ℝ := fun k => by
    rw [real_inner_smul_right]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hqNe)) (hqkPos k)
  let U : Set (Metric.sphere (0 : E3) 1) := {y | ∀ k : Fin 3, 0 < ⟪(w k).1, y.1⟫_ℝ}
  have hUSub : U ⊆ triSet w := fun y hy k => (hy k).le
  have hUm : MeasurableSet U := by
    have hOpen : IsOpen U := by
      have hEqU : U = ⋂ k : Fin 3, {y : Metric.sphere (0 : E3) 1 | 0 < ⟪(w k).1, y.1⟫_ℝ} := by
        ext; simp [U]
      rw [hEqU]
      exact isOpen_iInter_of_finite fun k =>
        isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
    exact hOpen.measurableSet
  have hUVol : 0 < (MeasureTheory.volume : Measure E3).real (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U)) := by
    let V : Set E3 := {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ ∀ k : Fin 3, 0 < ⟪(w k).1, x⟫_ℝ}
    have hEqV : {x : E3 | ∀ k : Fin 3, 0 < ⟪(w k).1, x⟫_ℝ} =
        ⋂ k : Fin 3, {x : E3 | 0 < ⟪(w k).1, x⟫_ℝ} := by ext; simp
    have hVOpen : IsOpen V :=
      (isOpen_lt continuous_const continuous_norm).inter
        ((isOpen_lt continuous_norm continuous_const).inter
          (by
            change IsOpen {x : E3 | ∀ k : Fin 3, 0 < ⟪(w k).1, x⟫_ℝ}
            rw [hEqV]
            exact isOpen_iInter_of_finite fun k =>
              isOpen_lt continuous_const (continuous_const.inner continuous_id)))
    have hVNonempty : V.Nonempty := by
      refine ⟨(1 / 2 : ℝ) • u, ?_⟩
      simp only [V, Set.mem_ofPred_eq, norm_smul, huNorm, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_one]
      refine ⟨by norm_num, by norm_num, fun k => ?_⟩
      rw [real_inner_smul_right]
      exact mul_pos (by norm_num) (huPos k)
    have hVSub : V ⊆ Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U) := by
      rintro x ⟨hx0, hx1, hxk⟩
      let r := ‖x‖
      have hrPos : 0 < r := hx0
      refine ⟨r, ⟨hrPos, hx1⟩, r⁻¹ • x, ⟨⟨r⁻¹ • x, ?_⟩, ?_, rfl⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hrPos.ne']
      · intro k
        rw [real_inner_smul_right]
        exact mul_pos (inv_pos.mpr hrPos) (hxk k)
      · change r • (r⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hrPos.ne', one_smul]
    have hVPos : (0 : ℝ≥0∞) < (MeasureTheory.volume : Measure E3) V :=
      hVOpen.measure_pos _ hVNonempty
    have hVTop : (MeasureTheory.volume : Measure E3) (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U)) ≠ ⊤ := by
      have hSubBall : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' U) ⊆ Metric.ball (0 : E3) 1 := by
        rintro x ⟨r, hr, y, ⟨z, _, rfl⟩, rfl⟩
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
        have hz : ‖z.1‖ = 1 := by simpa using z.2
        rw [hz, mul_one]
        exact hr.2
      exact (lt_of_le_of_lt (measure_mono hSubBall) MeasureTheory.measure_ball_lt_top).ne
    rw [measureReal_def]
    exact ENNReal.toReal_pos (lt_of_lt_of_le hVPos (measure_mono hVSub)).ne' hVTop
  have hTriPos : 0 < ν.real (triSet w) := by
    have hUPos : 0 < ν.real U := by
      have h3 : ((3 : ℕ) : ℝ≥0∞).toReal = 3 := by simp
      rw [measureReal_def, Measure.toSphere_apply' (MeasureTheory.volume : Measure E3) hUm,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, h3, ← measureReal_def]
      exact mul_pos (by norm_num) hUVol
    exact lt_of_lt_of_le hUPos (by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hUSub))
  rw [hTri] at hTriPos
  rcases mul_pos_iff.mp hTriPos with ⟨_, h⟩ | ⟨hneg, _⟩
  · exact h
  · have hnn : 0 ≤ ν.real Set.univ / (4 * Real.pi) := div_nonneg measureReal_nonneg (by positivity)
    linarith

end LuneAndGirard

section TetrahedronFacesAndPerimeter

/-- Scale factor relating `SphericalTetrahedron.measure 2` to standard `4π`-normalized `S²` excess area. -/
def faceScale : ℝ :=
  sphereScale 2 * ((MeasureTheory.volume : Measure E3).toSphere).real Set.univ / (4 * Real.pi)

theorem faceScale_pos : 0 < faceScale :=
  div_pos (mul_pos (sphereScale_pos (by norm_num)) (toSphere_real_univ_pos 3)) (by positivity)

/-- Orthogonal projection of `T.normal j` onto `(T.normal i)ᗮ`. -/
def projNormal (T : SphericalTetrahedron) (i j : Fin 4) : E4 :=
  T.normal j - ⟪T.normal i, T.normal j⟫_ℝ • T.normal i

theorem projNormal_ne_zero (T : SphericalTetrahedron) {i j : Fin 4} (hij : i ≠ j) :
    projNormal T i j ≠ 0 := by
  intro h0
  have hdep : (1 : ℝ) • T.normal j + (-⟪T.normal i, T.normal j⟫_ℝ) • T.normal i = 0 := by
    simpa [projNormal, sub_eq_add_neg, neg_smul] using h0
  have := linearIndependent_iff'.mp T.independent ({i, j} : Finset (Fin 4))
    (fun k => if k = j then 1 else -⟪T.normal i, T.normal j⟫_ℝ)
  have hsum : ∑ k ∈ ({i, j} : Finset (Fin 4)),
      (if k = j then (1 : ℝ) else -⟪T.normal i, T.normal j⟫_ℝ) • T.normal k = 0 := by
    rw [Finset.sum_pair hij]
    simp only [hij, ↓reduceIte]
    rw [add_comm]
    exact hdep
  have hcoeff := this hsum j (by simp)
  simp at hcoeff

/-- Unit inward normal of edge `(i, j)` in face `i`. -/
def unitProjNormal (T : SphericalTetrahedron) (i j : Fin 4) : E4 :=
  ‖projNormal T i j‖⁻¹ • projNormal T i j

theorem unitProjNormal_norm (T : SphericalTetrahedron) {i j : Fin 4} (hij : i ≠ j) :
    ‖unitProjNormal T i j‖ = 1 := by
  simp [unitProjNormal, norm_smul, norm_inv,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (projNormal_ne_zero T hij))]

theorem unitProjNormal_inner_normal (T : SphericalTetrahedron) (i j : Fin 4) :
    ⟪T.normal i, unitProjNormal T i j⟫_ℝ = 0 := by
  simp only [unitProjNormal, projNormal, inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, T.unit i, one_pow, mul_one, sub_self, mul_zero]

/-- Interior angle of face `i` between edges `(i, j)` and `(i, k)`. -/
def faceAngle (T : SphericalTetrahedron) (i j k : Fin 4) : ℝ :=
  Real.arccos (-⟪unitProjNormal T i j, unitProjNormal T i k⟫_ℝ)

theorem faceAngle_comm (T : SphericalTetrahedron) (i j k : Fin 4) :
    faceAngle T i j k = faceAngle T i k j := by
  simp only [faceAngle, real_inner_comm]

/-- Standard Girard excess area of `T.face i`. -/
def stdFaceArea (T : SphericalTetrahedron) (i : Fin 4) : ℝ :=
  faceAngle T i (i.succAbove 0) (i.succAbove 1) +
  faceAngle T i (i.succAbove 1) (i.succAbove 2) +
  faceAngle T i (i.succAbove 2) (i.succAbove 0) - Real.pi

/-- Total standard `S²`-normalized boundary area of `T`. -/
def stdArea (T : SphericalTetrahedron) : ℝ :=
  ∑ i : Fin 4, stdFaceArea T i

private def embedE3 : E3 →ₗᵢ[ℝ] E4 :=
  { toFun := fun y => WithLp.toLp 2 (Fin.cons 0 y.ofLp)
    map_add' := fun x y => by ext i; refine Fin.cases (by simp) (fun j => by simp) i
    map_smul' := fun r x => by ext i; refine Fin.cases (by simp) (fun j => by simp) i
    norm_map' := fun x => by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, PiLp.inner_apply, PiLp.inner_apply]
      simp [Fin.sum_univ_succ] }

private def drop0 : E4 →ₗ[ℝ] E3 :=
  { toFun := fun x => WithLp.toLp 2 fun k : Fin 3 => x k.succ
    map_add' := fun x y => by ext k; rfl
    map_smul' := fun r x => by ext k; rfl }

private lemma exists_ortho_iso_E3 (n₀ : E4) (hn₀ : ‖n₀‖ = 1) :
    ∃ Φ : E3 →ₗᵢ[ℝ] E4,
      (∀ y : E3, ⟪n₀, Φ y⟫_ℝ = 0) ∧
      (∀ x : E4, ⟪n₀, x⟫_ℝ = 0 → ∃ y : E3, Φ y = x) := by
  let e0vec : E4 := WithLp.toLp 2 (fun m : Fin 4 => if m = 0 then (1 : ℝ) else 0)
  have he0norm : ‖e0vec‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
      PiLp.inner_apply]
    simp [e0vec, Fin.sum_univ_four]
  let e0 : Metric.sphere (0 : E4) 1 := ⟨e0vec, by simpa [Metric.mem_sphere, dist_zero_right] using he0norm⟩
  let nv : Metric.sphere (0 : E4) 1 := ⟨n₀, by simpa [Metric.mem_sphere, dist_zero_right] using hn₀⟩
  obtain ⟨g, hg⟩ := oGroup_transitive_sphere e0 nv
  have hg0 : (orthoEquiv g) e0vec = n₀ := congrArg Subtype.val hg
  let Φ : E3 →ₗᵢ[ℝ] E4 := (orthoEquiv g).toLinearIsometry.comp embedE3
  refine ⟨Φ, ?_, ?_⟩
  · intro y
    rw [← hg0]
    simp only [Φ, LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.inner_map_map]
    rw [PiLp.inner_apply]
    simp [e0vec, embedE3, Fin.sum_univ_four]
  · intro x hx
    let z := (orthoEquiv g).symm x
    have hz0 : z 0 = 0 := by
      have : ⟪e0vec, z⟫_ℝ = 0 := by
        calc ⟪e0vec, z⟫_ℝ = ⟪(orthoEquiv g) e0vec, (orthoEquiv g) z⟫_ℝ :=
              ((orthoEquiv g).inner_map_map _ _).symm
          _ = ⟪n₀, x⟫_ℝ := by rw [hg0]; simp [z]
          _ = 0 := hx
      rw [PiLp.inner_apply] at this
      simpa [e0vec, Fin.sum_univ_four] using this
    refine ⟨drop0 z, ?_⟩
    have hemb : embedE3 (drop0 z) = z := by
      ext m
      refine Fin.cases ?_ (fun _ => rfl) m
      simpa [embedE3] using hz0.symm
    simp [Φ, hemb, z]

private lemma exists_face_triSet (T : SphericalTetrahedron) (i : Fin 4) :
    ∃ (Φ : E3 →ₗᵢ[ℝ] E4) (w : Fin 3 → Metric.sphere (0 : E3) 1),
      LinearIndependent ℝ (fun k : Fin 3 => (w k).1) ∧
      Φ '' (Subtype.val '' triSet w) = T.face i ∧
      stdTriArea w = stdFaceArea T i := by
  obtain ⟨Φ, hPhiOrtho, hPhiSurj⟩ := exists_ortho_iso_E3 (T.normal i) (T.unit i)
  choose wVec hwSpec using fun k : Fin 3 =>
    hPhiSurj _ (unitProjNormal_inner_normal T i (i.succAbove k))
  have hwInner (k : Fin 3) (y : E3) :
      ⟪wVec k, y⟫_ℝ = ⟪unitProjNormal T i (i.succAbove k), Φ y⟫_ℝ := by
    rw [← Φ.inner_map_map, hwSpec k]
  have hwNorm (k : Fin 3) : ‖wVec k‖ = 1 := by
    rw [← Φ.norm_map, hwSpec k]
    exact unitProjNormal_norm T (i.succAbove_ne k).symm
  let w : Fin 3 → Metric.sphere (0 : E3) 1 := fun k =>
    ⟨wVec k, by simpa [Metric.mem_sphere, dist_zero_right] using hwNorm k⟩
  have hwInd : LinearIndependent ℝ (fun k : Fin 3 => (w k).1) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hUp0 : ∑ m : Fin 3, c m • unitProjNormal T i (i.succAbove m) = 0 := by
      have hmap := congrArg Φ hc
      simp only [map_sum, map_smul, map_zero] at hmap
      simpa only [w, hwSpec] using hmap
    let a : Fin 4 → ℝ := fun j =>
      if h : j = i then
        - ∑ m : Fin 3, (c m * ‖projNormal T i (i.succAbove m)‖⁻¹) * ⟪T.normal i, T.normal (i.succAbove m)⟫_ℝ
      else
        let m := Classical.choose (Fin.exists_succAbove_eq h)
        c m * ‖projNormal T i j‖⁻¹
    have hcoeff : ∀ m : Fin 3, a (i.succAbove m) = c m * ‖projNormal T i (i.succAbove m)‖⁻¹ := by
      intro m
      have hne : i.succAbove m ≠ i := i.succAbove_ne m
      simp only [a, dif_neg hne]
      have hm : i.succAbove (Classical.choose (Fin.exists_succAbove_eq hne)) = i.succAbove m :=
        Classical.choose_spec (Fin.exists_succAbove_eq hne)
      rw [Fin.succAbove_right_injective hm]
    have hfull : ∑ j : Fin 4, a j • T.normal j = 0 := by
      rw [Fin.sum_univ_succAbove _ i]
      simp_rw [hcoeff]
      have hdecomp : ∑ m : Fin 3, (c m * ‖projNormal T i (i.succAbove m)‖⁻¹) • T.normal (i.succAbove m) =
          (∑ m : Fin 3, c m • unitProjNormal T i (i.succAbove m)) +
          (∑ m : Fin 3, (c m * ‖projNormal T i (i.succAbove m)‖⁻¹) *
            ⟪T.normal i, T.normal (i.succAbove m)⟫_ℝ) • T.normal i := by
        simp only [unitProjNormal, projNormal, smul_sub, smul_smul, Finset.sum_sub_distrib,
          ← Finset.sum_smul]
        simp only [smul_eq_mul, neg_one_mul, neg_smul, mul_assoc]
        abel
      rw [hdecomp, hUp0, zero_add]
      dsimp [a]
      simp [neg_smul]
    have ha0 := Fintype.linearIndependent_iff.mp T.independent a hfull (i.succAbove k)
    rw [hcoeff k] at ha0
    exact (mul_eq_zero.mp ha0).resolve_right
      (inv_ne_zero (norm_ne_zero_iff.mpr (projNormal_ne_zero T (i.succAbove_ne k).symm)))
  have hFaceImg : Φ '' (Subtype.val '' triSet w) = T.face i := by
    ext x
    simp only [Set.mem_image, triSet, Set.mem_ofPred_eq, SphericalTetrahedron.face,
      SphericalTetrahedron.body]
    constructor
    · rintro ⟨_, ⟨y, hyTri, rfl⟩, rfl⟩
      have hy1 : ‖y.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.2
      refine ⟨⟨by simpa [Φ.norm_map] using hy1, ?_⟩, hPhiOrtho y.1⟩
      intro j
      by_cases hji : j = i
      · subst hji; exact (hPhiOrtho y.1).ge
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hpos : 0 < ‖projNormal T i (i.succAbove k)‖ :=
          norm_pos_iff.mpr (projNormal_ne_zero T (i.succAbove_ne k).symm)
        have hinn : ⟪T.normal (i.succAbove k), Φ y.1⟫_ℝ =
            ‖projNormal T i (i.succAbove k)‖ * ⟪wVec k, y.1⟫_ℝ := by
          rw [hwInner k y.1]
          have hni : ⟪T.normal i, Φ y.1⟫_ℝ = 0 := hPhiOrtho y.1
          have hpos' :
              ‖T.normal (i.succAbove k) - ⟪T.normal i, T.normal (i.succAbove k)⟫_ℝ • T.normal i‖ ≠ 0 := by
            simpa [projNormal] using hpos.ne'
          simp only [unitProjNormal, projNormal, real_inner_smul_left, inner_sub_left,
            hni, mul_zero, sub_zero]
          rw [mul_inv_cancel_left₀ hpos']
        rw [hinn]
        exact mul_nonneg hpos.le (hyTri k)
    · rintro ⟨⟨hx1, hxn⟩, hxi⟩
      obtain ⟨y, rfl⟩ := hPhiSurj x hxi
      have hy1 : ‖y‖ = 1 := by simpa [Φ.norm_map] using hx1
      let ys : Metric.sphere (0 : E3) 1 :=
        ⟨y, by simpa [Metric.mem_sphere, dist_zero_right] using hy1⟩
      refine ⟨y, ⟨ys, fun k => ?_, rfl⟩, rfl⟩
      have hpos : 0 < ‖projNormal T i (i.succAbove k)‖ :=
        norm_pos_iff.mpr (projNormal_ne_zero T (i.succAbove_ne k).symm)
      change 0 ≤ ⟪wVec k, y⟫_ℝ
      rw [hwInner k y]
      simp only [unitProjNormal, projNormal, real_inner_smul_left, inner_sub_left,
        hxi, mul_zero, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr hpos.le) (hxn (i.succAbove k))
  have hTriAreaEq : stdTriArea w = stdFaceArea T i := by
    have hwin (a b : Fin 3) : ⟪(w a).1, (w b).1⟫_ℝ =
        ⟪unitProjNormal T i (i.succAbove a), unitProjNormal T i (i.succAbove b)⟫_ℝ := by
      rw [← Φ.inner_map_map, hwSpec a, hwSpec b]
    simp only [stdTriArea, stdFaceArea, luneAngle, faceAngle, hwin]
  exact ⟨Φ, w, hwInd, hFaceImg, hTriAreaEq⟩

theorem measure_face_eq_faceScale_mul_stdFaceArea (T : SphericalTetrahedron) (i : Fin 4) :
    SphericalTetrahedron.measure 2 (T.face i) = faceScale * stdFaceArea T i := by
  obtain ⟨Φ, w, hwInd, hFaceImg, hTriAreaEq⟩ := exists_face_triSet T i
  have hSub3 : Subtype.val '' triSet w ⊆ Metric.sphere (0 : E3) 1 := by
    rintro _ ⟨y, _, rfl⟩; exact y.2
  have hMeas3 : MeasurableSet (Subtype.val '' triSet w) :=
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).measurableSet_image.mpr
      (triSet_measurableSet w)
  have hpre3 : Subtype.val ⁻¹' (Subtype.val '' triSet w) = triSet w :=
    Subtype.val_injective.preimage_image _
  have hcast2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [SphericalTetrahedron.measure, ← hFaceImg,
    Φ.isometry.hausdorffMeasure_image (Or.inl (by norm_num)) _,
    ← hcast2,
    hausdorffMeasure_real_eq_scale_mul_toSphere (d := 2) (by norm_num) hSub3 hMeas3,
    hpre3, toSphere_real_triSet w hwInd, hTriAreaEq]
  dsimp [faceScale]
  ring

theorem stdFaceArea_pos (T : SphericalTetrahedron) (i : Fin 4) : 0 < stdFaceArea T i := by
  obtain ⟨_, w, hwInd, _, hTriAreaEq⟩ := exists_face_triSet T i
  rw [← hTriAreaEq]
  exact stdTriArea_pos w hwInd

theorem area_eq_faceScale_mul_stdArea (T : SphericalTetrahedron) :
    T.area = faceScale * stdArea T := by
  simp only [SphericalTetrahedron.area, stdArea, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => measure_face_eq_faceScale_mul_stdFaceArea T i

private lemma orthonormal3_decomp (b : Fin 3 → E3)
    (hb : ∀ p q : Fin 3, ⟪b p, b q⟫_ℝ = if p = q then 1 else 0) (z : E3) :
    z = ∑ p : Fin 3, ⟪b p, z⟫_ℝ • b p := by
  have hbInd : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    have h0 := congrArg (fun x : E3 => ⟪b p, x⟫_ℝ) hc
    simp only [inner_sum, inner_smul_right, hb, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, inner_zero_right] at h0
    exact h0
  have hTop : Submodule.span ℝ (Set.range b) = ⊤ :=
    hbInd.span_eq_top_of_card_eq_finrank (by simp [E3])
  let r : E3 := z - ∑ p : Fin 3, ⟪b p, z⟫_ℝ • b p
  have hrB : ∀ p : Fin 3, ⟪b p, r⟫_ℝ = 0 := by
    intro p
    simp only [r, inner_sub_right, inner_sum, inner_smul_right, hb, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sub_self]
  have hrAll : ∀ y : E3, ⟪y, r⟫_ℝ = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range b) := hTop ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => rcases hx with ⟨p, rfl⟩; exact hrB p
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => simp [inner_add_left, h₁, h₂]
    | smul c x _ hx => simp [inner_smul_left, hx]
  have hrr : ⟪r, r⟫_ℝ = 0 := hrAll r
  rw [real_inner_self_eq_norm_sq] at hrr
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hrr))

private lemma two_plane_dual_inner {a u w eu ew : E3}
    (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (heu : ‖eu‖ = 1) (hew : ‖ew‖ = 1)
    (hau : ⟪a, u⟫_ℝ = 0) (haw : ⟪a, w⟫_ℝ = 0) (haeu : ⟪a, eu⟫_ℝ = 0) (haew : ⟪a, ew⟫_ℝ = 0)
    (hueu : ⟪u, eu⟫_ℝ = 0) (hwew : ⟪w, ew⟫_ℝ = 0)
    (hweu : 0 < ⟪w, eu⟫_ℝ) (huew : 0 < ⟪u, ew⟫_ℝ) :
    ⟪eu, ew⟫_ℝ = -⟪u, w⟫_ℝ := by
  have heua : ⟪eu, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact haeu
  have hewa : ⟪ew, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact haew
  have hua : ⟪u, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact hau
  have hwa : ⟪w, a⟫_ℝ = 0 := by rw [real_inner_comm]; exact haw
  have heuu : ⟪eu, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hueu
  have heww : ⟪ew, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hwew
  have hwDecomp : w = ⟪u, w⟫_ℝ • u + ⟪eu, w⟫_ℝ • eu := by
    let b : Fin 3 → E3 := fun p => match p with | 0 => a | 1 => u | 2 => eu
    have hb : ∀ p q : Fin 3, ⟪b p, b q⟫_ℝ = if p = q then 1 else 0 := by
      have haa : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
      have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
      have heu2 : ⟪eu, eu⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, heu, one_pow]
      intro p q
      fin_cases p <;> fin_cases q <;>
        simp only [b, haa, huu, heu2, hau, hua, haeu, heua, hueu, heuu] <;> simp
    have hsum := orthonormal3_decomp b hb w
    rw [Fin.sum_univ_three] at hsum
    simpa [b, haw, zero_smul, zero_add] using hsum
  have huDecomp : u = ⟪w, u⟫_ℝ • w + ⟪ew, u⟫_ℝ • ew := by
    let b : Fin 3 → E3 := fun p => match p with | 0 => a | 1 => w | 2 => ew
    have hb : ∀ p q : Fin 3, ⟪b p, b q⟫_ℝ = if p = q then 1 else 0 := by
      have haa : ⟪a, a⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
      have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
      have hew2 : ⟪ew, ew⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hew, one_pow]
      intro p q
      fin_cases p <;> fin_cases q <;>
        simp only [b, haa, hww, hew2, haw, hwa, haew, hewa, hwew, heww] <;> simp
    have hsum := orthonormal3_decomp b hb u
    rw [Fin.sum_univ_three] at hsum
    simpa [b, hau, zero_smul, zero_add] using hsum
  have hsq1 : ⟪u, w⟫_ℝ ^ 2 + ⟪eu, w⟫_ℝ ^ 2 = 1 := by
    have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have heu2 : ⟪eu, eu⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, heu, one_pow]
    calc ⟪u, w⟫_ℝ ^ 2 + ⟪eu, w⟫_ℝ ^ 2
        = ⟪⟪u, w⟫_ℝ • u + ⟪eu, w⟫_ℝ • eu, ⟪u, w⟫_ℝ • u + ⟪eu, w⟫_ℝ • eu⟫_ℝ := by
            simp only [inner_add_left, inner_add_right, real_inner_smul_left,
              real_inner_smul_right, huu, heu2, hueu, heuu, mul_zero, add_zero, zero_add]
            ring
      _ = ⟪w, w⟫_ℝ := by rw [← hwDecomp]
      _ = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
  have hsq2 : ⟪w, u⟫_ℝ ^ 2 + ⟪ew, u⟫_ℝ ^ 2 = 1 := by
    have hww : ⟪w, w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
    have hew2 : ⟪ew, ew⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hew, one_pow]
    calc ⟪w, u⟫_ℝ ^ 2 + ⟪ew, u⟫_ℝ ^ 2
        = ⟪⟪w, u⟫_ℝ • w + ⟪ew, u⟫_ℝ • ew, ⟪w, u⟫_ℝ • w + ⟪ew, u⟫_ℝ • ew⟫_ℝ := by
            simp only [inner_add_left, inner_add_right, real_inner_smul_left,
              real_inner_smul_right, hww, hew2, hwew, heww, mul_zero, add_zero, zero_add]
            ring
      _ = ⟪u, u⟫_ℝ := by rw [← huDecomp]
      _ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have heuPos : 0 < ⟪eu, w⟫_ℝ := by rwa [real_inner_comm]
  have hewPos : 0 < ⟪ew, u⟫_ℝ := by rwa [real_inner_comm]
  have heqSq : ⟪eu, w⟫_ℝ ^ 2 = ⟪ew, u⟫_ℝ ^ 2 := by
    have hwu : ⟪w, u⟫_ℝ = ⟪u, w⟫_ℝ := real_inner_comm _ _
    rw [hwu] at hsq2
    linarith
  have heq : ⟪ew, u⟫_ℝ = ⟪eu, w⟫_ℝ := by
    have hmul0 : (⟪ew, u⟫_ℝ - ⟪eu, w⟫_ℝ) * (⟪ew, u⟫_ℝ + ⟪eu, w⟫_ℝ) = 0 := by
      calc (⟪ew, u⟫_ℝ - ⟪eu, w⟫_ℝ) * (⟪ew, u⟫_ℝ + ⟪eu, w⟫_ℝ)
          = ⟪ew, u⟫_ℝ ^ 2 - ⟪eu, w⟫_ℝ ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr heqSq.symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul0).resolve_right (by positivity))
  have hpair : 0 = ⟪eu, w⟫_ℝ * (⟪u, w⟫_ℝ + ⟪eu, ew⟫_ℝ) := by
    calc 0 = ⟪eu, u⟫_ℝ := heuu.symm
      _ = ⟪eu, ⟪w, u⟫_ℝ • w + ⟪ew, u⟫_ℝ • ew⟫_ℝ := by rw [← huDecomp]
      _ = ⟪w, u⟫_ℝ * ⟪eu, w⟫_ℝ + ⟪ew, u⟫_ℝ * ⟪eu, ew⟫_ℝ := by
            simp only [inner_add_right, inner_smul_right]
      _ = ⟪eu, w⟫_ℝ * (⟪u, w⟫_ℝ + ⟪eu, ew⟫_ℝ) := by
            rw [heq, real_inner_comm w u]; ring
  have hsum0 : ⟪u, w⟫_ℝ + ⟪eu, ew⟫_ℝ = 0 :=
    (mul_eq_zero.mp hpair.symm).resolve_left heuPos.ne'
  linarith

private lemma vertex_link_sum_lt_two_pi (T : SphericalTetrahedron) (l : Fin 4) :
    faceAngle T (l.succAbove 0) (l.succAbove 1) (l.succAbove 2) +
    faceAngle T (l.succAbove 1) (l.succAbove 2) (l.succAbove 0) +
    faceAngle T (l.succAbove 2) (l.succAbove 0) (l.succAbove 1) < 2 * Real.pi := by
  obtain ⟨Φ, hPhiOrtho, hPhiSurj⟩ := exists_ortho_iso_E3 (T.dualVertex l) (T.dualVertex_norm l)
  have hnv (a : Fin 3) : ⟪T.dualVertex l, T.normal (l.succAbove a)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact T.dualVertex_offdiag (l.succAbove a) l (l.succAbove_ne a)
  choose m hmSpec using fun a : Fin 3 => hPhiSurj _ (hnv a)
  have hmNorm (a : Fin 3) : ‖m a‖ = 1 := by
    rw [← Φ.norm_map, hmSpec a]
    exact T.unit (l.succAbove a)
  have hmInd : LinearIndependent ℝ m := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have hc4 : ∑ mIdx : Fin 3, c mIdx • T.normal (l.succAbove mIdx) = 0 := by
      have hmap := congrArg Φ hc
      simp only [map_sum, map_smul, map_zero, hmSpec] at hmap
      exact hmap
    let coeff : Fin 4 → ℝ := fun j =>
      if h : j = l then 0 else c (Classical.choose (Fin.exists_succAbove_eq h))
    have hsum4 : ∑ j : Fin 4, coeff j • T.normal j = 0 := by
      rw [Fin.sum_univ_succAbove _ l]
      have hdl : coeff l = 0 := by simp [coeff]
      have hsucc (a : Fin 3) : coeff (l.succAbove a) = c a := by
        have hne : l.succAbove a ≠ l := l.succAbove_ne a
        simp only [coeff, dif_neg hne]
        have ha : l.succAbove (Classical.choose (Fin.exists_succAbove_eq hne)) = l.succAbove a :=
          Classical.choose_spec (Fin.exists_succAbove_eq hne)
        rw [Fin.succAbove_right_injective ha]
      simp_rw [hdl, zero_smul, zero_add, hsucc]
      exact hc4
    have h0 := Fintype.linearIndependent_iff.mp T.independent coeff hsum4 (l.succAbove k)
    have hsucck : coeff (l.succAbove k) = c k := by
      have hne : l.succAbove k ≠ l := l.succAbove_ne k
      simp only [coeff, dif_neg hne]
      have hk : l.succAbove (Classical.choose (Fin.exists_succAbove_eq hne)) = l.succAbove k :=
        Classical.choose_spec (Fin.exists_succAbove_eq hne)
      rw [Fin.succAbove_right_injective hk]
    rwa [hsucck] at h0
  obtain ⟨d, hdNorm, hdZero, hdPos⟩ := dual_basis_pos_E3 m hmInd
  have hdInd : LinearIndependent ℝ d := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have h0 := congrArg (fun x : E3 => ⟪m a, x⟫_ℝ) hc
    rw [inner_sum, inner_zero_right] at h0
    have hterm : ∀ b : Fin 3, ⟪m a, c b • d b⟫_ℝ = if b = a then c a * ⟪m a, d a⟫_ℝ else 0 := by
      intro b
      rw [inner_smul_right]
      by_cases hba : b = a
      · subst hba; simp
      · simp [hba, hdZero b a (Ne.symm hba)]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
    exact (mul_eq_zero.mp h0).resolve_right (hdPos a).ne'
  let dS : Fin 3 → Metric.sphere (0 : E3) 1 := fun a =>
    ⟨d a, by simpa [Metric.mem_sphere, dist_zero_right] using hdNorm a⟩
  let projM (a b : Fin 3) : E3 := m b - ⟪m a, m b⟫_ℝ • m a
  have hProjMap (a b : Fin 3) : Φ (projM a b) = T.projNormal (l.succAbove a) (l.succAbove b) := by
    simp only [projM, projNormal, map_sub, map_smul, hmSpec]
    rw [← Φ.inner_map_map (m a) (m b), hmSpec a, hmSpec b]
  have hProjNe {a b : Fin 3} (hab : a ≠ b) : projM a b ≠ 0 := fun h =>
    T.projNormal_ne_zero (Fin.succAbove_right_injective.ne hab) (by rw [← hProjMap, h, map_zero])
  let unitProjM (a b : Fin 3) : E3 := ‖projM a b‖⁻¹ • projM a b
  have hUnitMap {a b : Fin 3} :
      Φ (unitProjM a b) = T.unitProjNormal (l.succAbove a) (l.succAbove b) := by
    simp only [unitProjM, unitProjNormal, map_smul, hProjMap, ← Φ.norm_map]
  have hAngle {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      faceAngle T (l.succAbove a) (l.succAbove b) (l.succAbove c) =
        Real.pi - luneAngle (dS b) (dS c) := by
    have hpab : 0 < ‖projM a b‖ := norm_pos_iff.mpr (hProjNe hab)
    have hpac : 0 < ‖projM a c‖ := norm_pos_iff.mpr (hProjNe hac)
    have humab : ‖unitProjM a b‖ = 1 := by
      simp [unitProjM, norm_smul, norm_inv, inv_mul_cancel₀ hpab.ne']
    have humac : ‖unitProjM a c‖ = 1 := by
      simp [unitProjM, norm_smul, norm_inv, inv_mul_cancel₀ hpac.ne']
    have hau : ⟪m a, unitProjM a b⟫_ℝ = 0 := by
      simp only [unitProjM, projM, inner_smul_right, inner_sub_right,
        real_inner_self_eq_norm_sq, hmNorm a, one_pow, mul_one, sub_self, mul_zero]
    have haw : ⟪m a, unitProjM a c⟫_ℝ = 0 := by
      simp only [unitProjM, projM, inner_smul_right, inner_sub_right,
        real_inner_self_eq_norm_sq, hmNorm a, one_pow, mul_one, sub_self, mul_zero]
    have hudc : ⟪unitProjM a b, d c⟫_ℝ = 0 := by
      simp only [unitProjM, projM, inner_smul_left, inner_sub_left,
        hdZero c b hbc, hdZero c a hac, mul_zero, sub_zero]
    have hwdc : 0 < ⟪unitProjM a c, d c⟫_ℝ := by
      simp only [unitProjM, projM, inner_smul_left, inner_sub_left, hdZero c a hac,
        mul_zero, sub_zero]
      exact mul_pos (inv_pos.mpr hpac) (hdPos c)
    have hwdb : ⟪unitProjM a c, d b⟫_ℝ = 0 := by
      simp only [unitProjM, projM, inner_smul_left, inner_sub_left,
        hdZero b c hbc.symm, hdZero b a hab, mul_zero, sub_zero]
    have hudb : 0 < ⟪unitProjM a b, d b⟫_ℝ := by
      simp only [unitProjM, projM, inner_smul_left, inner_sub_left, hdZero b a hab,
        mul_zero, sub_zero]
      exact mul_pos (inv_pos.mpr hpab) (hdPos b)
    have hdDual := two_plane_dual_inner (hmNorm a) humab humac (hdNorm c) (hdNorm b)
      hau haw (hdZero c a hac) (hdZero b a hab) hudc hwdb hwdc hudb
    have hface : -⟪T.unitProjNormal (l.succAbove a) (l.succAbove b),
        T.unitProjNormal (l.succAbove a) (l.succAbove c)⟫_ℝ = ⟪(dS b).1, (dS c).1⟫_ℝ := by
      calc -⟪T.unitProjNormal (l.succAbove a) (l.succAbove b),
              T.unitProjNormal (l.succAbove a) (l.succAbove c)⟫_ℝ
          = -⟪Φ (unitProjM a b), Φ (unitProjM a c)⟫_ℝ := by rw [hUnitMap, hUnitMap]
        _ = -⟪unitProjM a b, unitProjM a c⟫_ℝ := by rw [Φ.inner_map_map]
        _ = ⟪d c, d b⟫_ℝ := hdDual.symm
        _ = ⟪(dS b).1, (dS c).1⟫_ℝ := by rw [real_inner_comm]
    rw [faceAngle, hface, luneAngle]
    have hneg := Real.arccos_neg (-⟪(dS b).1, (dS c).1⟫_ℝ)
    rw [neg_neg] at hneg
    exact hneg
  have h012 := hAngle (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide)
  have h120 := hAngle (a := 1) (b := 2) (c := 0) (by decide) (by decide) (by decide)
  have h201 := hAngle (a := 2) (b := 0) (c := 1) (by decide) (by decide) (by decide)
  have hTriPos := stdTriArea_pos dS hdInd
  have htriDef : stdTriArea dS =
      luneAngle (dS 0) (dS 1) + luneAngle (dS 1) (dS 2) + luneAngle (dS 2) (dS 0) - Real.pi := rfl
  linarith [h012, h120, h201, hTriPos, htriDef]

theorem stdArea_lt_four_pi (T : SphericalTetrahedron) : stdArea T < 4 * Real.pi := by
  have h0 := vertex_link_sum_lt_two_pi T 0
  have h1 := vertex_link_sum_lt_two_pi T 1
  have h2 := vertex_link_sum_lt_two_pi T 2
  have h3 := vertex_link_sum_lt_two_pi T 3
  have hexp : stdArea T =
      (faceAngle T (Fin.succAbove 0 0) (Fin.succAbove 0 1) (Fin.succAbove 0 2) +
       faceAngle T (Fin.succAbove 0 1) (Fin.succAbove 0 2) (Fin.succAbove 0 0) +
       faceAngle T (Fin.succAbove 0 2) (Fin.succAbove 0 0) (Fin.succAbove 0 1)) +
      (faceAngle T (Fin.succAbove 1 0) (Fin.succAbove 1 1) (Fin.succAbove 1 2) +
       faceAngle T (Fin.succAbove 1 1) (Fin.succAbove 1 2) (Fin.succAbove 1 0) +
       faceAngle T (Fin.succAbove 1 2) (Fin.succAbove 1 0) (Fin.succAbove 1 1)) +
      (faceAngle T (Fin.succAbove 2 0) (Fin.succAbove 2 1) (Fin.succAbove 2 2) +
       faceAngle T (Fin.succAbove 2 1) (Fin.succAbove 2 2) (Fin.succAbove 2 0) +
       faceAngle T (Fin.succAbove 2 2) (Fin.succAbove 2 0) (Fin.succAbove 2 1)) +
      (faceAngle T (Fin.succAbove 3 0) (Fin.succAbove 3 1) (Fin.succAbove 3 2) +
       faceAngle T (Fin.succAbove 3 1) (Fin.succAbove 3 2) (Fin.succAbove 3 0) +
       faceAngle T (Fin.succAbove 3 2) (Fin.succAbove 3 0) (Fin.succAbove 3 1)) -
      4 * Real.pi := by
    simp only [stdArea, Fin.sum_univ_four, stdFaceArea, Fin.succAbove]
    norm_num [Fin.lt_def]
    rw [faceAngle_comm T 0 3 1, faceAngle_comm T 1 0 2, faceAngle_comm T 2 1 3, faceAngle_comm T 3 2 0]
    ring
  linarith [hexp, h0, h1, h2, h3]

end TetrahedronFacesAndPerimeter

end SphericalTetrahedron
