module

public import SphericalTetrahedron.ManuscriptFirstVariationBridge
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Fixed-area maximizers from a compactification and boundary improvement

The manuscript compactifies *four normals*, with surface area defined as
the genuine geometric boundary area of the limit cone rather than as a
sum of four possibly coalescing labelled faces. On that compactification,
the objective is continuous, and every degenerate maximizer is strictly
improvable by an interior tetrahedron.

This file proves the abstract topological maximization and the exact
transfer back to `SphericalTetrahedron`, supplied with continuity and boundary
bounds by `ManuscriptCompactness` and `ManuscriptBoundaryPerturbation`.
-/

noncomputable section

namespace SphericalTetrahedron

/-- A continuous function on a nonempty compact set achieves its maximum
at an interior point if every noninterior point can be strictly improved. -/
theorem interior_maximizer_of_compact_boundary_improvement
    {X : Type*} [TopologicalSpace X]
    (K : Set X) (volume : X → ℝ) (interior : X → Prop)
    (hK : IsCompact K) (hne : K.Nonempty)
    (hvol : ContinuousOn volume K)
    (himprove : ∀ x ∈ K, ¬ interior x →
      ∃ y ∈ K, volume x < volume y) :
    ∃ x ∈ K, interior x ∧ ∀ y ∈ K, volume y ≤ volume x := by
  obtain ⟨x, hx, hMax⟩ := hK.exists_isMaxOn hne hvol
  have hInterior : interior x := by
    by_contra hNot
    obtain ⟨y, hy, hGreater⟩ := himprove x hx hNot
    exact (not_lt_of_ge (hMax hy)) hGreater
  exact ⟨x, hx, hInterior, fun y hy => hMax hy⟩

/-- A precise interface for Section 5--6 of the manuscript.
The compact space of possibly degenerate normals is `X`; `good` means
that the limit has rank four. The coverage hypothesis embeds every
original fixed-area tetrahedron into the compactified level set.
No analytically difficult assertion is assumed silently. -/
theorem fixed_area_maximizer_of_manuscript_compactification
    (T : SphericalTetrahedron)
    {X : Type*} [TopologicalSpace X]
    (K : Set X) (volume : X → ℝ) (good : X → Prop)
    (hCompact : IsCompact K) (hNonempty : K.Nonempty)
    (hVolContinuous : ContinuousOn volume K)
    (hBoundaryImprove : ∀ x ∈ K, ¬ good x →
      ∃ y ∈ K, volume x < volume y)
    (hRealize : ∀ x ∈ K, good x →
      ∃ M : SphericalTetrahedron,
        M.area = T.area ∧ M.volume = volume x)
    (hCover : ∀ S : SphericalTetrahedron, S.area = T.area →
      ∃ x ∈ K, S.volume = volume x) :
    ∃ M : SphericalTetrahedron,
      M.area = T.area ∧
      ∀ S : SphericalTetrahedron,
        S.area = T.area → S.volume ≤ M.volume := by
  obtain ⟨x, hx, hGood, hMax⟩ :=
    interior_maximizer_of_compact_boundary_improvement
      K volume good hCompact hNonempty hVolContinuous hBoundaryImprove
  obtain ⟨M, hArea, hVol⟩ := hRealize x hx hGood
  refine ⟨M, hArea, ?_⟩
  intro S hSa
  obtain ⟨y, hy, hVy⟩ := hCover S hSa
  calc
    S.volume = volume y := hVy
    _ ≤ volume x := hMax y hy
    _ = M.volume := hVol.symm

end SphericalTetrahedron
