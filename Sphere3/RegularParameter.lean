module

public import Mathlib

@[expose] public section

/-!
# Exact one-parameter functions for regular spherical tetrahedra

This file contains only real-variable statements.  These are the explicit
functions expected to describe the face angles, surface area, edge lengths,
and dihedral angles of the regular family parameterized by the common inner
product `ρ` of the inward unit facet normals.

These are purely real-variable identities; strict monotonicity on the
regular family is proved geometrically via `CanonicalFaceHausdorffStrict`.
-/

noncomputable section

namespace Sphere3

/-- The admissible common normal inner products of a nondegenerate
regular spherical tetrahedron. -/
def regularParameterDomain : Set ℝ := Set.Ioo (-(1 : ℝ) / 3) 1

/-- Cosine of each face angle in a regular tetrahedron with normal
inner product `ρ`. -/
def faceAngleCos (ρ : ℝ) : ℝ := -ρ / (1 + ρ)

/-- Cosine of each edge length in that family. -/
def edgeLengthCos (ρ : ℝ) : ℝ := -ρ / (1 + 2 * ρ)

/-- The surface area of the regular model of parameter `ρ`. -/
def regularAreaModel (ρ : ℝ) : ℝ :=
  4 * (3 * Real.arccos (faceAngleCos ρ) - Real.pi)

/-- The common edge length of the regular model. -/
def regularEdgeLength (ρ : ℝ) : ℝ :=
  Real.arccos (edgeLengthCos ρ)

/-- The common internal dihedral angle of the regular model. -/
def regularDihedralAngle (ρ : ℝ) : ℝ :=
  Real.arccos (-ρ)

private theorem den_one_pos {ρ : ℝ} (hρ : ρ ∈ regularParameterDomain) :
    0 < 1 + ρ := by
  dsimp [regularParameterDomain] at hρ
  linarith [hρ.1]

private theorem den_two_pos {ρ : ℝ} (hρ : ρ ∈ regularParameterDomain) :
    0 < 1 + 2 * ρ := by
  dsimp [regularParameterDomain] at hρ
  linarith [hρ.1]

/-- The face-angle cosine remains strictly between `-1` and `1`. -/
theorem faceAngleCos_mem_Ioo {ρ : ℝ} (hρ : ρ ∈ regularParameterDomain) :
    -1 < faceAngleCos ρ ∧ faceAngleCos ρ < 1 := by
  have hd : 0 < 1 + ρ := den_one_pos hρ
  dsimp [faceAngleCos]
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith
  · apply (div_lt_iff₀ hd).2
    dsimp [regularParameterDomain] at hρ
    nlinarith [hρ.1]

/-- The cosine of the edge length lies strictly between `-1` and `1`. -/
theorem edgeLengthCos_mem_Ioo {ρ : ℝ} (hρ : ρ ∈ regularParameterDomain) :
    -1 < edgeLengthCos ρ ∧ edgeLengthCos ρ < 1 := by
  have hd : 0 < 1 + 2 * ρ := den_two_pos hρ
  dsimp [edgeLengthCos]
  constructor
  · apply (lt_div_iff₀ hd).2
    dsimp [regularParameterDomain] at hρ
    nlinarith [hρ.1]
  · apply (div_lt_iff₀ hd).2
    dsimp [regularParameterDomain] at hρ
    nlinarith [hρ.1]

/-- The face-angle cosine strictly decreases as `ρ` increases. -/
theorem strictAntiOn_faceAngleCos :
    StrictAntiOn faceAngleCos regularParameterDomain := by
  intro a ha b hb hab
  have ha0 : 0 < 1 + a := den_one_pos ha
  have hb0 : 0 < 1 + b := den_one_pos hb
  unfold faceAngleCos
  apply (div_lt_div_iff₀ hb0 ha0).2
  nlinarith

/-- The edge-length cosine strictly decreases as `ρ` increases. -/
theorem strictAntiOn_edgeLengthCos :
    StrictAntiOn edgeLengthCos regularParameterDomain := by
  intro a ha b hb hab
  have ha0 : 0 < 1 + 2 * a := den_two_pos ha
  have hb0 : 0 < 1 + 2 * b := den_two_pos hb
  unfold edgeLengthCos
  apply (div_lt_div_iff₀ hb0 ha0).2
  nlinarith

/-- Model surface area is strictly increasing on the admissible interval. -/
theorem strictMonoOn_regularAreaModel :
    StrictMonoOn regularAreaModel regularParameterDomain := by
  intro a ha b hb hab
  have hcos : faceAngleCos b < faceAngleCos a :=
    strictAntiOn_faceAngleCos ha hb hab
  have hcosb : -1 ≤ faceAngleCos b :=
    (faceAngleCos_mem_Ioo hb).1.le
  have hcosa : faceAngleCos a ≤ 1 :=
    (faceAngleCos_mem_Ioo ha).2.le
  have hang : Real.arccos (faceAngleCos a) <
      Real.arccos (faceAngleCos b) :=
    Real.arccos_lt_arccos hcosb hcos hcosa
  dsimp [regularAreaModel]
  linarith

/-- Distinct admissible parameters have distinct model surface areas. -/
theorem regularAreaModel_injOn :
    Set.InjOn regularAreaModel regularParameterDomain :=
  strictMonoOn_regularAreaModel.injOn

/-- Edge length is strictly increasing on the admissible interval. -/
theorem strictMonoOn_regularEdgeLength :
    StrictMonoOn regularEdgeLength regularParameterDomain := by
  intro a ha b hb hab
  have hcos : edgeLengthCos b < edgeLengthCos a :=
    strictAntiOn_edgeLengthCos ha hb hab
  have hcosb : -1 ≤ edgeLengthCos b :=
    (edgeLengthCos_mem_Ioo hb).1.le
  have hcosa : edgeLengthCos a ≤ 1 :=
    (edgeLengthCos_mem_Ioo ha).2.le
  exact Real.arccos_lt_arccos hcosb hcos hcosa

/-- Dihedral angle is strictly increasing on the admissible interval. -/
theorem strictMonoOn_regularDihedralAngle :
    StrictMonoOn regularDihedralAngle regularParameterDomain := by
  intro a ha b hb hab
  have hneg : -b < -a := by linarith
  have hneglo : -1 ≤ -b := by
    dsimp [regularParameterDomain] at hb
    linarith [hb.2]
  have hneghi : -a ≤ 1 := by
    dsimp [regularParameterDomain] at ha
    linarith [ha.1]
  exact Real.arccos_lt_arccos hneglo hneg hneghi

end Sphere3
