module

public import Sphere3.CanonicalGram

@[expose] public section

/-!
# Explicit face-angle and surface-area functions for the canonical regular family

The four facets of the canonical spherical model have identical side
lengths and identical face angles. The following theorems concern these explicit real functions.
-/

noncomputable section

namespace Sphere3

/-- Cosine of the common edge length in the canonical vertex model. -/
def canonicalEdgeCos (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 + 3 * t ^ 2)

/-- Cosine of the common face angle, computed from spherical cosine rule. -/
def canonicalFaceCos (t : ℝ) : ℝ :=
  (1 - t ^ 2) / (2 * (1 + t ^ 2))

/-- The normal-Gram and vertex-Gram expressions for edge length agree. -/
theorem canonicalEdgeCos_eq_normal (t : ℝ) :
    canonicalEdgeCos t = edgeLengthCos (canonicalGramParameter t) := by
  have h1 : t ^ 2 + 3 ≠ 0 := by positivity
  have h2 : 1 + 3 * t ^ 2 ≠ 0 := by positivity
  have h3 : 1 + 2 * ((t ^ 2 - 1) / (t ^ 2 + 3)) = (1 + 3 * t ^ 2) / (t ^ 2 + 3) := by
    field_simp
    ring
  unfold canonicalEdgeCos edgeLengthCos canonicalGramParameter
  rw [h3]
  field_simp
  ring

/-- The spherical cosine-rule expression for face angles agrees with
that obtained directly from the normal Gram parameter. -/
theorem canonicalFaceCos_eq_normal (t : ℝ) :
    canonicalFaceCos t = faceAngleCos (canonicalGramParameter t) := by
  have h1 : t ^ 2 + 3 ≠ 0 := by positivity
  have h2 : 1 + t ^ 2 ≠ 0 := by positivity
  have h3 : 1 + (t ^ 2 - 1) / (t ^ 2 + 3) = (2 * (1 + t ^ 2)) / (t ^ 2 + 3) := by
    field_simp
    ring
  unfold canonicalFaceCos faceAngleCos canonicalGramParameter
  rw [h3]
  field_simp
  ring

/-- The explicit regular-tetrahedron area as a function of the
positive canonical height parameter. -/
def canonicalAreaModel (t : ℝ) : ℝ :=
  4 * (3 * Real.arccos (canonicalFaceCos t) - Real.pi)

theorem canonicalAreaModel_eq_regular (t : ℝ) :
    canonicalAreaModel t = regularAreaModel (canonicalGramParameter t) := by
  rw [canonicalAreaModel, regularAreaModel, canonicalFaceCos_eq_normal]

/-- The *model formula* for area is strictly increasing on positive
parameters. No Hausdorff-measure assertion is used here. -/
theorem canonicalAreaModel_strictMonoOn :
    StrictMonoOn canonicalAreaModel (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [canonicalAreaModel_eq_regular, canonicalAreaModel_eq_regular]
  exact strictMonoOn_regularAreaModel
    (canonicalGramParameter_mem a ha)
    (canonicalGramParameter_mem b hb)
    (canonicalGramParameter_strictMonoOn ha hb hab)

end Sphere3
