module

public import SphericalTetrahedron.CanonicalRealization
public import Sphere3.CanonicalPatch

@[expose] public section

/-!
# Strict geometric expansion in the *actual* spherical tetrahedron family

These are set-theoretic/topological assertions.  Strict inclusion does
NOT yet imply strict Hausdorff-volume monotonicity without an analytic
positivity argument.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace SphericalTetrahedron

/-- Increasing the positive parameter enlarges the genuine body. -/
theorem canonicalTetrahedron_body_mono {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    (canonicalTetrahedron t ht).body ⊆
      (canonicalTetrahedron s (lt_of_lt_of_le ht hts)).body := by
  rw [canonicalTetrahedron_body_eq t ht,
    canonicalTetrahedron_body_eq s (lt_of_lt_of_le ht hts)]
  exact Sphere3.canonicalSphereBody_mono ht hts

/-- For strictly increasing parameters, inclusion is proper, already
on the level of geometric bodies. -/
theorem canonicalTetrahedron_body_strict {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (canonicalTetrahedron t ht).body ⊂
      (canonicalTetrahedron s (lt_trans ht hts)).body := by
  constructor
  · exact canonicalTetrahedron_body_mono ht hts.le
  · intro hReverse
    obtain ⟨x, hxS, hxNotT, _⟩ :=
      Sphere3.canonicalSphereBody_strict_witness ht hts
    have hS : x ∈ (canonicalTetrahedron s (lt_trans ht hts)).body := by
      rw [canonicalTetrahedron_body_eq s (lt_trans ht hts)]
      exact hxS
    have hT : x ∈ (canonicalTetrahedron t ht).body := hReverse hS
    rw [canonicalTetrahedron_body_eq t ht] at hT
    exact hxNotT hT

/-- The proper difference of two genuine bodies contains a nonempty
open patch in the subspace topology of the larger spherical body. -/
def canonicalRealizationPatch {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    Set (canonicalTetrahedron s (lt_trans ht hts)).body :=
  {p | (p.1 : E4) ∈ Sphere3.canonicalAmbientPatch t s}

/-- The patch is open relative to the larger tetrahedron. -/
theorem canonicalRealizationPatch_isOpen {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    IsOpen (canonicalRealizationPatch ht hts) := by
  change IsOpen (Subtype.val ⁻¹' Sphere3.canonicalAmbientPatch t s)
  exact (Sphere3.canonicalAmbientPatch_isOpen t s).preimage
    continuous_subtype_val

/-- The canonical relative patch is inhabited. -/
theorem canonicalRealizationPatch_nonempty {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (canonicalRealizationPatch ht hts).Nonempty := by
  obtain ⟨x, hxS, hxNotSmall, hInterior⟩ :=
    Sphere3.canonicalSphereBody_strict_witness ht hts
  have hx : x ∈ (canonicalTetrahedron s (lt_trans ht hts)).body := by
    rw [canonicalTetrahedron_body_eq s (lt_trans ht hts)]
    exact hxS
  refine ⟨⟨x, hx⟩, ?_⟩
  change Sphere3.CanonicalConeInterior s (x 0) (x 1) (x 2) (x 3) ∧
    ¬ Sphere3.CanonicalCone t (x 0) (x 1) (x 2) (x 3)
  refine ⟨hInterior, ?_⟩
  intro hsmall
  exact hxNotSmall ⟨hxS.1, hsmall⟩

/-- No point of the canonical relative patch belongs to the smaller body. -/
theorem canonicalRealizationPatch_disjoint {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    {p : (canonicalTetrahedron s (lt_trans ht hts)).body}
    (hp : p ∈ canonicalRealizationPatch ht hts) :
    (p.1 : E4) ∉ (canonicalTetrahedron t ht).body := by
  intro hSmall
  have hCone : Sphere3.CanonicalCone t (p.1 0) (p.1 1)
      (p.1 2) (p.1 3) := by
    have hh : (p.1 : E4) ∈ Sphere3.canonicalSphereBody t := by
      rw [← canonicalTetrahedron_body_eq t ht]
      exact hSmall
    exact hh.2
  exact hp.2 hCone

end SphericalTetrahedron
