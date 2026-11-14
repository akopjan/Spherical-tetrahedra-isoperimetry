module

public import Sphere3.CanonicalPatch
public import Sphere3.MeasureGrowth
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

/-!
# Strict growth for the canonical family in the natural spherical measure

`Measure.toSphere` is the angular measure obtained by radial disintegration
of four-dimensional Lebesgue measure. Unlike ambient `hausdorffMeasure 3`,
its finiteness and positivity on nonempty open subsets of the unit sphere
are already supplied by Mathlib.

The strict inequality below concerns this natural spherical measure.
-/

noncomputable section

namespace Sphere3

open MeasureTheory

local notation "E4" => EuclideanSpace ℝ (Fin 4)

/-- Unit vectors in four-dimensional Euclidean space, as a subtype. -/
abbrev UnitSphere3 := Metric.sphere (0 : E4) 1

/-- The canonical tetrahedron, regarded as a set in the sphere subtype. -/
def canonicalSphereSubtype (t : ℝ) : Set UnitSphere3 :=
  {p | CanonicalCone t (p.1 0) (p.1 1) (p.1 2) (p.1 3)}

/-- The relatively open spherical patch between two canonical bodies. -/
def canonicalSphereSubtypePatch (t s : ℝ) : Set UnitSphere3 :=
  {p | (p.1 : E4) ∈ canonicalAmbientPatch t s}

theorem canonicalSphereSubtype_mono {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    canonicalSphereSubtype t ⊆ canonicalSphereSubtype s := by
  intro p hp
  exact canonicalCone_mono ht hts hp

theorem canonicalSphereSubtypePatch_subset (t s : ℝ) :
    canonicalSphereSubtypePatch t s ⊆ canonicalSphereSubtype s := by
  intro p hp
  exact canonicalInterior_subset hp.1

theorem canonicalSphereSubtypePatch_disjoint (t s : ℝ) :
    Disjoint (canonicalSphereSubtype t) (canonicalSphereSubtypePatch t s) := by
  apply Set.disjoint_left.mpr
  intro p hp hpatch
  exact hpatch.2 hp

theorem canonicalSphereSubtypePatch_isOpen (t s : ℝ) :
    IsOpen (canonicalSphereSubtypePatch t s) := by
  change IsOpen (Subtype.val ⁻¹' canonicalAmbientPatch t s)
  exact (canonicalAmbientPatch_isOpen t s).preimage continuous_subtype_val

theorem canonicalSphereSubtypePatch_nonempty {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    (canonicalSphereSubtypePatch t s).Nonempty := by
  obtain ⟨x, hx⟩ := canonicalSpherePatch_nonempty ht hts
  have hxSphere : x ∈ (Metric.sphere (0 : E4) 1) := by
    change dist x (0 : E4) = 1
    simpa only [dist_zero_right] using hx.1
  refine ⟨⟨x, hxSphere⟩, ?_⟩
  exact hx.2

/-- Strict growth of radial-angular volume along the canonical family.
This uses no polar-normalization assumption and no custom axiom. -/
theorem canonical_toSphere_strictMono {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    ((volume : Measure E4).toSphere) (canonicalSphereSubtype t) <
      ((volume : Measure E4).toSphere) (canonicalSphereSubtype s) := by
  have hFin : ((volume : Measure E4).toSphere)
      (canonicalSphereSubtype t) ≠ ⊤ := measure_ne_top _ _
  exact measure_lt_of_open_patch ((volume : Measure E4).toSphere)
    (canonicalSphereSubtype_mono ht (le_of_lt hts))
    (canonicalSphereSubtypePatch_subset t s)
    (canonicalSphereSubtypePatch_disjoint t s)
    (canonicalSphereSubtypePatch_isOpen t s)
    (canonicalSphereSubtypePatch_nonempty ht hts)
    hFin

/-- The angular subset of the sphere and its ambient representation
have exactly the same points. -/
theorem canonicalSphereSubtype_image (t : ℝ) :
    Subtype.val '' canonicalSphereSubtype t = canonicalSphereBody t := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    constructor
    · have h := p.property
      change dist (p : E4) (0 : E4) = 1 at h
      simpa only [dist_zero_right] using h
    · exact hp
  · intro hx
    have hSphere : x ∈ (Metric.sphere (0 : E4) 1) := by
      change dist x (0 : E4) = 1
      simpa only [dist_zero_right] using hx.1
    exact ⟨⟨x, hSphere⟩, hx.2, rfl⟩

/-- The real-valued angular volume of the canonical spherical body. -/
def canonicalAngularVolume (t : ℝ) : ℝ :=
  (((volume : Measure E4).toSphere) (canonicalSphereSubtype t)).toReal

/-- Strict growth of angular volume, now as a real-valued function. -/
theorem canonicalAngularVolume_strict {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    canonicalAngularVolume t < canonicalAngularVolume s := by
  unfold canonicalAngularVolume
  exact ENNReal.toReal_strict_mono (measure_ne_top _ _)
    (canonical_toSphere_strictMono ht hts)

/-- The Hausdorff measure in the challenge is not normalized a priori
like `Measure.toSphere`. A POSITIVE MULTIPLICATIVE CONSTANT, not exact
identity, suffices for strict comparison. This is still a conditional
lemma, not a proof of the required measure comparison. -/
theorem canonicalHausdorff_real_strict_of_scaled_bridge {t s : ℝ}
    (ht : 0 < t) (hts : t < s)
    (c : ℝ) (hc : 0 < c)
    (hBridge : ∀ u : ℝ, 0 < u →
      ((Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody u)).toReal =
        c * canonicalAngularVolume u) :
    ((Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody t)).toReal <
      ((Measure.hausdorffMeasure (3 : ℝ)) (canonicalSphereBody s)).toReal := by
  rw [hBridge t ht, hBridge s (lt_trans ht hts)]
  exact mul_lt_mul_of_pos_left (canonicalAngularVolume_strict ht hts) hc

end Sphere3
