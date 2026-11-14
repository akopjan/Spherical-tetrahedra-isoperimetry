module

public import Sphere3.RadialParameter

@[expose] public section

/-!
# A one-to-one radial coordinate for regular spherical tetrahedra

This file establishes the algebraic parametrization of the admissible
normal Gram values by positive radial scales. It also shows that the
explicit model area is strictly increasing with the radial scale.

These are real-variable lemmas parametrizing the admissible regular Gram
values by positive radial scales.
-/

noncomputable section

namespace Sphere3

/-- The inverse of the regular normal parameter recovers every positive
radial scale. -/
theorem radialScale_radialGramParameter (t : ℝ) (ht : 0 < t) :
    radialScale (radialGramParameter t) = t := by
  have hp : radialGramParameter t ∈ regularParameterDomain :=
    radialGramParameter_mem t ht
  have ht' : 0 < radialScale (radialGramParameter t) :=
    radialScale_pos _ hp
  apply strictMonoOn_radialGramParameter.injOn ht' ht
  exact radialGramParameter_radialScale _ hp

/-- The positive radial scales parameterize the interval of regular Gram
values bijectively. -/
theorem radialGramParameter_bijective :
    Set.BijOn radialGramParameter (Set.Ioi 0) regularParameterDomain := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact radialGramParameter_mem t ht
  · intro x hx y hy hxy
    exact strictMonoOn_radialGramParameter.injOn hx hy hxy
  · intro rho hrho
    refine ⟨radialScale rho, radialScale_pos rho hrho, ?_⟩
    exact radialGramParameter_radialScale rho hrho

/-- The explicit area of a regular model strictly increases under radial
scaling. No statement about geometric Hausdorff area is used. -/
theorem strictMonoOn_radialAreaModel :
    StrictMonoOn (fun t => regularAreaModel (radialGramParameter t))
      (Set.Ioi 0) := by
  intro a ha b hb hab
  exact strictMonoOn_regularAreaModel
    (radialGramParameter_mem a ha)
    (radialGramParameter_mem b hb)
    (strictMonoOn_radialGramParameter ha hb hab)

/-- The common dihedral angle of the regular model increases with radial
scale. -/
theorem strictMonoOn_radialDihedralAngle :
    StrictMonoOn (fun t => regularDihedralAngle (radialGramParameter t))
      (Set.Ioi 0) := by
  intro a ha b hb hab
  exact strictMonoOn_regularDihedralAngle
    (radialGramParameter_mem a ha)
    (radialGramParameter_mem b hb)
    (strictMonoOn_radialGramParameter ha hb hab)

end Sphere3
