module

public import Sphere3.ManuscriptTriangleAlgebra
public import SphericalTetrahedron.StationaryEqualHeights

@[expose] public section

/-!
# The manuscript's four-face rigidity argument

This file gives an exact formal interface between the triangle ordering
lemma of the manuscript and the existing `Stationary`/`Regular` predicates.
The main theorem is CONDITIONAL on the three real-variable comparison
inequalities and on the four-face energy identities. Those hypotheses are
not smuggled in as axioms: they appear in the theorem's type.

The derivation of those hypotheses is completed in
`ManuscriptTriangleOrdering` and `ManuscriptStationaryRigidity`.
-/

noncomputable section

open scoped InnerProductSpace

namespace SphericalTetrahedron

/-- The exact rational face energy from the manuscript, parameterized by
an inverse `g` of the stationary angular kernel. -/
def manuscriptFaceEnergy (g : ℝ → ℝ) (a b c : ℝ) : ℝ :=
  Sphere3.triangleGramEnergy (g (b + c)) (g (a + c)) (g (a + b)) a b c

/-- Exchanging the first two face vertices does not change energy. -/
theorem manuscriptFaceEnergy_swap12 (g : ℝ → ℝ) (a b c : ℝ) :
    manuscriptFaceEnergy g a b c = manuscriptFaceEnergy g b a c := by
  unfold manuscriptFaceEnergy
  simpa only [add_comm b a] using
    (Sphere3.triangleGramEnergy_swap12
      (g (b + c)) (g (a + c)) (g (a + b)) a b c)

/-- Exchanging the last two face vertices does not change energy. -/
theorem manuscriptFaceEnergy_swap23 (g : ℝ → ℝ) (a b c : ℝ) :
    manuscriptFaceEnergy g a b c = manuscriptFaceEnergy g a c b := by
  unfold manuscriptFaceEnergy
  simpa only [add_comm c b] using
    (Sphere3.triangleGramEnergy_swap23
      (g (b + c)) (g (a + c)) (g (a + b)) a b c)

/-- Precisely the real-variable conclusion of Section 4 of the manuscript,
assuming the three strict comparisons supplied by Section 3. No
geometric or analytic axiom is used. -/
theorem manuscript_ordered_four_face_rigidity
    (g : ℝ → ℝ) (a b c d : ℝ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c)
    (hFirst : b < a →
      manuscriptFaceEnergy g a c d < manuscriptFaceEnergy g b c d)
    (hSecond : c < b →
      manuscriptFaceEnergy g b d a < manuscriptFaceEnergy g c d a)
    (hIso : d < a →
      manuscriptFaceEnergy g a a a < manuscriptFaceEnergy g d a a)
    (h01 : manuscriptFaceEnergy g a c d = manuscriptFaceEnergy g b c d)
    (h12 : manuscriptFaceEnergy g a b d = manuscriptFaceEnergy g a c d)
    (h23 : manuscriptFaceEnergy g a b c = manuscriptFaceEnergy g a b d) :
    a = b ∧ b = c ∧ c = d := by
  exact ordered_four_face_rigidity (manuscriptFaceEnergy g)
    (manuscriptFaceEnergy_swap12 g)
    (manuscriptFaceEnergy_swap23 g)
    a b c d hab hbc hcd hFirst hSecond hIso h01 h12 h23

/-- A one-to-one interface from the *actual* tetrahedron's stationary
heights to the triangle ordering lemma.  Once the hypotheses about the
face energies have been established, global regularity follows via the
already explicit dual-polarity argument.

The heights are normalized by an arbitrary `c ≠ 0`. In the intended
application `c` is the Lagrange multiplier from `Stationary`. -/
theorem stationary_regular_of_ordered_manuscript_face_comparisons
    (T : SphericalTetrahedron) (hStat : T.Stationary)
    (g : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (t : Fin 4 → ℝ)
    (ht : ∀ i : Fin 4,
      t i = c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ)
    (hSorted : t 1 ≤ t 0 ∧ t 2 ≤ t 1 ∧ t 3 ≤ t 2)
    (hFirst : t 1 < t 0 →
      manuscriptFaceEnergy g (t 0) (t 2) (t 3) <
        manuscriptFaceEnergy g (t 1) (t 2) (t 3))
    (hSecond : t 2 < t 1 →
      manuscriptFaceEnergy g (t 1) (t 3) (t 0) <
        manuscriptFaceEnergy g (t 2) (t 3) (t 0))
    (hIso : t 3 < t 0 →
      manuscriptFaceEnergy g (t 0) (t 0) (t 0) <
        manuscriptFaceEnergy g (t 3) (t 0) (t 0))
    (hFaces01 : manuscriptFaceEnergy g (t 0) (t 2) (t 3) =
      manuscriptFaceEnergy g (t 1) (t 2) (t 3))
    (hFaces12 : manuscriptFaceEnergy g (t 0) (t 1) (t 3) =
      manuscriptFaceEnergy g (t 0) (t 2) (t 3))
    (hFaces23 : manuscriptFaceEnergy g (t 0) (t 1) (t 2) =
      manuscriptFaceEnergy g (t 0) (t 1) (t 3)) :
    T.Regular := by
  obtain ⟨h01, h12, h23⟩ :=
    manuscript_ordered_four_face_rigidity g
      (t 0) (t 1) (t 2) (t 3)
      hSorted.1 hSorted.2.1 hSorted.2.2
      hFirst hSecond hIso hFaces01 hFaces12 hFaces23
  have h02 : t 0 = t 2 := h01.trans h12
  have h03 : t 0 = t 3 := h02.trans h23
  have ht0 : ∀ i : Fin 4, t i = t 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h02.symm
    · exact h03.symm
  apply T.stationary_regular_of_equal_dual_heights hStat
  intro i j
  have hti := ht i
  have htj := ht j
  have hscaled :
      c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ =
        c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ := by
    calc
      c⁻¹ * ⟪T.normalDualAxis, T.dualVertex i⟫_ℝ = t i := hti.symm
      _ = t 0 := ht0 i
      _ = t j := (ht0 j).symm
      _ = c⁻¹ * ⟪T.normalDualAxis, T.dualVertex j⟫_ℝ := htj
  exact mul_left_cancel₀ (inv_ne_zero hc) hscaled

end SphericalTetrahedron
