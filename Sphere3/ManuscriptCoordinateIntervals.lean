module

public import Sphere3.ManuscriptTriangleAlgebra

@[expose] public section

/-!
# Coordinate-line connectedness of the triangle domain

The coordinate interval claim in section 3.4 of the manuscript reduces
to these real-variable inequalities when the side functions are antitone
and their difference is monotone. Geometry and inverse-function calculus are handled in
`SphericalTetrahedron.ManuscriptTriangleOrdering`.
-/

namespace Sphere3

/-- The spherical triangle inequalities with fixed side `a`. -/
def triangleSideAdmissible (a : ℝ) (b c : ℝ → ℝ) (x : ℝ) : Prop :=
  0 < b x ∧ b x < Real.pi ∧
  0 < c x ∧ c x < Real.pi ∧
  b x - c x < a ∧ a < b x + c x ∧
  a + b x + c x < 2 * Real.pi

/-- Between two admissible points, every intermediate point is
admissible, given the three relevant side monotonicities. -/
theorem triangle_side_admissible_between
    (a : ℝ) (b c : ℝ → ℝ)
    (hb : Antitone b) (hc : Antitone c)
    (hdiff : Monotone (fun x => b x - c x))
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hx : triangleSideAdmissible a b c x)
    (hz : triangleSideAdmissible a b c z) :
    triangleSideAdmissible a b c y := by
  rcases hx with ⟨hbx0, hbxpi, hcx0, hcxpi, hxdiff, hxsum, hxtotal⟩
  rcases hz with ⟨hbz0, hbzpi, hcz0, hczpi, hzdiff, hzsum, hztotal⟩
  have hbx_y : b y ≤ b x := hb hxy
  have hby_z : b z ≤ b y := hb hyz
  have hcx_y : c y ≤ c x := hc hxy
  have hcy_z : c z ≤ c y := hc hyz
  have hdiff_yz : b y - c y ≤ b z - c z := hdiff hyz
  unfold triangleSideAdmissible
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Pair-sum bounds preserve the interval between feasible endpoints. -/
theorem triangle_pair_sums_between
    (u v : ℝ) {x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z)
    (hxu : 0 < x + u) (hxv : 0 < x + v)
    (hzu : z + u < 2) (hzv : z + v < 2) :
    0 < y + u ∧ y + u < 2 ∧
    0 < y + v ∧ y + v < 2 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end Sphere3
