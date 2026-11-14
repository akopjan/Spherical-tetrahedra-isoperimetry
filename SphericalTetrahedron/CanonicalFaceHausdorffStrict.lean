module

public import SphericalTetrahedron.CanonicalFaceHausdorffOrder
public import Sphere3.CanonicalFaceOpenPatchProjection

@[expose] public section

/-!
# Strict monotonicity of the true canonical first-face H² area

The final proof combines five independent facts:
1. the face is a compact Lipschitz image (finite raw Hausdorff H²);
2. the smaller face rotates into the larger one by an ambient isometry;
3. the larger face contains the image of a genuine nonempty open planar
   difference patch disjoint from the rotated smaller face;
4. the fixed-plane projection is open via the explicit elliptic chart;
5. raw H² in the Euclidean plane is positive on every nonempty open set.
-/

noncomputable section

namespace SphericalTetrahedron

/-- Strict growth of the *original unnormalized* Hausdorff area of one
canonical face, without Girard's theorem or a change-of-measure axiom. -/
theorem canonicalFirstFaceStrict_from_open_patch : CanonicalFirstFaceStrict := by
  intro t s ht hs hts
  obtain ⟨O, hOpen, hNonempty, hInclusion⟩ :=
    Sphere3.canonical_face_difference_has_open_projection ht hts
  exact canonical_first_face_area_strict_of_open_projection_final
    ht hts O hOpen hNonempty hInclusion

end SphericalTetrahedron
