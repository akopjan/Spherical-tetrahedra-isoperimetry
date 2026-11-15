# Isoperimetric Inequality for Spherical Tetrahedra

Sharp isoperimetric comparisons for geodesic tetrahedra in the unit three-sphere $\mathbb{S}^3$: conditional on a regular tetrahedron having the same volume or surface area, the regular tetrahedron uniquely minimizes surface area at fixed volume and uniquely maximizes volume at fixed surface area up to congruence.

This repository formalizes the optimality and uniqueness claims of *A global isoperimetric inequality for spherical tetrahedra* ([`paper/manuscript.tex`](paper/manuscript.tex)) in Lean 4, developed with the assistance of ChatGPT and Gemini.

---

## Challenge Theorems

The challenge is specified in `Challenge.lean` and checked by the Palomar Comparator against `Solution.lean`:

1. **Fixed-Volume Area Minimization (Conditional Comparison, cf. Theorem 1.1)**:
   Conditional on a given regular spherical tetrahedron `R` having the same volume as `T` (`T.volume = R.volume`), `R` uniquely minimizes total surface area up to congruence:
   ```lean
   theorem isoperimetric_area
       (T R : SphericalTetrahedron)
       (hR : R.Regular) (hV : T.volume = R.volume) :
       R.area ≤ T.area ∧ (T.area = R.area ↔ T.Congruent R)
   ```

2. **Fixed-Area Volume Maximization (Conditional Comparison, cf. Theorem 1.2)**:
   Conditional on a given regular spherical tetrahedron `R` having the same surface area as `T` (`T.area = R.area`), `R` uniquely maximizes volume up to congruence:
   ```lean
   theorem isoperimetric_volume
       (T R : SphericalTetrahedron)
       (hR : R.Regular) (hA : T.area = R.area) :
       T.volume ≤ R.volume ∧ (T.volume = R.volume ↔ T.Congruent R)
   ```

---

## Scope and Alignment with the Manuscript

- **Conditional statements in `Challenge.lean`:** Both compared theorems take an explicit regular tetrahedron `R` with matching volume (`T.volume = R.volume`) or surface area (`T.area = R.area`) as a hypothesis and prove optimality and uniqueness relative to `R`. They do not assert per-value existence of a regular tetrahedron for every prescribed numerical value in the volume interval $(0, \pi^2)$ or surface-area interval $(0, 4\pi)$ stated in Theorems 1.1–1.2 and Section 6 of [`paper/manuscript.tex`](paper/manuscript.tex).
- **Hausdorff-measure normalization:** In `Challenge.lean`, `volume` and `area` are defined via Mathlib's unnormalized `Measure.hausdorffMeasure 3` and `Measure.hausdorffMeasure 2` on `E4` (`EuclideanSpace ℝ (Fin 4)`), which differ from standard spherical volume and area on $\mathbb{S}^3$ by positive dimension-dependent normalization constants.
- **Internal existence result:** Internally, `Solution.lean` establishes without `sorry` that every spherical tetrahedron `T` admits a regular fixed-area volume maximizer `M` with `M.area = T.area` (`regular_fixed_area_maximizer`), though this existence claim and surjectivity onto the normalized numerical intervals $(0, \pi^2)$ and $(0, 4\pi)$ are not part of the compared `Challenge.lean` declarations.

---

## Verification

### Prerequisites
- Lean 4 toolchain `leanprover/lean4:v4.35.0-rc3`
- Mathlib `v4.35.0-rc3`

### Build & Check
```bash
# Build the challenge and solution
lake build

# Run Palomar mechanical verification check
lake comparator --inadvisably-no-sandbox
```

When verified with `lake comparator`, the solution is exported and replayed through the Lean default kernel:
```text
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```
