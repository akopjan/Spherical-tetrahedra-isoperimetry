# Isoperimetric Inequality for Spherical Tetrahedra

The sharp isoperimetric inequalities for tetrahedra in the unit three-sphere $\mathbb{S}^3$: the regular tetrahedron uniquely minimizes surface area at a fixed volume and maximizes volume at a fixed surface area.

This repository provides a complete, unconditional Lean 4 formalization of *A global isoperimetric inequality for spherical tetrahedra* ([`paper/manuscript.tex`](paper/manuscript.tex)), developed with the assistance of ChatGPT and Gemini.

---

## Challenge Theorems

The challenge is specified in `Challenge.lean` and checked by the Palomar Comparator against `Solution.lean`:

1. **Theorem 1.1 (Fixed-Volume Area Minimization)**:
   Among all spherical tetrahedra of a given volume, the regular tetrahedron uniquely minimizes total surface area:
   ```lean
   theorem isoperimetric_area
       (T R : SphericalTetrahedron)
       (hR : R.Regular) (hV : T.volume = R.volume) :
       R.area ≤ T.area ∧ (T.area = R.area ↔ T.Congruent R)
   ```

2. **Theorem 1.2 (Fixed-Area Volume Maximization)**:
   Among all spherical tetrahedra of a given surface area, the regular tetrahedron uniquely maximizes volume:
   ```lean
   theorem isoperimetric_volume
       (T R : SphericalTetrahedron)
       (hR : R.Regular) (hA : T.area = R.area) :
       T.volume ≤ R.volume ∧ (T.volume = R.volume ↔ T.Congruent R)
   ```

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
