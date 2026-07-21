# Formal verification and structure theory of the Alpöge Keller map

[![CI](https://github.com/alerad/alpoge-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/alerad/alpoge-lean/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/1306865154.svg)](https://doi.org/10.5281/zenodo.21461528)

Lean 4 / Mathlib formalization of Alpöge's July 2026 counterexample to the
Jacobian Conjecture, together with new machine-verified theorems about its
geometry.  Three files, no `sorry`, no axioms beyond Mathlib.

## Verified results (`Alpoge/Basic.lean`)

Over every field `K` (characteristic hypotheses marked per theorem; most need
only `2 ≠ 0`):

- `jacobian_det` — the formal Jacobian determinant is constantly `-2` (over `ℤ`,
  via `MvPolynomial.pderiv`);
- `three_point_fiber`, `not_injective` — three explicit rational points share
  one image;
- `missed_curve`, `not_surjective` — the image omits the entire explicit curve
  `s ↦ (s²/12, s, 4/(3s))`, via a parametric Nullstellensatz certificate;
- `fiber_u_elimination` — every fiber point satisfies the sheet cubic
  `c²(W·u³ + (b²−12a)u − 4a) = 0`, `W = 27a²c²−18abc+16a+b³c−b²`;
- `fiberCubic_discr` — the fiber cubic `cT³ − 2T² + bT − 2a` has discriminant
  exactly `−4W`; `fiberCubic_on_curve` — on the missed curve it is a perfect
  cube (the omitted locus is the triple-root stratum);
- `fiberCubic_cleared`, `fiberCubic_deriv_identity` — the root coordinate
  `t = y + 1/x` satisfies the fiber cubic with `x·P′(t) = 2` (the Keller
  condition as one identity);
- `residual_disc` — the residual quadratic has discriminant `−W·x²` on the
  fiber: adjoining `√−W` splits the two residual sheets — the quadratic step
  toward the generic splitting field (irreducibility not formalized);
- `fiber_point_of_root`, `sibling_root`, `resolvent_injective` — explicit
  reconstruction of fiber points from simple roots, and of the remaining
  sheets from one root plus a square root of `−W`;
- `projectiveSimpleRoot_exists_third` — the no-two law: two distinct simple
  rational roots force a third;
- `fiberEquivSimpleRootsProj` — each fiber is equivalent to the simple
  projective `K`-roots of its binary cubic, with `[1:0]` as the `x = 0` sheet.

## Structure theorem (`Alpoge/Incidence.lean`)

- `sourceEquivSimpleRootIncidence` — **the whole source of the map is
  equivalent to the incidence space of pairs (normalized binary cubic
  `cT³ − 2T²U + bTU² − 2aU³`, simple projective root), and under this
  equivalence the Keller map is the coefficient projection — definitionally
  (`rfl`)**;
- `source_rootDerivative_normalForm` — every source point is a root equipped
  with a nonvanishing root derivative: `x·Q′(t) = 2` on the affine chart,
  derivative `−2` at infinity.

In one sentence: the Keller condition forces every attained root to be
simple, but does not control how many simple roots the cubic has — three,
one, or zero.

Additionally verified (counting layer):

- `fiber_ncard_le_three`, `fiber_ncard_mem_zero_one_three` — every rational
  fiber over a characteristic-zero field is finite of cardinality `0`, `1`,
  or `3`;
- `range_eq_compl_missedCurve` — over an algebraically closed field of
  characteristic zero the image is exactly the complement of the triple-root
  curve `{12a = b², 3bc = 4}`;
- `projective_structure_and_exact_image`, `counterexample_explained` —
  packaged headline statements;
- `missedCurveEquivNonzero` — the missed curve is a punctured line: projection
  to the `b`-coordinate is an equivalence onto `K \ {0}`, with explicit
  inverse `s ↦ (s²/12, s, 4/(3s))`;
- `fiber_ncard_eq_zero_iff`, `fiber_ncard_mem_one_three_of_not_onMissedCurve`,
  `wallW_eq_zero_of_onMissedCurve` — stratum boundaries: the fiber is empty
  exactly on the missed curve, and has one or three points off it.

## Wall stratification (`Alpoge/Wall.lean`)

The discriminant hypersurface `V(W)` (`disc P = −4W`) identified, at the
`K`-point level, as the exact fiber-drop locus — and the missed curve as its singular locus:

- `neg_four_mul_wallW_eq_sq_sep` — discriminant as root separation: under the
  Vieta relations of the fiber cubic, `−4W = c⁴·(t₁−t₂)²(t₁−t₃)²(t₂−t₃)²`;
- `wallW_ne_zero_of_two_fiber_points`, `fiber_ncard_le_one_of_wallW_eq_zero` —
  **arithmetic wall pinch**: over any field (char ≠ 2, projective-root form
  characteristic-free), two distinct rational points in one fiber force
  `W ≠ 0`; on the wall every rational fiber has at most one point, with no
  algebraic closure needed;
- `simpleRoot_of_root_of_wallW_ne_zero` — off the wall every root of the
  fiber cubic is automatically simple (via the universal certificate
  `disc_factorization`);
- `fiber_ncard_eq_three_iff`, `fiber_ncard_eq_one_iff`,
  `fiber_ncard_stratification` — over an algebraically closed field of
  characteristic zero the count is an exact dictionary: `3` iff `W ≠ 0`,
  `1` iff `W = 0` off the missed curve, `0` iff on the missed curve.  The
  prose claim "fibers jump `3 → 1 → 0` across the discriminant wall" is now
  a theorem;
- `onMissedCurve_iff_pderiv_wallPoly_eq_zero`,
  `onMissedCurve_iff_singular_point` — **the missed curve is the singular
  locus of `V(W)`**: with `wallPoly` over `ℤ` and genuine
  `MvPolynomial.pderiv` partials, the critical equations `∇W = 0` hold at a
  `K`-point (char ≠ 2) exactly on the missed curve.  Certificates:
  `(3bc−4)² = W_a + 3c·W_b` (an identity over `ℤ`) and
  `b·W_b + 2(12a−b²) = (b²−6a)(3bc−4)`.

## Not claimed (work in progress)

- `S₃` monodromy and irreducibility statements;
- identification of the Jelonek non-properness set `S_F` with `V(W)`
  (properness/topology is not formalized; the fiber-count stratification
  above is its `K`-point layer);
- scheme-level (as opposed to `K`-point) statements;
- the analytic identification of formal partials with Fréchet derivatives.

## Build

```
lake exe cache get
lake build
```

## Attribution

The map is due to L. Alpöge (announcement 2026-07-19).  The normalized fiber
cubic presentation refines observations circulating in community analyses.  The
formalization and the new theorems here were produced in an AI-assisted
workflow (CAS-discovered certificates checked by `linear_combination`);
details on request.

## Related work

A same-day prose explainer, *The Jacobian counterexample, explained*
(A. Gallagher, <https://jacobianfun.org/jacobian-explained>, 2026-07-20),
presents the counterexample with exact SymPy verification and develops
higher-degree families of counterexamples; it contains no formalization.  The
distinctive contributions here are: machine-checked proofs of the structure
theory (the incidence equivalence is definitional in Lean); the arithmetic
strengthening — the fiber equivalence and the 0/1/3 law over **every** field
of characteristic zero (mostly char ≠ 2), with two rational fiber points
constructively determining a third; and the wall stratification with the
singular-locus identification.  Other public Lean formalizations verify the
Jacobian determinant and the three-point collision only.

## License

Apache License 2.0 (the Mathlib ecosystem license) — see `LICENSE`.
