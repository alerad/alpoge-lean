# Formal verification and structure theory of the Alpöge Keller map

Lean 4 / Mathlib formalization of Alpöge's July 2026 counterexample to the
Jacobian Conjecture, together with new machine-verified theorems about its
geometry.  Two files, no `sorry`, no axioms beyond Mathlib.

## Verified results (`Alpoge/Basic.lean`)

Over every field `K` (characteristic hypotheses marked per theorem; most need
only `2 ≠ 0`):

- `jacobian_det` — the formal Jacobian determinant is constantly `-2` (over `ℤ`,
  via `MvPolynomial.pderiv`);
- `three_point_fiber`, `not_injective` — three explicit rational states share
  one image;
- `missed_curve`, `not_surjective` — the image omits the entire explicit curve
  `s ↦ (s²/12, s, 4/(3s))`, via a parametric Nullstellensatz certificate;
- `fiber_cubic` — every fiber state satisfies the sheet cubic
  `c²(W·u³ + (b²−12a)u − 4a) = 0`, `W = 27a²c²−18abc+16a+b³c−b²`;
- `fiberCubic_discr` — the fiber cubic `cT³ − 2T² + bT − 2a` has discriminant
  exactly `−4W`; `fiberCubic_on_curve` — on the missed curve it is a perfect
  cube (the omitted locus is the triple-root stratum);
- `primitive_cubic`, `primitive_cubic_deriv` — the resolvent `t = y + 1/x`
  satisfies the fiber cubic with `x·P′(t) = 2` (étaleness as one identity);
- `residual_disc` — the residual quadratic has discriminant `−W·x²` on the
  fiber: the degree-six Galois closure of the cover is `source(√−W)`;
- `fiber_point_of_root`, `sibling_root`, `resolvent_injective` — explicit
  reconstruction of fiber states from simple roots, and of the remaining
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
- `source_recoveryJet_normalForm` — every source state is a root equipped with
  a nonvanishing first recovery jet: `x·Q′(t) = 2` on the affine chart, jet
  `−2` at infinity.

In one sentence: étaleness remembers only that every reached root is simple;
it cannot know whether the cubic has three, one, or zero of them.

## Not claimed (work in progress)

- the exact fiber count `3/1/0` over an algebraically closed field (all
  ingredients above; multiset counting glue pending);
- `S₃` monodromy and irreducibility statements;
- identification of the non-properness set with `V(W)`;
- scheme-level (as opposed to `K`-point) statements;
- the analytic identification of formal partials with Fréchet derivatives.

## Build

```
lake exe cache get
lake build
```

## Attribution

The map is due to L. Alpöge (announcement 2026-07-19).  The primitive cubic
presentation refines observations circulating in community analyses.  The
formalization and the new theorems here were produced in an AI-assisted
workflow (CAS-discovered certificates checked by `linear_combination`);
details on request.

## License

Apache License 2.0 (the Mathlib ecosystem license) — see `LICENSE`.
