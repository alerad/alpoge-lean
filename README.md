# Formal verification and structure theory of the Alpöge Keller map

[![CI](https://github.com/alerad/alpoge-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/alerad/alpoge-lean/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/1306865154.svg)](https://doi.org/10.5281/zenodo.21461528)

Lean 4 / Mathlib formalization of Alpöge's July 2026 counterexample to the
Jacobian Conjecture, together with new machine-verified theorems about its
geometry.  Six files, no `sorry`, no axioms beyond Mathlib.

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
  equivalent, as an equivalence of `K`-points, to the incidence space of pairs (normalized binary cubic
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
  fiber over any field with `2 ≠ 0` — in particular over every finite field
  of odd order — is finite of cardinality `0`, `1`, or `3`;
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

## Refutation of the formal-conjectures statement (`Alpoge/FormalConjectures.lean`)

The Jacobian Conjecture statement of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/4fac2db24ca16acef0e1c089c86891d0383dbf38/FormalConjectures/Wikipedia/JacobianConjecture.lean)
(commit `4fac2db2`) is mirrored verbatim (formal `pderiv` Jacobian, unit
determinant hypothesis, *compositional* polynomial inverse via `bind₁`) and
refuted:

- `isUnit_jacobian_det` — the mirrored Jacobian determinant of the Alpöge map
  is the unit `-2`;
- `no_polynomial_inverse` — over any characteristic-zero field the map admits
  no two-sided polynomial inverse (a compositional inverse would make the
  point map injective, contradicting the three-point fiber);
- `jacobian_conjecture_false` — the negation of the mirrored statement,
  witnessed at `k = ℚ`, `σ = Fin 3`.

## Characteristic-three degeneration (`Alpoge/CharThree.lean`)

In characteristic `3` the geometry undergoes a verified phase transition:

- `fiberCubic_char3_normal_form` — the translation `T = b + S` puts the
  fiber cubic into the exact normal form `cS³ + S² + W` (the linear term
  vanishes; the wall scalar is the constant term);
- `not_onMissedCurve_char3` — the missed curve is empty (`3bc = 4` forces
  `1 = 0`);
- `wall_pderiv_a_ne_zero_char3` — the formal `a`-partial of the wall
  polynomial evaluates to `1` everywhere (whence `V(W)` has no critical
  `K`-points: the singular curve is gone);
- `no_triple_root_char3` — the triple-root stratum disappears.

## Exact finite-field statistics (`Alpoge/Counting.lean`)

**Machine-verified**: over every finite field `K` with `2 ≠ 0`, writing `Nⱼ`
for the number of targets with exactly `j` rational preimages and
`q = |K|` (`finiteField_fiber_statistics`):

- `6N₃ = (q−1)(q²+2)` for `char K ≠ 3`, and `6N₃ = q²(q−1)` for
  `char K = 3`;
- `N₁ + 3N₃ = q³` and `N₀ + N₁ + N₃ = q³`, hence `N₀ = 2N₃`;
- the fiber-count distribution satisfies `(N₀, N₁, N₃)/q³ → (1/3, 1/2, 1/6)`
  — the proportions of elements of `S₃` with `0`, `1`, `3` fixed points
  (3-cycles, transpositions, identity): fibers distribute like fixed-point
  counts of the generic `S₃`-cover, obtained here by exact finite-`q`
  counting with all lower-order terms explicit.

Proof: the double count of (target, ordered triple of simple roots) pairs.
A distinct triple of projective points supports exactly one target unless it
is finite with sum zero (`c·(t₁+t₂+t₃) = 2` is forced by Vieta), and
targets with three-point fibers carry exactly `3! = 6` ordered root triples.
The forbidden sum-zero locus is counted by an explicit pair bijection.
Independently cross-checked by brute-force enumeration for
`q = 3, 5, 7, 11, 13`.

In characteristic `3`, over an algebraically closed field, the map becomes
surjective while remaining étale and non-injective (certificate layer in
`CharThree.lean`; the algebraically-closed root count is future work).

## The sign-biased S₃ law (`Alpoge/SignBias.lean`)

The finite-field statistics repackage exactly.  Assign to a fiber with
`j ∈ {0, 1, 3}` rational points the unique `S₃`-class with `j` fixed points,
and to that class the characteristic polynomial `det(I − t·Pσ)` of the
permutation representation.  **Machine-verified**, in every commutative
ring, with `q = |K|`, `Nⱼ` the fiber counts, and bias `b := q³ − 6N₃`:

- `S3_cycle_index` — the uniform average is `1 − t`: summed over `S₃`,
  `(1−t)³ + 3(1−t)(1−t²) + 2(1−t³) = 6(1−t)` (characteristic-free);
- `fiberCount_sign_bias` — `2N₁ = q³ + b` and `3N₀ = q³ − b`: the
  fiber-count distribution is the uniform `S₃` measure deformed exactly in
  the sign-character direction;
- `bias_eq_of_three_ne_zero`, `bias_eq_char3` — the bias is the integer
  `b = (q−1)² + 1` (char `≠ 3`), resp. `b = q²` (char `3`): **no error
  term**, where generic Chebotarev equidistribution would only give
  `O(q^{5/2})`;
- `sum_permCharPoly_fiber` — the averaged characteristic polynomial of the
  map: `∑_y det(I − t·P_{ν(y)}) = (1 − t)(q³(1 − t²) + 6N₃t²)`, the
  subtraction-free form of `q³(1 − t)(1 − κ_q t²)` with `κ_q = b/q³`.

The bias coordinate `κ_q` interpolates between `κ = 1` (the map would be a
bijection — the endpoint the Jacobian Conjecture asserted) and `κ = 0`
(uniform `S₃` equidistribution, the `q → ∞` limit); the Alpöge map traces
the exact arc `κ_q = ((q−1)² + 1)/q³`.

## The double-root slice is affine 3-space (`Alpoge/Slice.lean`)

Tao's digestion of the counterexample (2026-07-21) presents the source as the
slice `X = {(L,Q) : Res(L,Q) = 1, D(LQ) = 1}` of the multiplication map
`(L,Q) ↦ LQ` on binary forms, where `D` is the double-root-type coefficient
hyperplane, and observes the "affine miracle": `X` is polynomially isomorphic
to `𝔸³`.  **Machine-verified** at the `K`-point level, over every field with
`2 ≠ 0` (`sliceEquiv`):

- the slice equations in coordinates `L = az + bw`, `Q = cz² + dzw + ew²` are
  `a²e − abd + cb² = 1` and `ad + bc = 1`;
- `res_eq_key_combination`: the resultant decomposes as
  `Res = b·(ad + bc) + a·(ae − 2bd)`, so on the slice `b = 1 + a·(2bd − ae)`
  (Will Sawin's coordinate reduction);
- Tao's explicit polynomial chart `𝔸³ → X` lands in the slice
  (characteristic-free `ℤ`-identity) and is a bijection onto it, with a
  polynomial-in-`1/2` inverse — surjectivity by cancelling `a` (resp. `a²`)
  against CAS-extracted certificates, with the `a = 0` fiber (where `b = 1`
  is forced) checked separately.

The cohomological reason the trivialization *had* to exist — the slice is an
affine-line torsor over the `(a, y)`-plane, and `H¹(𝔸², O) = Pic(𝔸²) = 0` —
is not formalized; this module pins down its `K`-point content.

## Not claimed (work in progress)

- `S₃` monodromy and irreducibility statements;
- identification of the Jelonek non-properness set `S_F` with `V(W)`
  (properness/topology is not formalized; the fiber-count stratification
  above is its `K`-point layer);
- scheme-level (as opposed to `K`-point) statements — in particular the
  factorization presentation (`Sym¹ × Sym² → Sym³` multiplication and
  resultant normalization) of which the incidence theorem is the `K`-point
  shadow, and the torsor/cohomology argument of which the slice
  trivialization is the `K`-point shadow;
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
