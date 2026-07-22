import Alpoge.Wall

/-!
# The characteristic-three degeneration

In characteristic `3` the geometry of the Alpöge map undergoes a phase
transition, verified here at the certificate level:

* `fiberCubic_char3_normal_form` — the substitution `T = b + S` reduces the
  fiber cubic to the exact normal form `cS³ + S² + W`: in characteristic `3`
  the wall scalar `W` *is* the constant term of the depressed cubic;
* `not_onMissedCurve_char3` — the missed curve is empty: `3bc = 4` is
  unsatisfiable;
* `wall_smooth_char3` — the discriminant hypersurface `V(W)` is smooth:
  the formal `a`-partial of the wall polynomial evaluates to `1 ≠ 0`
  everywhere.

Together with the `0/1/3` law (now proved for every field with `2 ≠ 0`),
these are the certificate layer of the characteristic-three picture: the
triple-root stratum disappears, so over an algebraically closed field of
characteristic `3` no fiber can be empty — the map becomes surjective while
remaining non-injective.  (The surjectivity statement itself requires the
algebraically-closed root machinery in characteristic `3` and is left as the
next milestone; see the README.)

Characteristic `3` is expressed by the hypothesis `(3 : K) = 0` rather than
`CharP K 3`, keeping every statement a certified polynomial identity.
-/

namespace Alpoge

open MvPolynomial

variable {K : Type*} [Field K]

/-- **Characteristic-three normal form.**  If `3 = 0`, the substitution
`T = b + S` depresses the fiber cubic to `cS³ + S² + W`: the wall scalar is
the constant term.  Certificate: the difference is `3·(explicit polynomial)`. -/
theorem fiberCubic_char3_normal_form (h3 : (3 : K) = 0) (a b c s : K) :
    c * (b + s) ^ 3 - 2 * (b + s) ^ 2 + b * (b + s) - 2 * a =
      c * s ^ 3 + s ^ 2 + wallW a b c := by
  unfold wallW
  linear_combination
    (c * b ^ 2 * s + c * b * s ^ 2 - b * s - s ^ 2 - 6 * a -
      9 * a ^ 2 * c ^ 2 + 6 * a * b * c) * h3

/-- In characteristic three the missed curve is empty: `3bc = 4` would force
`1 = 0`. -/
theorem not_onMissedCurve_char3 (h3 : (3 : K) = 0) (a b c : K) :
    ¬ OnMissedCurve a b c := by
  rintro ⟨-, h34⟩
  have h4 : (4 : K) = 0 := by linear_combination (b * c) * h3 - h34
  have h1 : (1 : K) = 0 := by linear_combination h4 - h3
  exact one_ne_zero h1

/-- **The wall is smooth in characteristic three.**  The formal `a`-partial
of the wall polynomial evaluates to `54ac² − 18bc + 16 = 1 ≠ 0` at every
point: `V(W)` has no critical points, so the singular triple-root curve of
the characteristic-zero picture has disappeared. -/
theorem wall_smooth_char3 (h3 : (3 : K) = 0) (a b c : K) :
    aeval ![a, b, c] (pderiv 0 wallPoly) ≠ 0 := by
  rw [aeval_pderiv_wallPoly_zero]
  intro h0
  have h1 : (1 : K) = 0 := by
    linear_combination h0 - (18 * a * c ^ 2 - 6 * b * c + 5) * h3
  exact one_ne_zero h1

/-- **No triple roots in characteristic three.**  A triple root of the fiber
cubic at any `t` forces `1 = 0`: in the depressed form `cS³ + S² + W` the
`S²`-coefficient is the unit `1`, while a cube `c(S − r)³` has no `S²` term
when `3 = 0`.  Stated via the second divided difference: if `t` is a root of
the cubic, of its derivative, and of its second Hasse derivative, we get a
contradiction. -/
theorem no_triple_root_char3 (h3 : (3 : K) = 0) {a b c t : K}
    (_hP : c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0)
    (_hP' : 3 * c * t ^ 2 - 4 * t + b = 0)
    (hP'' : 3 * c * t - 2 = 0) :
    False := by
  have h1 : (1 : K) = 0 := by
    linear_combination hP'' - (c * t - 1) * h3
  exact one_ne_zero h1

end Alpoge
