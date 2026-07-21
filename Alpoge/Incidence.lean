import Alpoge.Basic

/-!
# The Keller map as the simple-root incidence projection

This module globalizes the projective fiber equivalence proved in
`Alpoge.Basic`.  A target `q = (a,b,c)` is read as the normalized
binary cubic

```text
Q_q(T,U) = cT³ - 2T²U + bTU² - 2aU³.
```

Its projective roots are represented by `Option K`: `some t` is `[t:1]` and
`none` is `[1:0]`.  The total incidence space consists of a target together
with a simple projective root of its cubic.  The headline equivalence
`sourceEquivSimpleRootIncidence` identifies the whole source of the Alpöge map
with this incidence space, not merely one fiber at a time, and
`sourceEquivSimpleRootIncidence_target` says that the Keller map becomes the
incidence projection under that identification.

The second theorem chain makes the root derivative explicit.  In the affine
chart it is the ordinary derivative `Q'_q(t)` and satisfies `x * Q'_q(t) = 2`;
at infinity it is the derivative of the dehomogenized cubic at `U = 0`, namely
the unit coefficient `-2`.  Thus the attained incidence space consists exactly
of roots carrying a nonvanishing root derivative.
-/

namespace Alpoge


noncomputable section

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- A target together with a simple projective root of its normalized binary
cubic.  This is the `K`-point presentation of the simple-root incidence space. -/
abbrev Incidence (K : Type*) [Field K] :=
  Σ q : K × K × K,
    {r : Option K // projectiveSimpleRoot q.1 q.2.1 q.2.2 r}

/-- Projection from the simple-root incidence space to cubic coefficients. -/
def target : Incidence K → K × K × K := Sigma.fst

/-- **Global simple-root incidence theorem.**  The whole source of the
Alpöge map is equivalent to the total space of simple projective roots of the
normalized binary cubic family. -/
noncomputable def sourceEquivSimpleRootIncidence :
    (K × K × K) ≃ Incidence K :=
  (Equiv.sigmaFiberEquiv (F K)).symm.trans
    (Equiv.sigmaCongrRight fun q =>
      fiberEquivSimpleRootsProj (K := K) (a := q.1) (b := q.2.1) (c := q.2.2))

/-- Under the incidence equivalence, the Keller map is literally
projection to the coefficients of the normalized binary cubic. -/
@[simp] theorem sourceEquivSimpleRootIncidence_target (p : K × K × K) :
    target (sourceEquivSimpleRootIncidence (K := K) p) = F K p :=
  rfl

/-- The root coordinate of the incidence equivalence is the
projective resolvent of the source point. -/
@[simp] theorem sourceEquivSimpleRootIncidence_root (p : K × K × K) :
    (sourceEquivSimpleRootIncidence (K := K) p).2.1 =
      projectiveResolventValue p :=
  rfl

/-- Vanishing equation for the normalized binary cubic on `ℙ¹(K)`. -/
def IsProjectiveRoot (a b c : K) : Option K → Prop
  | none => c = 0
  | some t => c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0

/-- Root derivative of the normalized binary cubic.  At `[t:1]` this is
`Q'(t)`; at `[1:0]` it is the derivative of the dehomogenized cubic at
`U = 0`, namely `-2`. -/
def rootDerivative (b c : K) : Option K → K
  | none => -2
  | some t => 3 * c * t ^ 2 - 4 * t + b

/-- A projective root is simple exactly when its root derivative is
nonzero. -/
theorem projectiveSimpleRoot_iff_rootDerivative {a b c : K} {r : Option K} :
    projectiveSimpleRoot a b c r ↔
      IsProjectiveRoot a b c r ∧ rootDerivative b c r ≠ 0 := by
  cases r with
  | none =>
      simp only [projectiveSimpleRoot, IsProjectiveRoot, rootDerivative, ne_eq,
        neg_eq_zero, iff_self_and]
      exact fun _ => two_ne_zero
  | some t =>
      rfl

/-- Every point of the incidence space carries a nonvanishing root
derivative. -/
theorem incidence_rootDerivative_ne_zero (i : Incidence K) :
    rootDerivative i.1.2.1 i.1.2.2 i.2.1 ≠ 0 :=
  (projectiveSimpleRoot_iff_rootDerivative.mp i.2.2).2

/-- On the affine source chart the source coordinate satisfies
`x * Q'(t) = 2`. -/
theorem affine_source_mul_rootDerivative {x y z : K} (hx : x ≠ 0) :
    x * rootDerivative (F K (x, y, z)).2.1 (F K (x, y, z)).2.2
        (projectiveResolventValue (x, y, z)) = 2 := by
  rw [show projectiveResolventValue (x, y, z) = some (y + 1 / x) by
    simp [projectiveResolventValue, hx]]
  simp only [rootDerivative]
  have h := fiberCubic_deriv_div (K := K) hx
    (show F K (x, y, z) =
      ((F K (x, y, z)).1, (F K (x, y, z)).2.1, (F K (x, y, z)).2.2) from rfl)
  rw [h]
  field_simp

omit [NeZero (2 : K)] in
/-- On the complementary source chart, the projective root is infinity and
its root derivative is the unit coefficient `-2`. -/
theorem infinity_source_root_and_deriv {x y z : K} (hx : x = 0) :
    projectiveResolventValue (x, y, z) = none ∧
      rootDerivative (F K (x, y, z)).2.1 (F K (x, y, z)).2.2
        (projectiveResolventValue (x, y, z)) = -2 := by
  subst x
  simp [projectiveResolventValue, rootDerivative]

/-- **Root-derivative normal form.**  Every source point is either the root
at infinity, with derivative `-2`, or an affine root whose derivative is
`2/x`. -/
theorem source_rootDerivative_normalForm (p : K × K × K) :
    (p.1 = 0 ∧
        projectiveResolventValue p = none ∧
        rootDerivative (F K p).2.1 (F K p).2.2 (projectiveResolventValue p) = -2) ∨
      (p.1 ≠ 0 ∧
        p.1 * rootDerivative (F K p).2.1 (F K p).2.2
          (projectiveResolventValue p) = 2) := by
  rcases p with ⟨x, y, z⟩
  by_cases hx : x = 0
  · left
    exact ⟨hx, (infinity_source_root_and_deriv (K := K) hx).1,
      (infinity_source_root_and_deriv (K := K) hx).2⟩
  · right
    exact ⟨hx, affine_source_mul_rootDerivative (K := K) hx⟩

end

end Alpoge
