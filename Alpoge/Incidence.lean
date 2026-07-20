import Alpoge.Basic

/-!
# The Keller map as the universal simple-root incidence observer

This module globalizes the projective fiber equivalence proved in
`JacobianCounterexample`.  A target `q = (a,b,c)` is read as the normalized
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

The second theorem chain makes the recovery jet explicit.  In the affine
chart it is the ordinary derivative `Q'_q(t)` and satisfies `x * Q'_q(t) = 2`;
at infinity it is the normalized next coefficient `-2`, which is automatically
nonzero.  Thus the reached incidence space consists exactly of roots carrying
a nonvanishing first recovery jet.  A reached state is thus exactly a root
equipped with a nonvanishing first recovery jet.
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

/-- **Universal simple-root incidence theorem.**  The whole source of the
Alpöge map is equivalent to the total space of simple projective roots of the
normalized binary cubic family. -/
noncomputable def sourceEquivSimpleRootIncidence :
    (K × K × K) ≃ Incidence K :=
  (Equiv.sigmaFiberEquiv (F K)).symm.trans
    (Equiv.sigmaCongrRight fun q =>
      fiberEquivSimpleRootsProj (K := K) (a := q.1) (b := q.2.1) (c := q.2.2))

/-- Under the universal incidence equivalence, the Keller map is literally
projection to the coefficients of the normalized binary cubic. -/
@[simp] theorem sourceEquivSimpleRootIncidence_target (p : K × K × K) :
    target (sourceEquivSimpleRootIncidence (K := K) p) = F K p :=
  rfl

/-- The root coordinate of the universal incidence equivalence is the
projective resolvent of the source state. -/
@[simp] theorem sourceEquivSimpleRootIncidence_root (p : K × K × K) :
    (sourceEquivSimpleRootIncidence (K := K) p).2.1 =
      projectiveResolventValue p :=
  rfl

/-- Vanishing equation for the normalized binary cubic on `𝔻¹(K)`. -/
def IsProjectiveRoot (a b c : K) : Option K → Prop
  | none => c = 0
  | some t => c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0

/-- First recovery jet of the normalized binary cubic.  At `[t:1]` this is
`Q'(t)`; at `[1:0]` it is the next homogeneous coefficient `-2`. -/
def rootJet (b c : K) : Option K → K
  | none => -2
  | some t => 3 * c * t ^ 2 - 4 * t + b

/-- A projective root is simple exactly when its first recovery jet is
nonzero. -/
theorem projectiveSimpleRoot_iff_root_jet {a b c : K} {r : Option K} :
    projectiveSimpleRoot a b c r ↔
      IsProjectiveRoot a b c r ∧ rootJet b c r ≠ 0 := by
  cases r with
  | none =>
      simp only [projectiveSimpleRoot, IsProjectiveRoot, rootJet, ne_eq,
        neg_eq_zero, iff_self_and]
      exact fun _ => two_ne_zero
  | some t =>
      rfl

/-- Every point of the incidence space carries a nonvanishing first recovery
jet. -/
theorem incidence_rootJet_ne_zero (i : Incidence K) :
    rootJet i.1.2.1 i.1.2.2 i.2.1 ≠ 0 :=
  (projectiveSimpleRoot_iff_root_jet.mp i.2.2).2

/-- On the affine source chart, the source coordinate is the reciprocal of
the root-recovery jet: `x * Q'(t) = 2`. -/
theorem affine_source_mul_rootJet {x y z : K} (hx : x ≠ 0) :
    x * rootJet (F K (x, y, z)).2.1 (F K (x, y, z)).2.2
        (projectiveResolventValue (x, y, z)) = 2 := by
  rw [show projectiveResolventValue (x, y, z) = some (y + 1 / x) by
    simp [projectiveResolventValue, hx]]
  simp only [rootJet]
  have h := primitive_cubic_deriv_div (K := K) hx
    (show F K (x, y, z) =
      ((F K (x, y, z)).1, (F K (x, y, z)).2.1, (F K (x, y, z)).2.2) from rfl)
  rw [h]
  field_simp

omit [NeZero (2 : K)] in
/-- On the complementary source chart, the projective root is infinity and
its recovery jet is the normalized coefficient `-2`. -/
theorem infinity_source_root_and_jet {x y z : K} (hx : x = 0) :
    projectiveResolventValue (x, y, z) = none ∧
      rootJet (F K (x, y, z)).2.1 (F K (x, y, z)).2.2
        (projectiveResolventValue (x, y, z)) = -2 := by
  subst x
  simp [projectiveResolventValue, rootJet]

/-- **Recovery-jet normal form.**  Every source state is either the root at
infinity, with fixed nonzero jet `-2`, or an affine root whose jet is the
reciprocal coordinate `2/x`. -/
theorem source_recoveryJet_normalForm (p : K × K × K) :
    (p.1 = 0 ∧
        projectiveResolventValue p = none ∧
        rootJet (F K p).2.1 (F K p).2.2 (projectiveResolventValue p) = -2) ∨
      (p.1 ≠ 0 ∧
        p.1 * rootJet (F K p).2.1 (F K p).2.2
          (projectiveResolventValue p) = 2) := by
  rcases p with ⟨x, y, z⟩
  by_cases hx : x = 0
  · left
    exact ⟨hx, (infinity_source_root_and_jet (K := K) hx).1,
      (infinity_source_root_and_jet (K := K) hx).2⟩
  · right
    exact ⟨hx, affine_source_mul_rootJet (K := K) hx⟩

end

end Alpoge
