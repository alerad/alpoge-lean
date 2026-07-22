import Alpoge.Basic

/-!
# Refutation of the formal-conjectures Jacobian Conjecture statement

This module mirrors, verbatim up to renaming, the statement of the Jacobian
Conjecture from `google-deepmind/formal-conjectures`
(`FormalConjectures/Wikipedia/JacobianConjecture.lean`, commit `4fac2db2`,
Apache-2.0) and proves its negation from the Alpöge counterexample:

* `RegularFunction`, `Jacobian`, `comp`, `id` — the mirrored definitions:
  the Jacobian is `Matrix.of fun i j => pderiv i (F j)` (formal partials),
  and invertibility is compositional (`bind₁`), i.e. a genuine polynomial
  inverse, not merely a bijection on points;
* `counterexample` — the Alpöge map as a `RegularFunction K (Fin 3) (Fin 3)`;
* `isUnit_jacobian_det` — its Jacobian determinant is the unit `-2`;
* `no_polynomial_inverse` — it admits no two-sided polynomial inverse over
  any characteristic-zero field: a polynomial left inverse would make the
  induced point map injective, contradicting `Alpoge.not_injective`;
* `jacobian_conjecture_false` — the negation of the mirrored conjecture.

The compositional conclusion is *stronger* than point-bijectivity, so its
failure follows from the failure of injectivity on `K`-points.
-/

namespace Alpoge.FormalConjecturesJC

open MvPolynomial

variable (k : Type*) [Field k] (σ τ ι : Type*)

/-- Mirrored: a vector-valued polynomial function. -/
abbrev RegularFunction := τ → MvPolynomial σ k

variable {k σ τ ι}

/-- Mirrored: the Jacobian of a vector-valued polynomial function, viewed as
a matrix of formal partial derivatives. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (F j)

/-- Mirrored: composition of regular functions by polynomial substitution. -/
noncomputable def comp (F : RegularFunction k σ τ)
    (G : RegularFunction k τ ι) : RegularFunction k σ ι :=
  fun i => MvPolynomial.bind₁ F (G i)

variable (k σ) in
/-- Mirrored: the identity regular function. -/
protected noncomputable def id : RegularFunction k σ σ := MvPolynomial.X

/-- The induced map on `K`-points of a regular function. -/
noncomputable def pointMap (F : RegularFunction k σ τ) : (σ → k) → (τ → k) :=
  fun v i => eval v (F i)

theorem pointMap_comp (F : RegularFunction k σ τ)
    (G : RegularFunction k τ ι) :
    pointMap (comp F G) = pointMap G ∘ pointMap F := by
  funext v i
  simp only [pointMap, comp, Function.comp_apply, bind₁, aeval_def,
    algebraMap_eq, eval_eval₂]
  have hC : (eval v).comp (C : k →+* MvPolynomial σ k) = RingHom.id k := by
    ext a
    simp
  rw [hC, eval₂_id]
  rfl

theorem pointMap_id : pointMap (FormalConjecturesJC.id k σ) = _root_.id := by
  funext v i
  simp [pointMap, FormalConjecturesJC.id]

section Counterexample

variable {K : Type*} [Field K]

/-- The Alpöge counterexample as a mirrored `RegularFunction`. -/
noncomputable def counterexample : RegularFunction K (Fin 3) (Fin 3) :=
  ![(1 + X 0 * X 1) ^ 3 * X 2 +
      X 1 ^ 2 * (1 + X 0 * X 1) * (4 + 3 * X 0 * X 1),
    X 1 + 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 +
      3 * X 0 * X 1 ^ 2 * (4 + 3 * X 0 * X 1),
    2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2]

private theorem pderiv_ofNat'' {σ R : Type*} [CommSemiring R] {i : σ} (n : ℕ)
    [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ R) = 0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial σ R) n]
  exact pderiv_C

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8000 in
/-- The mirrored Jacobian determinant of the counterexample is `-2`. -/
theorem jacobian_det_counterexample :
    (Jacobian (counterexample (K := K))).det = -2 := by
  have h : (Jacobian (counterexample (K := K))).det =
      (!![pderiv 0 (counterexample (K := K) 0),
          pderiv 0 (counterexample (K := K) 1),
          pderiv 0 (counterexample (K := K) 2);
         pderiv 1 (counterexample (K := K) 0),
          pderiv 1 (counterexample (K := K) 1),
          pderiv 1 (counterexample (K := K) 2);
         pderiv 2 (counterexample (K := K) 0),
          pderiv 2 (counterexample (K := K) 1),
          pderiv 2 (counterexample (K := K) 2)] :
        Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) K)).det := by
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Jacobian, Matrix.of_apply]
  rw [h]
  simp only [counterexample, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    map_add, map_sub, pderiv_mul, pderiv_pow, pderiv_ofNat'', pderiv_one,
    pderiv_X_self, pderiv_X, Pi.single_apply, Nat.cast_ofNat, Fin.reduceEq,
    reduceIte]
  norm_num
  ring

/-- The mirrored Jacobian determinant is a unit — the hypothesis of the
formal-conjectures statement holds for the counterexample. -/
theorem isUnit_jacobian_det [CharZero K] :
    IsUnit (Jacobian (counterexample (K := K))).det := by
  rw [jacobian_det_counterexample]
  refine IsUnit.neg ?_
  rw [show ((2 : MvPolynomial (Fin 3) K)) = C 2 from (map_ofNat C 2).symm]
  exact IsUnit.map (C : K →+* MvPolynomial (Fin 3) K)
    (isUnit_iff_ne_zero.mpr two_ne_zero)

/-- The point map of the mirrored counterexample agrees with the concrete
Alpöge map `F`. -/
theorem pointMap_counterexample (v : Fin 3 → K) :
    pointMap (counterexample (K := K)) v =
      ![(F K (v 0, v 1, v 2)).1, (F K (v 0, v 1, v 2)).2.1,
        (F K (v 0, v 1, v 2)).2.2] := by
  funext i
  fin_cases i <;>
    simp [pointMap, counterexample, F, eval_add, eval_sub, eval_mul,
      eval_pow, eval_X, eval_ofNat]

/-- **No polynomial inverse.**  Over any characteristic-zero field, the
counterexample admits no two-sided compositional inverse: a polynomial
right-composition inverse would make the induced point map injective,
contradicting the three-point collision. -/
theorem no_polynomial_inverse [CharZero K] :
    ¬ ∃ G : RegularFunction K (Fin 3) (Fin 3),
        comp G (counterexample (K := K)) = FormalConjecturesJC.id K (Fin 3) ∧
        comp (counterexample (K := K)) G = FormalConjecturesJC.id K (Fin 3) := by
  rintro ⟨G, -, hFG⟩
  have hleft : pointMap G ∘ pointMap (counterexample (K := K)) = _root_.id := by
    rw [← pointMap_comp, hFG, pointMap_id]
  have hinj : Function.Injective (pointMap (counterexample (K := K))) :=
    Function.LeftInverse.injective (g := pointMap G) (congrFun hleft)
  apply Alpoge.not_injective K
  intro p q hpq
  have hv :
      pointMap (counterexample (K := K)) ![p.1, p.2.1, p.2.2] =
        pointMap (counterexample (K := K)) ![q.1, q.2.1, q.2.2] := by
    rw [pointMap_counterexample, pointMap_counterexample]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [hpq]
  have := hinj hv
  have h0 := congrFun this 0
  have h1 := congrFun this 1
  have h2 := congrFun this 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

end Counterexample

/-- **The formal-conjectures Jacobian Conjecture statement is false.**
This is the negation of the statement in
`google-deepmind/formal-conjectures` (commit `4fac2db2`), witnessed by
`k = ℚ`, `σ = Fin 3`, and the Alpöge map. -/
theorem jacobian_conjecture_false :
    ¬ ∀ (k : Type) [Field k] [CharZero k] (σ : Type) [Fintype σ] [DecidableEq σ]
        (F : RegularFunction k σ σ), IsUnit (Jacobian F).det →
        ∃ G : RegularFunction k σ σ,
          comp G F = FormalConjecturesJC.id k σ ∧
          comp F G = FormalConjecturesJC.id k σ := by
  intro h
  exact no_polynomial_inverse
    (h ℚ (Fin 3) (counterexample (K := ℚ)) isUnit_jacobian_det)

end Alpoge.FormalConjecturesJC
