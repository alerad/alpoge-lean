import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Alpöge's Keller map: a counterexample to the Jacobian Conjecture


```text
F (x, y, z) =
  ((1+xy)³ z + y² (1+xy)(4+3xy),
   y + 3x (1+xy)² z + 3x y² (4+3xy),
   2x − 3x²y − x³ z)
```

has formal Jacobian determinant identically `-2` over `ℤ`, yet identifies the
three rational points `(0, 0, -1/4)`, `(1, -3/2, 13/2)`, `(-1, 3/2, 13/2)`.

Conceptually: the Jacobian determinant is a nonzero constant (the Keller
condition), so the differential of `F` is invertible at every point — yet the
map identifies distinct points.  An everywhere-invertible differential does
not imply global injectivity.

The headline results are:

* `jacobian_det`: the formal Jacobian determinant is the constant `-2`;
* `F_eq_eval`: the concrete map is evaluation of the formal polynomials, so
  the Keller condition is a statement about the same object;
* `F_p₀_eq`, `F_p₁_eq`, `F_p₂_eq`: the three witnesses share one image;
* `not_injective`: `F` is not injective over any characteristic-zero field;
* `keller_counterexample`: the combined counterexample statement.

The projective fiber theorem below identifies every fiber with the simple
rational roots of one binary cubic.  It yields the arithmetic `0/1/3` law over
arbitrary characteristic-zero fields and, over algebraically closed fields,
the exact image: the complement of `12a = b²`, `3bc = 4`.  The identification
of formal partials with analytic Fréchet derivatives over `ℂ` is not formalized
here, nor is the degree of the induced function-field extension.
-/

namespace Alpoge

open MvPolynomial

/-- Formal polynomials over the integers; `X 0, X 1, X 2` are `x, y, z`. -/
local notation "P" => MvPolynomial (Fin 3) ℤ

noncomputable section Formal

/-- First component of the counterexample map. -/
def f₁ : P :=
  (1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) * (4 + 3 * X 0 * X 1)

/-- Second component of the counterexample map. -/
def f₂ : P :=
  X 1 + 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 + 3 * X 0 * X 1 ^ 2 * (4 + 3 * X 0 * X 1)

/-- Third component of the counterexample map. -/
def f₃ : P :=
  2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2

/-- The formal Jacobian matrix of `(f₁, f₂, f₃)` in the variables `x, y, z`. -/
def jacobian : Matrix (Fin 3) (Fin 3) P :=
  !![pderiv 0 f₁, pderiv 1 f₁, pderiv 2 f₁;
     pderiv 0 f₂, pderiv 1 f₂, pderiv 2 f₂;
     pderiv 0 f₃, pderiv 1 f₃, pderiv 2 f₃]

private theorem pderiv_ofNat {σ R : Type*} [CommSemiring R] {i : σ} (n : ℕ)
    [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ R) = 0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial σ R) n]
  exact pderiv_C

set_option maxHeartbeats 1600000 in
-- The fully expanded 3×3 polynomial determinant requires a larger normalization budget.
set_option maxRecDepth 8000 in
/-- **Keller condition.**  The formal Jacobian determinant is constantly `-2`. -/
theorem jacobian_det : jacobian.det = -2 := by
  simp only [jacobian, f₁, f₂, f₃, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.tail_cons, map_add,
    map_sub, pderiv_mul, pderiv_pow, pderiv_ofNat, pderiv_one, pderiv_X_self,
    pderiv_X, Pi.single_apply, Nat.cast_ofNat, Fin.reduceEq, reduceIte]
  norm_num
  ring

end Formal

section Concrete

variable (K : Type*) [Field K]

/-- The counterexample map on points over a field. -/
def F : K × K × K → K × K × K := fun p =>
  ((1 + p.1 * p.2.1) ^ 3 * p.2.2 +
      p.2.1 ^ 2 * (1 + p.1 * p.2.1) * (4 + 3 * p.1 * p.2.1),
   p.2.1 + 3 * p.1 * (1 + p.1 * p.2.1) ^ 2 * p.2.2 +
      3 * p.1 * p.2.1 ^ 2 * (4 + 3 * p.1 * p.2.1),
   2 * p.1 - 3 * p.1 ^ 2 * p.2.1 - p.1 ^ 3 * p.2.2)

/-- The concrete map is evaluation of the formal polynomials, so the Keller
condition `jacobian_det` and the three-point collision below concerns the same
object. -/
theorem F_eq_eval (p : K × K × K) :
    F K p =
      (aeval ![p.1, p.2.1, p.2.2] f₁,
       aeval ![p.1, p.2.1, p.2.2] f₂,
       aeval ![p.1, p.2.1, p.2.2] f₃) := by
  obtain ⟨x, y, z⟩ := p
  simp only [F, f₁, f₂, f₃, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- First point of the three-point collision. -/
def p₀ : K × K × K := (0, 0, -(1 / 4))

/-- Second point of the three-point collision. -/
def p₁ : K × K × K := (1, -(3 / 2), 13 / 2)

/-- Third point of the three-point collision. -/
def p₂ : K × K × K := (-1, 3 / 2, 13 / 2)

theorem F_p₀_eq : F K (p₀ K) = (-(1 / 4), 0, 0) := by
  simp [F, p₀]

theorem F_p₁_eq [CharZero K] : F K (p₁ K) = (-(1 / 4), 0, 0) := by
  simp only [F, p₁, Prod.mk.injEq]
  norm_num

theorem F_p₂_eq [CharZero K] : F K (p₂ K) = (-(1 / 4), 0, 0) := by
  simp only [F, p₂, Prod.mk.injEq]
  norm_num

variable [CharZero K]

theorem p₁_ne_p₂ : p₁ K ≠ p₂ K := by
  norm_num [p₁, p₂, Prod.ext_iff]

/-- The map `F` identifies two distinct points: it is not injective over any
characteristic-zero field. -/
theorem not_injective : ¬ Function.Injective (F K) := by
  intro h
  exact p₁_ne_p₂ K (h ((F_p₁_eq K).trans (F_p₂_eq K).symm))


/-- **Counterexample to the Jacobian Conjecture (Alpöge, 2026).**  The map has
constant formal Jacobian determinant `-2` and is not injective. -/
theorem keller_counterexample :
    jacobian.det = -2 ∧ ¬ Function.Injective (F K) :=
  ⟨jacobian_det, not_injective K⟩

/-- **The missed curve.**  No source point is sent to any point of the rational curve
`s ↦ (s²/12, s, 4/(3s))`.  The proof is a Nullstellensatz certificate: explicit
degree-four cofactors witness `2sx` in the fiber ideal, forcing `x = 0`, which
contradicts the third observed coordinate.  Found by eliminating the fiber
system in the coordinates `u = 1 + xy`, `τ = f₃/x`, where the fiber cubic
degenerates to `0·u = 4a` exactly on this curve. -/
theorem missed_curve (s : K) (hs : s ≠ 0) (p : K × K × K) :
    F K p ≠ (s ^ 2 / 12, s, 4 / (3 * s)) := by
  obtain ⟨x, y, z⟩ := p
  intro hFp
  simp only [F, Prod.mk.injEq] at hFp
  obtain ⟨h1, h2, h3⟩ := hFp
  have h3' : s * (2 * x - 3 * x ^ 2 * y - x ^ 3 * z) = 4 / 3 := by
    rw [h3]
    field_simp
  have hx : (2 : K) * s * x = 0 := by
    linear_combination
      (-6 * s * x ^ 3 + 12 * x ^ 3 * y + 12 * x ^ 2) * h1 +
        (s ^ 2 * x ^ 3 / 2 + s * x ^ 3 * y + 2 * s * x ^ 2 - 4 * x ^ 3 * y ^ 2 -
          8 * x ^ 2 * y - 4 * x) * h2 +
        (3 * s * x ^ 3 * y ^ 2 / 2 + 3 * s * x ^ 2 * y + 3 * s * x / 2 -
          3 * x ^ 3 * y ^ 3 - 6 * x ^ 2 * y ^ 2 - 3 * x * y) * h3'
  have hx0 : x = 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hs)
    · exact h
  rw [hx0] at h3'
  simp only [mul_zero, zero_mul, sub_zero, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, mul_comm] at h3'
  norm_num at h3'

/-- **Non-surjectivity.**  The Keller map misses the explicit rational
point `(1/12, 1, 4/3)`: its image is a proper subset of the codomain.
Together with `not_injective`, the first Jacobian-Conjecture counterexample is
doubly non-invertible — it identifies points and omits values. -/
theorem not_surjective : ¬ Function.Surjective (F K) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (1 / 12, 1, 4 / 3)
  refine missed_curve K 1 one_ne_zero p ?_
  rw [hp]
  norm_num

/-- The omitted point, stated against the range: `Set.range (F K)` omits
`(1/12, 1, 4/3)`. -/
theorem missed_point_not_mem_range :
    (1 / 12, 1, 4 / 3) ∉ Set.range (F K) := by
  rintro ⟨p, hp⟩
  refine missed_curve K 1 one_ne_zero p ?_
  rw [hp]
  norm_num

omit [CharZero K] in
/-- The plane `c = 0` lies entirely in the image: an explicit polynomial
section of the map over that plane. -/
theorem plane_section (a b : K) : F K (0, b, a - 4 * b ^ 2) = (a, b, 0) := by
  simp only [F, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- Explicit attained targets on the discriminant wall along the axis
`a = b = 0`: one rational preimage survives there. -/
theorem wall_axis_attained (c : K) : F K (c / 2, 0, 0) = (0, 0, c) := by
  simp only [F, Prod.mk.injEq]
  refine ⟨by ring, by ring, ?_⟩
  field_simp
  ring

/-- **The three-point fiber, packaged.**  Three pairwise distinct points over
`(-1/4, 0, 0)`. -/
theorem three_point_fiber :
    F K (p₀ K) = (-(1 / 4), 0, 0) ∧ F K (p₁ K) = (-(1 / 4), 0, 0) ∧
      F K (p₂ K) = (-(1 / 4), 0, 0) ∧
      p₀ K ≠ p₁ K ∧ p₀ K ≠ p₂ K ∧ p₁ K ≠ p₂ K :=
  ⟨F_p₀_eq K, F_p₁_eq K, F_p₂_eq K,
    by norm_num [p₀, p₁, Prod.ext_iff],
    by norm_num [p₀, p₂, Prod.ext_iff],
    p₁_ne_p₂ K⟩

set_option maxHeartbeats 4000000 in
-- Checking the explicit 233-term Nullstellensatz certificate is intentionally computation-heavy.
set_option linter.style.longLine false in
omit [CharZero K] in
/-- **Certified fiber cubic.**  Every preimage of `(a, b, c)` satisfies
the sheet cubic: with `u = 1 + xy` and
`W = 27a²c² − 18abc + 16a + b³c − b²`,

```text
c² · (W u³ + (b² − 12a) u − 4a) = 0.
```

For `c ≠ 0` this bounds the rational fiber by the roots of a cubic whose
leading coefficient is exactly the discriminant scalar `W`: three sheets off
the wall `V(W)`, a linear equation on it, and an inconsistent equation exactly
on the missed curve (`W = 0`, `b² = 12a`, `a ≠ 0`).  The proof is one explicit
Nullstellensatz certificate obtained from the extended Euclidean cofactors of
the fiber resultant. -/
theorem fiber_u_elimination (x y z a b c : K)
    (h : F K (x, y, z) = (a, b, c)) :
    c ^ 2 * ((27 * a ^ 2 * c ^ 2 - 18 * a * b * c + 16 * a + b ^ 3 * c - b ^ 2)
        * (1 + x * y) ^ 3 + (b ^ 2 - 12 * a) * (1 + x * y) - 4 * a) = 0 := by
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  linear_combination
    (-27*a*c^2*x^9*y^3*z^2 - 162*a*c^2*x^8*y^4*z - 81*a*c^2*x^8*y^2*z^2 - 243*a*c^2*x^7*y^5 - 378*a*c^2*x^7*y^3*z - 81*a*c^2*x^7*y*z^2 - 405*a*c^2*x^6*y^4 - 162*a*c^2*x^6*y^2*z - 27*a*c^2*x^6*z^2 + 135*a*c^2*x^5*y^3 + 162*a*c^2*x^5*y*z + 405*a*c^2*x^4*y^2 + 108*a*c^2*x^4*z - 108*a*c^2*x^2 + 9*b*c*x^12*y^4*z^3 + 81*b*c*x^11*y^5*z^2 + 36*b*c*x^11*y^3*z^3 + 243*b*c*x^10*y^6*z + 270*b*c*x^10*y^4*z^2 + 54*b*c*x^10*y^2*z^3 + 243*b*c*x^9*y^7 + 648*b*c*x^9*y^5*z + 285*b*c*x^9*y^3*z^2 + 36*b*c*x^9*y*z^3 + 486*b*c*x^8*y^6 + 360*b*c*x^8*y^4*z + 48*b*c*x^8*y^2*z^2 + 9*b*c*x^8*z^3 - 27*b*c*x^7*y^5 - 312*b*c*x^7*y^3*z - 84*b*c*x^7*y*z^2 - 468*b*c*x^6*y^4 - 291*b*c*x^6*y^2*z - 36*b*c*x^6*z^2 - 102*b*c*x^5*y^3 + 12*b*c*x^5*y*z + 120*b*c*x^4*y^2 + 36*b*c*x^4*z + 24*b*c*x^3*y - 12*x^12*y^4*z^3 - 108*x^11*y^5*z^2 - 42*x^11*y^3*z^3 - 324*x^10*y^6*z - 306*x^10*y^4*z^2 - 48*x^10*y^2*z^3 - 324*x^9*y^7 - 702*x^9*y^5*z - 196*x^9*y^3*z^2 - 18*x^9*y*z^3 - 486*x^8*y^6 - 24*x^8*y^4*z + 78*x^8*y^2*z^2 + 396*x^7*y^5 + 514*x^7*y^3*z + 72*x^7*y*z^2 + 450*x^6*y^4 + 48*x^6*y^2*z - 232*x^5*y^3 - 72*x^5*y*z - 24*x^4*y^2) * h1 +
    (9*a*c^2*x^9*y^4*z^2 + 54*a*c^2*x^8*y^5*z + 36*a*c^2*x^8*y^3*z^2 + 81*a*c^2*x^7*y^6 + 180*a*c^2*x^7*y^4*z + 54*a*c^2*x^7*y^2*z^2 + 216*a*c^2*x^6*y^5 + 177*a*c^2*x^6*y^3*z + 36*a*c^2*x^6*y*z^2 + 81*a*c^2*x^5*y^4 - 6*a*c^2*x^5*y^2*z + 9*a*c^2*x^5*z^2 - 192*a*c^2*x^4*y^3 - 93*a*c^2*x^4*y*z - 132*a*c^2*x^3*y^2 - 36*a*c^2*x^3*z + 42*a*c^2*x^2*y + 36*a*c^2*x + b^2*c^2*x^6*y^3*z + 3*b^2*c^2*x^5*y^4 + 3*b^2*c^2*x^5*y^2*z + 7*b^2*c^2*x^4*y^3 + 3*b^2*c^2*x^4*y*z + 3*b^2*c^2*x^3*y^2 + b^2*c^2*x^3*z - 3*b^2*c^2*x^2*y - 2*b^2*c^2*x - 3*b*c*x^12*y^5*z^3 - 27*b*c*x^11*y^6*z^2 - 15*b*c*x^11*y^4*z^3 - 81*b*c*x^10*y^7*z - 117*b*c*x^10*y^5*z^2 - 30*b*c*x^10*y^3*z^3 - 81*b*c*x^9*y^8 - 297*b*c*x^9*y^6*z - 184*b*c*x^9*y^4*z^2 - 30*b*c*x^9*y^2*z^3 - 243*b*c*x^8*y^7 - 330*b*c*x^8*y^5*z - 108*b*c*x^8*y^3*z^2 - 15*b*c*x^8*y*z^3 - 144*b*c*x^7*y^6 - 2*b*c*x^7*y^4*z + 15*b*c*x^7*y^2*z^2 - 3*b*c*x^7*z^3 + 180*b*c*x^6*y^5 + 206*b*c*x^6*y^3*z + 41*b*c*x^6*y*z^2 + 182*b*c*x^5*y^4 + 84*b*c*x^5*y^2*z + 12*b*c*x^5*z^2 - 28*b*c*x^4*y^3 - 22*b*c*x^4*y*z - 48*b*c*x^3*y^2 - 12*b*c*x^3*z + 4*x^12*y^5*z^3 + 36*x^11*y^6*z^2 + 18*x^11*y^4*z^3 + 108*x^10*y^7*z + 138*x^10*y^5*z^2 + 30*x^10*y^3*z^3 + 108*x^9*y^8 + 342*x^9*y^6*z + 166*x^9*y^4*z^2 + 22*x^9*y^2*z^3 + 270*x^8*y^7 + 234*x^8*y^5*z + 36*x^8*y^3*z^2 + 6*x^8*y*z^3 + 18*x^7*y^6 - 178*x^7*y^4*z - 52*x^7*y^2*z^2 - 296*x^6*y^5 - 186*x^6*y^3*z - 24*x^6*y*z^2 - 56*x^5*y^4 + 16*x^5*y^2*z + 96*x^4*y^3 + 24*x^4*y*z) * h2 +
    (-27*a^2*c^3*x^3*y^3 - 81*a^2*c^3*x^2*y^2 - 81*a^2*c^3*x*y - 27*a^2*c^3 + 27*a^2*c^2*x^6*y^3*z + 81*a^2*c^2*x^5*y^4 + 81*a^2*c^2*x^5*y^2*z + 189*a^2*c^2*x^4*y^3 + 81*a^2*c^2*x^4*y*z + 81*a^2*c^2*x^3*y^2 + 27*a^2*c^2*x^3*z - 81*a^2*c^2*x^2*y - 54*a^2*c^2*x + 18*a*b*c^2*x^3*y^3 + 54*a*b*c^2*x^2*y^2 + 54*a*b*c^2*x*y + 18*a*b*c^2 - 9*a*b*c*x^9*y^4*z^2 - 54*a*b*c*x^8*y^5*z - 36*a*b*c*x^8*y^3*z^2 - 81*a*b*c*x^7*y^6 - 180*a*b*c*x^7*y^4*z - 54*a*b*c*x^7*y^2*z^2 - 216*a*b*c*x^6*y^5 - 195*a*b*c*x^6*y^3*z - 36*a*b*c*x^6*y*z^2 - 135*a*b*c*x^5*y^4 - 48*a*b*c*x^5*y^2*z - 9*a*b*c*x^5*z^2 + 66*a*b*c*x^4*y^3 + 39*a*b*c*x^4*y*z + 78*a*b*c*x^3*y^2 + 18*a*b*c*x^3*z + 12*a*b*c*x^2*y - 12*a*c*x^6*y^4*z - 36*a*c*x^5*y^5 - 42*a*c*x^5*y^3*z - 102*a*c*x^4*y^4 - 48*a*c*x^4*y^2*z - 76*a*c*x^3*y^3 - 18*a*c*x^3*y*z - 6*a*c*x^2*y^2 + 12*a*x^9*y^4*z^2 + 72*a*x^8*y^5*z + 42*a*x^8*y^3*z^2 + 108*a*x^7*y^6 + 204*a*x^7*y^4*z + 48*a*x^7*y^2*z^2 + 234*a*x^6*y^5 + 136*a*x^6*y^3*z + 18*a*x^6*y*z^2 + 24*a*x^5*y^4 - 36*a*x^5*y^2*z - 134*a*x^4*y^3 - 36*a*x^4*y*z - 12*a*x^3*y^2 - b^3*c^2*x^3*y^3 - 3*b^3*c^2*x^2*y^2 - 3*b^3*c^2*x*y - b^3*c^2 + 3*b^2*c*x^9*y^5*z^2 + 18*b^2*c*x^8*y^6*z + 15*b^2*c*x^8*y^4*z^2 + 27*b^2*c*x^7*y^7 + 78*b^2*c*x^7*y^5*z + 30*b^2*c*x^7*y^3*z^2 + 99*b^2*c*x^6*y^6 + 124*b^2*c*x^6*y^4*z + 30*b^2*c*x^6*y^2*z^2 + 114*b^2*c*x^5*y^5 + 78*b^2*c*x^5*y^3*z + 15*b^2*c*x^5*y*z^2 + 16*b^2*c*x^4*y^4 + 3*b^2*c*x^4*z^2 - 50*b^2*c*x^3*y^3 - 20*b^2*c*x^3*y*z - 24*b^2*c*x^2*y^2 - 6*b^2*c*x^2*z - 4*b*x^9*y^5*z^2 - 24*b*x^8*y^6*z - 18*b*x^8*y^4*z^2 - 36*b*x^7*y^7 - 92*b*x^7*y^5*z - 30*b*x^7*y^3*z^2 - 114*b*x^6*y^6 - 112*b*x^6*y^4*z - 22*b*x^6*y^2*z^2 - 82*b*x^5*y^5 - 30*b*x^5*y^3*z - 6*b*x^5*y*z^2 + 44*b*x^4*y^4 + 26*b*x^4*y^2*z + 48*b*x^3*y^3 + 12*b*x^3*y*z) * h3

end Concrete


section TauChart

/-! ### The τ-chart: fiber combinatorics in collapsed coordinates

For a target `(a, b, c)` with `c ≠ 0`, every fiber point has `x ≠ 0`, and the
substitution `t = c/x`, `u = 1 + xy` identifies the fiber of `F` with the
common zero set (`t ≠ 0`) of two small polynomials `chartG₁`, `chartG₂` in the
scaled invariants `A = ac²`, `r = bc` (`fiber_tau_coordinates`,
`reconstruct_fiber`: the identification is a genuine equivalence, with
explicit inverse).  Sheets are governed by the τ-cubic `sheetCubic`, whose
constant term is `-c²W` (`sheetCubic_zero`): the multiplicity of a `t`-root
equals the number of sheets over it.  Over a simple root (`wallD ≠ 0`) the
unique sheet is `u = wallN/(t·wallD)` (`simple_root_G₁`, `simple_root_G₂`);
over a double root `wallD = 0` forces `wallN = 0`
(`wallN_eq_zero_of_double_root`), the two chart equations become proportional
(`double_root_reduction`), and the square form `three_mul_G₂` exhibits exactly
two sheets as square roots of `9t`.  The `c = 0` chart is quadratic instead
(`fiber_czero_equation`, `reconstruct_czero`), with `plane_section` as the
`x = 0` sheet.

The τ-cubic and the `u`-cubic of `fiber_u_elimination` explain the discriminant
wall twice: in the `u`-cubic the leading coefficient `W` dies and the degree
drops `3 → 1`; in the τ-cubic the constant term `c²W` dies and two roots
collapse to the forbidden value `t = 0`.

Everything here is a certified polynomial identity over an arbitrary field
(characteristic assumptions are marked where genuinely needed).  Root
existence and the exact `3/1/0` fiber count over an algebraically closed
field are deliberately not claimed in this section. -/

variable {K : Type*} [Field K]

/-- First chart polynomial; `chartG₁ (a*c²) t u = 0` encodes the first
observed coordinate. -/
def chartG₁ (A t u : K) : K := -A - t ^ 3 * u ^ 3 + t ^ 2 * u ^ 2 + t ^ 2 * u

/-- Second chart polynomial; `chartG₂ (b*c) t u = 0` encodes the second
observed coordinate. -/
def chartG₂ (r t u : K) : K := -r - 3 * t ^ 2 * u ^ 2 + 4 * t * u + 2 * t

/-- The τ-cubic carrying the sheets of the fiber. -/
def sheetCubic (A r t : K) : K :=
  2 * t ^ 3 + (3 * r - 4) * t ^ 2 -
    (27 * A ^ 2 - 18 * A * r + 16 * A + r ^ 3 - r ^ 2)

/-- Double-root detector: the τ-cubic has algebraic derivative `2t · wallD`
(see `sheetCubic_sub`). -/
def wallD (r t : K) : K := 3 * r + 3 * t - 4

/-- Numerator of the unique sheet over a simple τ-root. -/
def wallN (A r t : K) : K := 9 * A - r + 2 * t

/-- The constant term of the τ-cubic is exactly `-c²·W`. -/
theorem sheetCubic_zero (a b c : K) :
    sheetCubic (a * c ^ 2) (b * c) 0 =
      -(c ^ 2 *
        (27 * a ^ 2 * c ^ 2 - 18 * a * b * c + 16 * a + b ^ 3 * c - b ^ 2)) := by
  simp only [sheetCubic]
  ring

/-- **Chart coordinates.**  Over a target with `c ≠ 0`, every fiber point has
`x ≠ 0` and satisfies both chart equations at `t = c/x`, `u = 1 + xy`. -/
theorem fiber_tau_coordinates {x y z a b c : K} (hc : c ≠ 0)
    (h : F K (x, y, z) = (a, b, c)) :
    x ≠ 0 ∧ c / x ≠ 0 ∧
      chartG₁ (a * c ^ 2) (c / x) (1 + x * y) = 0 ∧
      chartG₂ (b * c) (c / x) (1 + x * y) = 0 := by
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx : x ≠ 0 := by
    rintro rfl
    exact hc (by linear_combination -h3)
  refine ⟨hx, div_ne_zero hc hx, ?_, ?_⟩
  · simp only [chartG₁]
    field_simp
    linear_combination (c ^ 2 * x ^ 3) * h1 + (c ^ 2 * (1 + x * y) ^ 3) * h3
  · simp only [chartG₂]
    field_simp
    linear_combination (c * x ^ 2) * h2 + (3 * c * (1 + x * y) ^ 2) * h3

/-- **Chart reconstruction.**  Every chart solution with `t ≠ 0` arises from
an actual fiber point, by explicit formulas; with `fiber_tau_coordinates`
this makes the `c ≠ 0` fiber equivalent to the chart solution set. -/
theorem reconstruct_fiber {a b c t u : K} (hc : c ≠ 0) (ht : t ≠ 0)
    (h1 : chartG₁ (a * c ^ 2) t u = 0) (h2 : chartG₂ (b * c) t u = 0) :
    F K (c / t, t * (u - 1) / c, t ^ 2 * (5 - 3 * u - t) / c ^ 2) = (a, b, c) := by
  simp only [chartG₁] at h1
  simp only [chartG₂] at h2
  simp only [F, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2
  · field_simp
    ring

/-- **The τ-cubic annihilates the chart**, with polynomial cofactors and no
localization: every common chart zero is a root of the sheet cubic. -/
theorem tau_cubic {A r t u : K}
    (h1 : chartG₁ A t u = 0) (h2 : chartG₂ r t u = 0) :
    sheetCubic A r t = 0 := by
  simp only [chartG₁] at h1
  simp only [chartG₂] at h2
  simp only [sheetCubic]
  linear_combination
    (27 * A + 9 * r * t * u - 15 * r + 9 * t ^ 2 * u - 12 * t * u - 6 * t + 16) * h1 +
      (-9 * A * t * u - 3 * A + r ^ 2 - 3 * r * t ^ 2 * u ^ 2 + 4 * r * t * u +
        2 * r * t - r - 3 * t ^ 3 * u ^ 2 + 4 * t ^ 2 * u ^ 2 + t ^ 2 * u + t ^ 2 -
        4 * t * u - 2 * t) * h2

/-- Simple-root sheet, second equation: the candidate `u = wallN/(t·wallD)`
clears `chartG₂` to `9 · sheetCubic`. -/
private theorem simple_root_G₂_aux {A r t v : K}
    (hv : v * (t * (3 * r + 3 * t - 4)) = 9 * A - r + 2 * t) :
    (3 * r + 3 * t - 4) ^ 2 * (-r - 3 * t ^ 2 * v ^ 2 + 4 * t * v + 2 * t) =
      9 * (2 * t ^ 3 + (3 * r - 4) * t ^ 2 -
        (27 * A ^ 2 - 18 * A * r + 16 * A + r ^ 3 - r ^ 2)) := by
  linear_combination
    (-3 * (v * (t * (3 * r + 3 * t - 4)) + (9 * A - r + 2 * t)) +
      4 * (3 * r + 3 * t - 4)) * hv

theorem simple_root_G₂ (A r t : K) (ht : t ≠ 0) (hD : wallD r t ≠ 0) :
    wallD r t ^ 2 * chartG₂ r t (wallN A r t / (t * wallD r t)) =
      9 * sheetCubic A r t := by
  have hd : 3 * r + 3 * t - 4 ≠ 0 := by simpa [wallD] using hD
  have hv : wallN A r t / (t * wallD r t) * (t * (3 * r + 3 * t - 4)) =
      9 * A - r + 2 * t := by
    rw [show t * (3 * r + 3 * t - 4) = t * wallD r t from by rw [wallD]]
    rw [div_mul_cancel₀ _ (mul_ne_zero ht hD), wallN]
  simpa only [chartG₂, wallD, wallN, sheetCubic] using simple_root_G₂_aux hv

/-- Simple-root sheet, first equation: the same candidate clears `chartG₁` to
`(27A + 9t − 4) · sheetCubic`. -/
private theorem simple_root_G₁_aux {A r t v : K}
    (hv : v * (t * (3 * r + 3 * t - 4)) = 9 * A - r + 2 * t) :
    (3 * r + 3 * t - 4) ^ 3 * (-A - t ^ 3 * v ^ 3 + t ^ 2 * v ^ 2 + t ^ 2 * v) =
      (27 * A + 9 * t - 4) * (2 * t ^ 3 + (3 * r - 4) * t ^ 2 -
        (27 * A ^ 2 - 18 * A * r + 16 * A + r ^ 3 - r ^ 2)) := by
  linear_combination
    (-((v * (t * (3 * r + 3 * t - 4))) ^ 2 +
        v * (t * (3 * r + 3 * t - 4)) * (9 * A - r + 2 * t) +
        (9 * A - r + 2 * t) ^ 2) +
      (3 * r + 3 * t - 4) * (v * (t * (3 * r + 3 * t - 4)) + (9 * A - r + 2 * t)) +
      t * (3 * r + 3 * t - 4) ^ 2) * hv

theorem simple_root_G₁ (A r t : K) (ht : t ≠ 0) (hD : wallD r t ≠ 0) :
    wallD r t ^ 3 * chartG₁ A t (wallN A r t / (t * wallD r t)) =
      (27 * A + 9 * t - 4) * sheetCubic A r t := by
  have hv : wallN A r t / (t * wallD r t) * (t * (3 * r + 3 * t - 4)) =
      9 * A - r + 2 * t := by
    rw [show t * (3 * r + 3 * t - 4) = t * wallD r t from by rw [wallD]]
    rw [div_mul_cancel₀ _ (mul_ne_zero ht hD), wallN]
  simpa only [chartG₁, wallD, wallN, sheetCubic] using simple_root_G₁_aux hv

/-- At a double root of the τ-cubic the sheet numerator vanishes:
`3·sheetCubic + wallN² = -wallD·(-12A + r² - rt - 2t²)`. -/
theorem wallN_eq_zero_of_double_root {A r t : K}
    (hQ : sheetCubic A r t = 0) (hD : wallD r t = 0) :
    wallN A r t = 0 := by
  have hsq : wallN A r t ^ 2 = 0 := by
    simp only [sheetCubic] at hQ
    simp only [wallD] at hD
    simp only [wallN]
    linear_combination (-3 : K) * hQ + (12 * A - r ^ 2 + r * t + 2 * t ^ 2) * hD
  exact sq_eq_zero_iff.mp hsq

/-- **Double-root reduction.**  Under `wallD = wallN = 0` the two chart
equations are proportional: the certificate is `9·chartG₁ − (3tu+1)·chartG₂ =
tu·wallD − wallN`. -/
theorem double_root_reduction {A r t : K} (u : K)
    (hD : wallD r t = 0) (hN : wallN A r t = 0) :
    9 * chartG₁ A t u = (3 * t * u + 1) * chartG₂ r t u := by
  simp only [wallD] at hD
  simp only [wallN] at hN
  simp only [chartG₁, chartG₂]
  linear_combination (t * u) * hD - hN

/-- Square form of the second chart equation:
`3·chartG₂ = 9t − (3tu − 2)² − wallD`.  Under `wallD = 0` the sheets over the
double root are exactly the square roots of `9t`; in particular there are two
of them over an algebraically closed field of characteristic `≠ 2, 3` when
`t ≠ 0`.  (In general `discᵤ(chartG₂) = -4t²(3r - 6t - 4)`; it equals `36t³`
only on `wallD = 0`.) -/
theorem three_mul_G₂ (r t u : K) :
    3 * chartG₂ r t u = 9 * t - (3 * t * u - 2) ^ 2 - wallD r t := by
  simp only [chartG₂, wallD]
  ring

/-- Difference form of the τ-cubic derivative: no calculus needed downstream,
and at `t = s` the factor is `2t·wallD`. -/
theorem sheetCubic_sub (A r t s : K) :
    sheetCubic A r t - sheetCubic A r s =
      (t - s) * (2 * (t ^ 2 + t * s + s ^ 2) + (3 * r - 4) * (t + s)) := by
  simp only [sheetCubic]
  ring

/-- **The `c = 0` chart.**  Any fiber point over `(a, b, 0)` with `x ≠ 0`
satisfies the sheet quadric `(16a − b²)x² = −4` — note `16a − b² = W(a,b,0)` —
and has `u = 1 + xy` pinned linearly. -/
theorem fiber_czero_equation {x y z a b : K} (hx : x ≠ 0)
    (h : F K (x, y, z) = (a, b, 0)) :
    (16 * a - b ^ 2) * x ^ 2 = -4 ∧ 4 * (1 + x * y) = b * x - 2 := by
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have htau : 2 - 3 * x * y - x ^ 2 * z = 0 :=
    mul_left_cancel₀ hx (by rw [mul_zero]; linear_combination h3)
  constructor
  · linear_combination (-16 * x ^ 2) * h1 +
      (b * x ^ 2 + 4 * x ^ 2 * y + 6 * x) * h2 +
      (3 * b * x ^ 3 * y ^ 2 + 6 * b * x ^ 2 * y + 3 * b * x - 4 * x ^ 3 * y ^ 3 -
        6 * x ^ 2 * y ^ 2 + 2) * htau
  · linear_combination x * h2 + (3 * (1 + x * y) ^ 2) * htau

/-- **`c = 0` reconstruction.**  Any solution of the sheet quadric with
`x ≠ 0` produces an actual fiber point over `(a, b, 0)`; with
`fiber_czero_equation` and the section `plane_section` this determines the
whole `c = 0` fiber structure.  Characteristic zero is required (the chart
divides by `4`). -/
theorem reconstruct_czero [CharZero K] {x a b : K} (hx : x ≠ 0)
    (hquad : (16 * a - b ^ 2) * x ^ 2 = -4) :
    F K (x, (b * x - 6) / (4 * x), (26 - 3 * b * x) / (4 * x ^ 2)) = (a, b, 0) := by
  simp only [F, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination (-16 : K) * hquad
  · field_simp
    ring
  · field_simp
    ring

end TauChart


section NormalizedCubic

/-! ### The normalized fiber cubic

In the root coordinate `t = y + 1/x`, the fiber over `(a, b, c)` is
governed by the cubic `P(T) = c·T³ − 2T² + bT − 2a`, whose coefficients are
*linear* in the target — so its annihilation certificate is immediate.  Its
key properties, all certified below:

* the cleared form `fiberCubic_cleared` holds with no hypotheses at all (at
  `x = 0` it degenerates to the true statement `c = 0`);
* `fiberCubic_deriv_identity`: `x²·P′(t) = 2x`, so every fiber point is a simple
  root of its own cubic — the Keller condition made visible in one identity;
* `fiberCubic_discr`: the discriminant is exactly `−4W`, identifying the
  wall with the discriminant hypersurface;
* `fiberCubic_on_curve`: on the missed curve the cubic collapses to the
  perfect cube `c·(T − 2/(3c))³` — the omitted locus is the triple-root
  stratum, which is also the singular locus of `V(W)`.

Compared to the τ-chart, this presentation is separating: distinct fiber
points never share a root-coordinate value (their `t`-values are distinct
roots of `P`).  The τ-chart remains useful for reconstruction; this section is the
right interface to Mathlib's `Cubic` root-counting machinery. -/

variable {K : Type*} [Field K]

/-- The normalized fiber cubic `c·T³ − 2T² + bT − 2a` as a Mathlib `Cubic`. -/
def fiberCubic (a b c : K) : Cubic K := ⟨c, -2, b, -2 * a⟩

/-- The discriminant of the fiber cubic is exactly `−4W`: the wall `V(W)` is
precisely the discriminant hypersurface of the fiber family. -/
theorem fiberCubic_discr (a b c : K) :
    (fiberCubic a b c).discr =
      -4 * (27 * a ^ 2 * c ^ 2 - 18 * a * b * c + 16 * a + b ^ 3 * c - b ^ 2) := by
  simp only [fiberCubic, Cubic.discr]
  ring

/-- **Normalized cubic, cleared form.**  Every fiber point satisfies the fiber
cubic at `t = y + 1/x`, multiplied through by `x³`.  No nondegeneracy
hypothesis is needed: at `x = 0` the identity degenerates to `c = 0`, which
is forced. -/
theorem fiberCubic_cleared {x y z a b c : K}
    (h : F K (x, y, z) = (a, b, c)) :
    c * (x * y + 1) ^ 3 - 2 * x * (x * y + 1) ^ 2 + b * x ^ 2 * (x * y + 1) -
      2 * a * x ^ 3 = 0 := by
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  linear_combination (2 * x ^ 3) * h1 - (x ^ 2 * (x * y + 1)) * h2 -
    ((x * y + 1) ^ 3) * h3

/-- Division form of `fiberCubic_cleared` on the chart `x ≠ 0`. -/
theorem fiberCubic_div {x y z a b c : K} (hx : x ≠ 0)
    (h : F K (x, y, z) = (a, b, c)) :
    c * (y + 1 / x) ^ 3 - 2 * (y + 1 / x) ^ 2 + b * (y + 1 / x) - 2 * a = 0 := by
  have key := fiberCubic_cleared h
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  apply mul_left_cancel₀ hx3
  rw [mul_zero]
  field_simp
  linear_combination key

/-- **Simple-root identity.**  `x²·P′(y + 1/x) = 2x`: every fiber point is a
simple root of its own fiber cubic.  This is the Keller condition seen through
the root coordinate. -/
theorem fiberCubic_deriv_identity {x y z a b c : K}
    (h : F K (x, y, z) = (a, b, c)) :
    3 * c * (x * y + 1) ^ 2 - 4 * x * (x * y + 1) + b * x ^ 2 = 2 * x := by
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  linear_combination (-(x ^ 2)) * h2 - (3 * (x * y + 1) ^ 2) * h3

/-- **Triple-root collapse on the missed curve.**  Under `12a = b²` and
`3bc = 4` the fiber cubic is the perfect cube `c·(T − 2/(3c))³`: the omitted
locus is exactly the triple-root stratum of the fiber family. -/
theorem fiberCubic_on_curve [CharZero K] {a b c : K}
    (h12 : 12 * a = b ^ 2) (h34 : 3 * b * c = 4) (T : K) :
    c * T ^ 3 - 2 * T ^ 2 + b * T - 2 * a = c * (T - 2 / (3 * c)) ^ 3 := by
  have hc : c ≠ 0 := by
    rintro rfl
    norm_num at h34
  have h27 : (27 : K) * c ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)
  apply mul_left_cancel₀ h27
  field_simp
  linear_combination (-(9 : K) / 2 * c ^ 2) * h12 +
    (9 * c * T - (3 * b * c + 4) / 2) * h34

end NormalizedCubic


section ResolventTower

/-! ### The quadratic tower: `√(−W)` splits the residual sheets

On the source, one root `t = y + 1/x` of the fiber cubic is known.  Dividing
it out leaves the residual quadratic carrying the other two sheets, and the
`disc_factorization` identity shows its discriminant is `−W·x²` on the fiber
(`residual_disc`).  Consequently adjoining one square root of `−W` to the
source splits the residual quadratic — the expected quadratic step toward the
generic splitting field.  (Generic irreducibility and `S₃` monodromy are not
formalized; see the README.)  `sibling_root` realizes the splitting
concretely: from one root and a square root `σ` of the residual discriminant,
the other two roots are given by the quadratic formula, and
`fiber_point_of_root` turns any simple root into an actual fiber point.
`resolvent_injective` shows distinct fiber points have distinct
root-coordinate values.  Together these reduce the exact fiber count to
counting simple roots of one cubic. -/

variable {K : Type*} [Field K]

/-- The wall polynomial `W`. -/
def wallW (a b c : K) : K :=
  27 * a ^ 2 * c ^ 2 - 18 * a * b * c + 16 * a + b ^ 3 * c - b ^ 2

/-- **Universal discriminant factorization along a root.**  In the polynomial
ring in `a, b, c, t`:
`−4W = P′(t)²·Δ(t) + λ(t)·P(t)` where `Δ` is the discriminant of the residual
quadratic and `λ` is an explicit cubic.  Pure `ring`. -/
theorem disc_factorization (a b c t : K) :
    -4 * wallW a b c =
      (3 * c * t ^ 2 - 4 * t + b) ^ 2 *
        ((c * t - 2) ^ 2 - 4 * c * (c * t ^ 2 - 2 * t + b)) +
      (27 * c ^ 3 * t ^ 3 - 54 * c ^ 2 * t ^ 2 + 27 * b * c ^ 2 * t +
        54 * a * c ^ 2 - 36 * b * c + 32) *
        (c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a) := by
  unfold wallW
  ring

/-- Division form of the simple-root identity: `P′(y + 1/x) = 2/x`. -/
theorem fiberCubic_deriv_div {x y z a b c : K} (hx : x ≠ 0)
    (h : F K (x, y, z) = (a, b, c)) :
    3 * c * (y + 1 / x) ^ 2 - 4 * (y + 1 / x) + b = 2 / x := by
  have key := fiberCubic_deriv_identity h
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  apply mul_left_cancel₀ hx2
  field_simp
  linear_combination key

/-- **Residual discriminant certificate.**  On the fiber, the discriminant of
the residual quadratic equals `−W·x²`.  Hence adjoining a square root of `−W`
to the source splits the two remaining sheets of the fiber cubic.
(Identifying `source(√−W)` with the full degree-six Galois closure would in
addition require generic irreducibility, which is not formalized.) -/
theorem residual_disc [NeZero (2 : K)] {x y z a b c : K} (hx : x ≠ 0)
    (h : F K (x, y, z) = (a, b, c)) :
    (c * (y + 1 / x) - 2) ^ 2 -
        4 * c * (c * (y + 1 / x) ^ 2 - 2 * (y + 1 / x) + b) =
      -(wallW a b c) * x ^ 2 := by
  have key := disc_factorization a b c (y + 1 / x)
  rw [fiberCubic_div hx h, mul_zero, add_zero,
    fiberCubic_deriv_div hx h] at key
  have hx2 : (2 / x) ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero two_ne_zero hx)
  apply mul_left_cancel₀ hx2
  rw [← key]
  field_simp
  ring

/-- **Fiber points from simple roots.**  Any root `t` of the fiber cubic with
`x·P′(t) = 2` solvable (equivalently `P′(t) ≠ 0`) reconstructs to an actual
fiber point.  The certificate is one term per component.  Together with
`fiberCubic_cleared` and `resolvent_injective` this identifies the fiber over
targets with `c ≠ 0` with the simple roots of the fiber cubic. -/
theorem fiber_point_of_root [NeZero (2 : K)] {x t a b c : K} (hx : x ≠ 0)
    (hxd : x * (3 * c * t ^ 2 - 4 * t + b) = 2)
    (hP : c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0) :
    F K (x, t - 1 / x, (2 * x - 3 * x ^ 2 * (t - 1 / x) - c) / x ^ 3) =
      (a, b, c) := by
  simp only [F, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (2 : K) ≠ 0 := two_ne_zero
    field_simp
    apply mul_left_cancel₀ h2
    linear_combination (-(t * x ^ 2)) * hxd + x ^ 3 * hP
  · field_simp
    linear_combination (-x) * hxd
  · field_simp
    ring

/-- **The root coordinate separates the fiber.**  Two fiber points over one target
with the same root-coordinate value `y + 1/x` coincide. -/
theorem resolvent_injective [NeZero (2 : K)] {x₁ y₁ z₁ x₂ y₂ z₂ a b c : K}
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (h₁ : F K (x₁, y₁, z₁) = (a, b, c)) (h₂ : F K (x₂, y₂, z₂) = (a, b, c))
    (ht : y₁ + 1 / x₁ = y₂ + 1 / x₂) :
    (x₁, y₁, z₁) = (x₂, y₂, z₂) := by
  have hd₁ := fiberCubic_deriv_div hx₁ h₁
  have hd₂ := fiberCubic_deriv_div hx₂ h₂
  rw [ht] at hd₁
  have h2 : (2 : K) / x₁ = 2 / x₂ := by rw [← hd₁, ← hd₂]
  have hxx : x₁ = x₂ := by
    have h2' := h2
    field_simp at h2'
    exact h2'.symm
  subst hxx
  have hyy : y₁ = y₂ := by
    have ht' := ht
    field_simp at ht'
    apply mul_left_cancel₀ hx₁
    linear_combination ht'
  subst hyy
  simp only [F, Prod.mk.injEq] at h₁ h₂
  have hz : z₁ = z₂ := by
    have h3 := h₁.2.2.trans h₂.2.2.symm
    have hx3 : x₁ ^ 3 ≠ 0 := pow_ne_zero 3 hx₁
    apply mul_left_cancel₀ hx3
    linear_combination -h3
  rw [hz]

/-- **Sibling roots via the resolvent square root.**  Given one root `t` of
the fiber cubic and a square root `σ` of the residual discriminant
(equivalently, by `residual_disc`, of `−W·x²`), the quadratic formula
produces the other roots. -/
theorem sibling_root [NeZero (2 : K)] {a b c t σ : K} (hc : c ≠ 0)
    (hP : c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0)
    (hσ : σ ^ 2 = (c * t - 2) ^ 2 - 4 * c * (c * t ^ 2 - 2 * t + b)) :
    c * ((2 - c * t + σ) / (2 * c)) ^ 3 - 2 * ((2 - c * t + σ) / (2 * c)) ^ 2 +
      b * ((2 - c * t + σ) / (2 * c)) - 2 * a = 0 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h2c : 2 * c ≠ 0 := mul_ne_zero h2 hc
  field_simp
  linear_combination (σ + 2 - 3 * c * t) * hσ + 8 * c ^ 2 * hP

end ResolventTower


section FiberEquiv

/-! ### The explanation: the fiber *is* the simple-root set of one cubic

The counterexample admits a one-sentence structure theorem.  For a target
`(a, b, c)` with `c ≠ 0`, the root coordinate `t = y + 1/x` is a **bijection**
between the fiber `F⁻¹(a, b, c)` and the simple roots in `K` of the single
cubic

```text
P(T) = c·T³ − 2T² + bT − 2a,
```

with explicit inverse `x = 2/P′(t)`, `y = t − 1/x`, `z = (2x − 3x²y − c)/x³`.
This explains every headline result at once:

* **Keller condition.**  `fiberCubic_deriv_identity` says `x·P′(t) = 2` on the
  fiber: every preimage is a simple root of its own cubic.  The constant
  Jacobian is the pointwise simplicity of roots — a local condition.
* **Non-injectivity.**  A cubic can have three simple roots; the fiber count
  follows the simple-root count.  (Over `(-1/4, 0, 0)` the cubic degenerates
  to `-2T² + 1/2`, whose simple roots `T = ±1/2` reconstruct exactly the two
  witnesses `(1, -3/2, 13/2)` and `(-1, 3/2, 13/2)` via `x = 2/P′(T)`.)
* **Non-surjectivity.**  On the missed curve `P` is a perfect cube
  (`fiberCubic_on_curve`); a triple root is never simple, so the fiber is
  empty.
* **The wall.**  `disc P = −4W` (`fiberCubic_discr`): fibers jump `3 → 1 → 0`
  exactly across the discriminant hypersurface.

The Jacobian Conjecture fails because *pointwise simplicity of roots does not
control the global simple-root count of a cubic*.

The affine equivalence first treats `c ≠ 0`.  Its projective completion below
adds the root `[1 : 0]`, which is precisely the `x = 0` sheet when `c = 0`, and
therefore removes the chart restriction entirely. -/

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The reconstruction formulas of `fiber_point_of_root` at the canonical
choice `x = 2 / P′(t)` forced by the simple-root identity. -/
noncomputable def fiberPoint (b c t : K) : K × K × K :=
  (2 / (3 * c * t ^ 2 - 4 * t + b),
   t - 1 / (2 / (3 * c * t ^ 2 - 4 * t + b)),
   (2 * (2 / (3 * c * t ^ 2 - 4 * t + b)) -
      3 * (2 / (3 * c * t ^ 2 - 4 * t + b)) ^ 2 *
        (t - 1 / (2 / (3 * c * t ^ 2 - 4 * t + b))) - c) /
    (2 / (3 * c * t ^ 2 - 4 * t + b)) ^ 3)

/-- Every simple root of the fiber cubic reconstructs to a fiber point. -/
theorem fiberPoint_mem {a b c t : K}
    (hP : c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0)
    (hd : 3 * c * t ^ 2 - 4 * t + b ≠ 0) :
    F K (fiberPoint b c t) = (a, b, c) := by
  unfold fiberPoint
  exact fiber_point_of_root (div_ne_zero two_ne_zero hd)
    (div_mul_cancel₀ 2 hd) hP

omit [NeZero (2 : K)] in
/-- The reconstructed point has root-coordinate value exactly `t`: a pure ring
identity `(t - 1/x) + 1/x = t`. -/
theorem fiberPoint_resolvent (b c t : K) :
    (fiberPoint b c t).2.1 + 1 / (fiberPoint b c t).1 = t := by
  dsimp only [fiberPoint]
  ring

/-- The root-coordinate value of any fiber point with `x ≠ 0` is a simple root of
the fiber cubic. -/
theorem resolvent_simpleRoot {x y z a b c : K} (hx : x ≠ 0)
    (h : F K (x, y, z) = (a, b, c)) :
    c * (y + 1 / x) ^ 3 - 2 * (y + 1 / x) ^ 2 + b * (y + 1 / x) - 2 * a = 0 ∧
      3 * c * (y + 1 / x) ^ 2 - 4 * (y + 1 / x) + b ≠ 0 := by
  refine ⟨fiberCubic_div hx h, ?_⟩
  rw [fiberCubic_deriv_div hx h]
  exact div_ne_zero two_ne_zero hx

/-- **Structure theorem: the fiber is the simple-root set of one cubic.**

For `c ≠ 0` the root coordinate `t = y + 1/x` is an equivalence between the fiber
of `F` over `(a, b, c)` and the simple roots in `K` of
`P(T) = c·T³ − 2T² + bT − 2a`, with explicit polynomial-in-`1/P′` inverse. -/
noncomputable def fiberEquivSimpleRoots {a b c : K} (hc : c ≠ 0) :
    { p : K × K × K // F K p = (a, b, c) } ≃
      { t : K // c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
          3 * c * t ^ 2 - 4 * t + b ≠ 0 } where
  toFun p :=
    ⟨p.1.2.1 + 1 / p.1.1,
     resolvent_simpleRoot (fiber_tau_coordinates hc p.2).1 p.2⟩
  invFun t := ⟨fiberPoint b c t.1, fiberPoint_mem t.2.1 t.2.2⟩
  left_inv := by
    rintro ⟨⟨x, y, z⟩, hp⟩
    have hx : x ≠ 0 := (fiber_tau_coordinates hc hp).1
    obtain ⟨hP, hd⟩ := resolvent_simpleRoot hx hp
    exact Subtype.ext (resolvent_injective (div_ne_zero two_ne_zero hd) hx
      (fiberPoint_mem hP hd) hp (fiberPoint_resolvent b c (y + 1 / x)))
  right_inv := by
    rintro ⟨t, hP, hd⟩
    exact Subtype.ext (fiberPoint_resolvent b c t)

/-! ### Projective completion of the fiber cubic

The missing `c = 0` chart is the root at infinity of the binary cubic

`cT³ - 2T²U + bTU² - 2aU³`.

We represent `ℙ¹(K)` by `Option K`: `some t` is `[t : 1]` and `none` is
`[1 : 0]`.  Since the coefficient following `c` is the unit `-2`, the root
at infinity is simple whenever it occurs.  Thus one statement covers every
target and identifies the `x = 0` section with that projective root. -/

/-- Simple `K`-rational roots of the projectivized fiber cubic.
`none` denotes the point at infinity `[1 : 0]`. -/
def projectiveSimpleRoot (a b c : K) : Option K → Prop
  | none => c = 0
  | some t =>
      c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
        3 * c * t ^ 2 - 4 * t + b ≠ 0

omit [NeZero (2 : K)] in
/-- A fiber point with `x = 0` is the unique point supplied by the plane
section; in particular its target has `c = 0`. -/
theorem fiber_xzero {y z a b c : K} (h : F K (0, y, z) = (a, b, c)) :
    c = 0 ∧ y = b ∧ z = a - 4 * b ^ 2 := by
  simp only [F, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hc : c = 0 := by linear_combination -h3
  have hy : y = b := by linear_combination h2
  refine ⟨hc, hy, ?_⟩
  rw [hy] at h1
  linear_combination h1

/-- Underlying value of the projective resolvent. -/
noncomputable def projectiveResolventValue (p : K × K × K) : Option K := by
  classical
  rcases p with ⟨x, y, z⟩
  exact if x = 0 then none else some (y + 1 / x)

/-- Underlying reconstruction map from the projective line. -/
noncomputable def projectiveFiberPointValue (a b c : K) : Option K → K × K × K
  | none => (0, b, a - 4 * b ^ 2)
  | some t => fiberPoint b c t

/-- Send a fiber point to its projective resolvent, using infinity exactly on
the `x = 0` sheet. -/
noncomputable def projectiveResolvent {a b c : K}
    (p : {p : K × K × K // F K p = (a, b, c)}) :
    {t : Option K // projectiveSimpleRoot a b c t} := by
  refine ⟨projectiveResolventValue p.1, ?_⟩
  rcases p with ⟨⟨x, y, z⟩, hp⟩
  by_cases hx : x = 0
  · subst x
    simpa [projectiveResolventValue, projectiveSimpleRoot] using (fiber_xzero hp).1
  · simpa [projectiveResolventValue, projectiveSimpleRoot, hx] using
      resolvent_simpleRoot hx hp

/-- Reconstruct a fiber point from a projective simple root. -/
noncomputable def projectiveFiberPoint {a b c : K}
    (t : {t : Option K // projectiveSimpleRoot a b c t}) :
    {p : K × K × K // F K p = (a, b, c)} := by
  refine ⟨projectiveFiberPointValue a b c t.1, ?_⟩
  rcases t with ⟨none | t, ht⟩
  · simp only [projectiveFiberPointValue]
    rw [ht]
    exact plane_section (K := K) a b
  · simpa [projectiveFiberPointValue] using fiberPoint_mem ht.1 ht.2

theorem projectiveFiberPoint_resolvent {a b c : K}
    (p : {p : K × K × K // F K p = (a, b, c)}) :
    projectiveFiberPoint (projectiveResolvent p) = p := by
  rcases p with ⟨⟨x, y, z⟩, hp⟩
  by_cases hx : x = 0
  · subst x
    obtain ⟨hc, hy, hz⟩ := fiber_xzero hp
    apply Subtype.ext
    change projectiveFiberPointValue a b c
      (projectiveResolventValue (0, y, z)) = (0, y, z)
    simp [projectiveFiberPointValue, projectiveResolventValue, hy, hz]
  · obtain ⟨hP, hd⟩ := resolvent_simpleRoot hx hp
    apply Subtype.ext
    simp only [projectiveFiberPoint, projectiveResolvent]
    have hval : projectiveResolventValue (x, y, z) = some (y + 1 / x) := by
      simp [projectiveResolventValue, hx]
    rw [hval]
    exact resolvent_injective (div_ne_zero two_ne_zero hd) hx
      (fiberPoint_mem hP hd) hp (fiberPoint_resolvent b c (y + 1 / x))

theorem projectiveResolvent_fiberPoint {a b c : K}
    (t : {t : Option K // projectiveSimpleRoot a b c t}) :
    projectiveResolvent (projectiveFiberPoint t) = t := by
  rcases t with ⟨none | t, ht⟩
  · apply Subtype.ext
    change projectiveResolventValue (projectiveFiberPointValue a b c none) = none
    simp [projectiveFiberPointValue, projectiveResolventValue]
  · have hx : (fiberPoint b c t).1 ≠ 0 := by
      dsimp only [fiberPoint]
      exact div_ne_zero two_ne_zero ht.2
    apply Subtype.ext
    change projectiveResolventValue (fiberPoint b c t) = some t
    simp only [projectiveResolventValue, hx, if_false]
    exact congrArg some (fiberPoint_resolvent b c t)

/-- **Projective structure theorem.**  For every target, including `c = 0`,
the fiber is equivalent to the simple `K`-rational roots of the binary cubic
`cT³ - 2T²U + bTU² - 2aU³`.  The root `[1 : 0]` is exactly the `x = 0`
sheet. -/
noncomputable def fiberEquivSimpleRootsProj {a b c : K} :
    { p : K × K × K // F K p = (a, b, c) } ≃
      { t : Option K // projectiveSimpleRoot a b c t } where
  toFun := projectiveResolvent
  invFun := projectiveFiberPoint
  left_inv := projectiveFiberPoint_resolvent
  right_inv := projectiveResolvent_fiberPoint

omit [NeZero (2 : K)] in
/-- Two distinct affine simple roots of a genuine cubic force a third distinct
simple root over the same field.  This is Vieta closure, stated in the exact
coefficient normalization used by `fiberCubic`. -/
theorem third_simpleRoot {a b c t₁ t₂ : K} (hc : c ≠ 0) (hne : t₁ ≠ t₂)
    (h₁ : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 ∧
      3 * c * t₁ ^ 2 - 4 * t₁ + b ≠ 0)
    (h₂ : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 ∧
      3 * c * t₂ ^ 2 - 4 * t₂ + b ≠ 0) :
    ∃ t₃ : K,
      (c * t₃ ^ 3 - 2 * t₃ ^ 2 + b * t₃ - 2 * a = 0 ∧
        3 * c * t₃ ^ 2 - 4 * t₃ + b ≠ 0) ∧ t₃ ≠ t₁ ∧ t₃ ≠ t₂ := by
  let t₃ := 2 / c - t₁ - t₂
  have hsum : c * (t₁ + t₂ + t₃) = 2 := by
    dsimp [t₃]
    field_simp
    ring
  have hfactor : c * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) - 2 * (t₁ + t₂) + b = 0 := by
    have hm : (t₁ - t₂) *
        (c * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) - 2 * (t₁ + t₂) + b) = 0 := by
      linear_combination h₁.1 - h₂.1
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne)
  have hpair : c * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) = b := by
    linear_combination -hfactor + (t₁ + t₂) * hsum
  have hprod : c * (t₁ * t₂ * t₃) = 2 * a := by
    linear_combination h₁.1 - t₁ ^ 2 * hsum + t₁ * hpair
  have hP₃ : c * t₃ ^ 3 - 2 * t₃ ^ 2 + b * t₃ - 2 * a = 0 := by
    linear_combination t₃ ^ 2 * hsum - t₃ * hpair + hprod
  have hd₁ : 3 * c * t₁ ^ 2 - 4 * t₁ + b =
      c * (t₁ - t₂) * (t₁ - t₃) := by
    linear_combination 2 * t₁ * hsum - hpair
  have hd₂ : 3 * c * t₂ ^ 2 - 4 * t₂ + b =
      c * (t₂ - t₁) * (t₂ - t₃) := by
    linear_combination 2 * t₂ * hsum - hpair
  have ht₃₁ : t₃ ≠ t₁ := by
    intro heq
    rw [heq, sub_self, mul_zero] at hd₁
    exact h₁.2 hd₁
  have ht₃₂ : t₃ ≠ t₂ := by
    intro heq
    rw [heq, sub_self, mul_zero] at hd₂
    exact h₂.2 hd₂
  have hd₃ : 3 * c * t₃ ^ 2 - 4 * t₃ + b =
      c * (t₃ - t₁) * (t₃ - t₂) := by
    linear_combination 2 * t₃ * hsum - hpair
  refine ⟨t₃, ⟨hP₃, ?_⟩, ht₃₁, ht₃₂⟩
  rw [hd₃]
  exact mul_ne_zero (mul_ne_zero hc (sub_ne_zero.mpr ht₃₁)) (sub_ne_zero.mpr ht₃₂)

/-- At `c = 0`, one affine simple root forces the other affine root.  Together
with `[1 : 0]`, these are the three projective simple roots. -/
theorem other_simpleRoot_at_infinity {a b t : K}
    (h : -2 * t ^ 2 + b * t - 2 * a = 0 ∧ -4 * t + b ≠ 0) :
    ∃ s : K, (-2 * s ^ 2 + b * s - 2 * a = 0 ∧ -4 * s + b ≠ 0) ∧ s ≠ t := by
  let s := b / 2 - t
  have hs : -2 * s ^ 2 + b * s - 2 * a = 0 := by
    have heqP : -2 * s ^ 2 + b * s - 2 * a =
        -2 * t ^ 2 + b * t - 2 * a := by
      dsimp [s]
      field_simp
      ring
    rw [heqP]
    exact h.1
  have hd : -4 * s + b = -(-4 * t + b) := by
    dsimp [s]
    field_simp
    ring
  have hst : s ≠ t := by
    intro heq
    have hz : -4 * t + b = 0 := by
      rw [heq] at hd
      apply mul_left_cancel₀ (show (2 : K) ≠ 0 from two_ne_zero)
      linear_combination hd
    exact h.2 hz
  refine ⟨s, ⟨hs, ?_⟩, hst⟩
  rw [hd]
  exact neg_ne_zero.mpr h.2

/-- **No-two law for projective roots.**  Any two distinct simple rational
roots of the binary fiber cubic extend to three distinct simple rational
roots. -/
theorem projectiveSimpleRoot_exists_third {a b c : K} {r₁ r₂ : Option K}
    (h₁ : projectiveSimpleRoot a b c r₁)
    (h₂ : projectiveSimpleRoot a b c r₂) (hne : r₁ ≠ r₂) :
    ∃ r₃, projectiveSimpleRoot a b c r₃ ∧ r₃ ≠ r₁ ∧ r₃ ≠ r₂ := by
  cases r₁ with
  | none =>
      cases r₂ with
      | none => exact (hne rfl).elim
      | some t =>
          have hc : c = 0 := h₁
          subst c
          obtain ⟨s, hs, hst⟩ := other_simpleRoot_at_infinity (a := a) (b := b)
            (by simpa [projectiveSimpleRoot] using h₂)
          exact ⟨some s, by simpa [projectiveSimpleRoot] using hs,
            by simp, by simpa using hst⟩
  | some t₁ =>
      cases r₂ with
      | none =>
          have hc : c = 0 := h₂
          subst c
          obtain ⟨s, hs, hst⟩ := other_simpleRoot_at_infinity (a := a) (b := b)
            (by simpa [projectiveSimpleRoot] using h₁)
          exact ⟨some s, by simpa [projectiveSimpleRoot] using hs,
            by simpa using hst, by simp⟩
      | some t₂ =>
          by_cases hc : c = 0
          · exact ⟨none, by simpa [projectiveSimpleRoot] using hc,
              by simp, by simp⟩
          · obtain ⟨t₃, h₃, h31, h32⟩ := third_simpleRoot hc
              (by simpa using hne) h₁ h₂
            exact ⟨some t₃, h₃, by simpa using h31, by simpa using h32⟩

/-- **Arithmetic no-two law.**  Over every field of characteristic not two,
two distinct points in one fiber force a third point in that same fiber,
distinct from both. -/
theorem two_fiber_points_extend_to_three {a b c : K} {p₁ p₂ : K × K × K}
    (h₁ : F K p₁ = (a, b, c)) (h₂ : F K p₂ = (a, b, c)) (hne : p₁ ≠ p₂) :
    ∃ p₃, F K p₃ = (a, b, c) ∧ p₃ ≠ p₁ ∧ p₃ ≠ p₂ := by
  let e := fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)
  let q₁ : {p // F K p = (a, b, c)} := ⟨p₁, h₁⟩
  let q₂ : {p // F K p = (a, b, c)} := ⟨p₂, h₂⟩
  have hq : (e q₁).1 ≠ (e q₂).1 := fun he =>
    hne (Subtype.ext_iff.mp (e.injective (Subtype.ext he)))
  obtain ⟨r₃, hr₃, hr31, hr32⟩ :=
    projectiveSimpleRoot_exists_third (e q₁).2 (e q₂).2 hq
  let q₃ := e.symm ⟨r₃, hr₃⟩
  exact ⟨q₃.1, q₃.2,
    fun he => hr31 (by
      have hq31 : q₃ = q₁ := Subtype.ext he
      simpa [q₃] using congrArg Subtype.val (congrArg e hq31)),
    fun he => hr32 (by
      have hq32 : q₃ = q₂ := Subtype.ext he
      simpa [q₃] using congrArg Subtype.val (congrArg e hq32))⟩

/-- The projective simple-root set is finite.  Off `c = 0` it injects into
the roots of a cubic; on `c = 0` it is the point at infinity plus roots of a
quadratic. -/
theorem projectiveSimpleRoots_finite (a b c : K) :
    Finite {r : Option K // projectiveSimpleRoot a b c r} := by
  classical
  let A := {t : K //
    c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
      3 * c * t ^ 2 - 4 * t + b ≠ 0}
  by_cases hc : c = 0
  · let A₀ := {t : K //
      -2 * t ^ 2 + b * t - 2 * a = 0 ∧ -4 * t + b ≠ 0}
    let p := fiberCubic a b 0
    have hP0 : p.toPoly ≠ 0 := by
      apply Cubic.ne_zero_of_b_ne_zero
      simpa [p, fiberCubic] using (neg_ne_zero.mpr two_ne_zero)
    let f : A₀ → p.roots.toFinset := fun t => ⟨t.1, by
      rw [Multiset.mem_toFinset, Cubic.mem_roots_iff hP0]
      convert t.2.1 using 1
      all_goals (simp [p, fiberCubic]; ring)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun q : p.roots.toFinset => (q.1 : K)) hxy
    letI : Finite A₀ := Finite.of_injective f hf
    let e : {r : Option K // projectiveSimpleRoot a b c r} ≃ Option A₀ := {
      toFun r := by
        rcases r with ⟨r, ht⟩
        cases r with
        | none => exact none
        | some t => exact some ⟨t, by simpa [projectiveSimpleRoot, hc] using ht⟩
      invFun r := by
        cases r with
        | none => exact ⟨none, by simpa [projectiveSimpleRoot] using hc⟩
        | some q =>
            rcases q with ⟨t, ht⟩
            exact ⟨some t, by simpa [projectiveSimpleRoot, hc] using ht⟩
      left_inv := by
        rintro ⟨r, ht⟩
        cases r <;> rfl
      right_inv := by
        intro r
        cases r with
        | none => rfl
        | some q =>
            rcases q with ⟨t, ht⟩
            rfl }
    exact Finite.of_injective e e.injective
  · let p := fiberCubic a b c
    have hP0 : p.toPoly ≠ 0 := by
      apply Cubic.ne_zero_of_a_ne_zero
      simpa [p, fiberCubic] using hc
    let f : A → p.roots.toFinset := fun t => ⟨t.1, by
      rw [Multiset.mem_toFinset, Cubic.mem_roots_iff hP0]
      convert t.2.1 using 1
      all_goals (simp [p, fiberCubic]; ring)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun q : p.roots.toFinset => (q.1 : K)) hxy
    letI : Finite A := Finite.of_injective f hf
    let e : {r : Option K // projectiveSimpleRoot a b c r} ≃ A :=
      (fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)).symm.trans
        (fiberEquivSimpleRoots hc)
    exact Finite.of_injective e e.injective

/-- The projective simple-root set has at most three elements. -/
theorem projectiveSimpleRoots_ncard_le_three (a b c : K) :
    Set.ncard {r : Option K | projectiveSimpleRoot a b c r} ≤ 3 := by
  classical
  let A := {t : K //
    c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
      3 * c * t ^ 2 - 4 * t + b ≠ 0}
  by_cases hc : c = 0
  · let A₀ := {t : K //
      -2 * t ^ 2 + b * t - 2 * a = 0 ∧ -4 * t + b ≠ 0}
    let p := fiberCubic a b 0
    have hP0 : p.toPoly ≠ 0 := by
      apply Cubic.ne_zero_of_b_ne_zero
      simpa [p, fiberCubic] using (neg_ne_zero.mpr two_ne_zero)
    let f : A₀ → p.roots.toFinset := fun t => ⟨t.1, by
      rw [Multiset.mem_toFinset, Cubic.mem_roots_iff hP0]
      convert t.2.1 using 1
      all_goals (simp [p, fiberCubic]; ring)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun q : p.roots.toFinset => (q.1 : K)) hxy
    letI : Finite A₀ := Finite.of_injective f hf
    have hroots : p.roots.toFinset.card ≤ 2 := by
      calc
        p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
        _ ≤ p.toPoly.natDegree := Polynomial.card_roots' p.toPoly
        _ = 2 := Cubic.natDegree_of_b_ne_zero (by simp [p, fiberCubic])
          (by simpa [p, fiberCubic] using (neg_ne_zero.mpr two_ne_zero))
    have hA : Nat.card A₀ ≤ 2 := by
      have hle := Nat.card_le_card_of_injective f hf
      have htarget : Nat.card p.roots.toFinset = p.roots.toFinset.card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
      rw [htarget] at hle
      exact hle.trans hroots
    let e : {r : Option K // projectiveSimpleRoot a b c r} ≃ Option A₀ := {
      toFun r := by
        rcases r with ⟨r, ht⟩
        cases r with
        | none => exact none
        | some t => exact some ⟨t, by simpa [projectiveSimpleRoot, hc] using ht⟩
      invFun r := by
        cases r with
        | none => exact ⟨none, by simpa [projectiveSimpleRoot] using hc⟩
        | some q =>
            rcases q with ⟨t, ht⟩
            exact ⟨some t, by simpa [projectiveSimpleRoot, hc] using ht⟩
      left_inv := by
        rintro ⟨r, ht⟩
        cases r <;> rfl
      right_inv := by
        intro r
        cases r with
        | none => rfl
        | some q =>
            rcases q with ⟨t, ht⟩
            rfl }
    rw [← Nat.card_coe_set_eq]
    change Nat.card {r : Option K // projectiveSimpleRoot a b c r} ≤ 3
    have he := Nat.card_congr e
    rw [he]
    simpa using Nat.add_le_add_right hA 1
  · let p := fiberCubic a b c
    have hP0 : p.toPoly ≠ 0 := by
      apply Cubic.ne_zero_of_a_ne_zero
      simpa [p, fiberCubic] using hc
    let f : A → p.roots.toFinset := fun t => ⟨t.1, by
      rw [Multiset.mem_toFinset, Cubic.mem_roots_iff hP0]
      convert t.2.1 using 1
      all_goals (simp [p, fiberCubic]; ring)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun q : p.roots.toFinset => (q.1 : K)) hxy
    letI : Finite A := Finite.of_injective f hf
    have hA : Nat.card A ≤ 3 := by
      have hle := Nat.card_le_card_of_injective f hf
      have htarget : Nat.card p.roots.toFinset = p.roots.toFinset.card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
      rw [htarget] at hle
      exact hle.trans p.card_roots_le
    let e : {r : Option K // projectiveSimpleRoot a b c r} ≃ A :=
      (fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)).symm.trans
        (fiberEquivSimpleRoots hc)
    rw [← Nat.card_coe_set_eq]
    change Nat.card {r : Option K // projectiveSimpleRoot a b c r} ≤ 3
    have he := Nat.card_congr e
    rw [he]
    exact hA

/-- Every fiber is finite, uniformly over the base field. -/
theorem fiber_finite (a b c : K) :
    Set.Finite {p : K × K × K | F K p = (a, b, c)} := by
  letI : Finite {r : Option K // projectiveSimpleRoot a b c r} :=
    projectiveSimpleRoots_finite a b c
  let e := fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)
  rw [← Set.finite_coe_iff]
  exact Finite.of_injective e e.injective

/-- Every fiber has at most three rational points. -/
theorem fiber_ncard_le_three (a b c : K) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} ≤ 3 := by
  let e := fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)
  exact (Set.ncard_congr' e).le.trans (projectiveSimpleRoots_ncard_le_three a b c)

/-- **The `0/1/3` law.**  Over every field with `2 ≠ 0` — in particular over
every finite field of odd order — every `K`-rational fiber has cardinality
zero, one, or three.  Cardinality two is impossible even when the fiber cubic
does not split over `K`. -/
theorem fiber_ncard_mem_zero_one_three (a b c : K) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} ∈ ({0, 1, 3} : Set ℕ) := by
  let S : Set (K × K × K) := {p | F K p = (a, b, c)}
  have hle : S.ncard ≤ 3 := fiber_ncard_le_three a b c
  have hne2 : S.ncard ≠ 2 := by
    intro h2
    obtain ⟨p₁, p₂, hpne, hS⟩ := Set.ncard_eq_two.mp h2
    have hp₁ : F K p₁ = (a, b, c) := by rw [show p₁ ∈ S from hS ▸ Set.mem_insert p₁ {p₂}]
    have hp₂ : F K p₂ = (a, b, c) := by rw [show p₂ ∈ S from hS ▸ Set.mem_insert_of_mem p₁ rfl]
    obtain ⟨p₃, hp₃, hp31, hp32⟩ := two_fiber_points_extend_to_three hp₁ hp₂ hpne
    have hp₃S : p₃ ∈ S := hp₃
    rw [hS] at hp₃S
    rcases hp₃S with (rfl | hp₃S)
    · exact hp31 rfl
    · exact hp32 (Set.mem_singleton_iff.mp hp₃S)
  interval_cases hcard : S.ncard <;> simp_all

/-! ### Exact image over an algebraically closed field -/

/-- The intrinsic equations of the omitted rational curve. -/
def OnMissedCurve (a b c : K) : Prop := 12 * a = b ^ 2 ∧ 3 * b * c = 4

omit [NeZero (2 : K)] in
/-- Away from the triple-root curve, the projective binary cubic has a simple
root over an algebraically closed field.  If an initially chosen root is
double, Vieta's remaining root is simple unless all three roots coincide;
that coincidence is exactly `OnMissedCurve`. -/
theorem exists_projectiveSimpleRoot_of_not_onMissedCurve [CharZero K] [IsAlgClosed K]
    {a b c : K} (hC : ¬ OnMissedCurve a b c) :
    ∃ r, projectiveSimpleRoot a b c r := by
  by_cases hc : c = 0
  · exact ⟨none, hc⟩
  · have hdeg : (fiberCubic a b c).toPoly.degree ≠ 0 := by
      rw [Cubic.degree_of_a_ne_zero]
      · norm_num
      · simpa [fiberCubic] using hc
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (fiberCubic a b c).toPoly hdeg
    have hP : c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 := by
      simp only [Polynomial.IsRoot] at ht
      simp [Cubic.toPoly, fiberCubic] at ht
      linear_combination ht
    by_cases hd : 3 * c * t ^ 2 - 4 * t + b = 0
    · let s := 2 / c - 2 * t
      have hsum : c * (t + t + s) = 2 := by
        dsimp [s]
        field_simp
        ring
      have hpair : c * (t * t + t * s + t * s) = b := by
        linear_combination 2 * t * hsum - hd
      have hprod : c * (t * t * s) = 2 * a := by
        linear_combination hP - t ^ 2 * hsum + t * hpair
      have hPs : c * s ^ 3 - 2 * s ^ 2 + b * s - 2 * a = 0 := by
        linear_combination s ^ 2 * hsum - s * hpair + hprod
      have hds : 3 * c * s ^ 2 - 4 * s + b = c * (s - t) ^ 2 := by
        linear_combination 2 * s * hsum - hpair
      by_cases hst : s = t
      · exfalso
        apply hC
        have h12 : 12 * a = b ^ 2 := by
          rw [hst] at hsum hpair hprod
          linear_combination (3 * c * t ^ 2 + b) * hpair -
            (3 * c * t ^ 3) * hsum - 6 * hprod
        have h34 : 3 * b * c = 4 := by
          rw [hst] at hsum hpair
          linear_combination (-3 * c) * hpair + (3 * c * t + 2) * hsum
        exact ⟨h12, h34⟩
      · refine ⟨some s, hPs, ?_⟩
        rw [hds]
        exact mul_ne_zero hc (pow_ne_zero 2 (sub_ne_zero.mpr hst))
    · exact ⟨some t, hP, hd⟩

/-- **Exact image theorem.**  Over every algebraically closed
characteristic-zero field, the image of `F` is precisely the complement of
the smooth rational curve `12a = b²`, `3bc = 4`. -/
theorem mem_range_iff_not_onMissedCurve [CharZero K] [IsAlgClosed K]
    (a b c : K) :
    (a, b, c) ∈ Set.range (F K) ↔ ¬ OnMissedCurve a b c := by
  constructor
  · rintro ⟨p, hp⟩ hC
    have hb : b ≠ 0 := by
      rintro rfl
      norm_num [OnMissedCurve] at hC
    have ha : a = b ^ 2 / 12 := by
      have h12 := hC.1
      field_simp
      linear_combination h12
    have hc : c = 4 / (3 * b) := by
      have h34 := hC.2
      field_simp
      linear_combination h34
    exact missed_curve (K := K) b hb p (by simpa [ha, hc] using hp)
  · intro hC
    obtain ⟨r, hr⟩ := exists_projectiveSimpleRoot_of_not_onMissedCurve hC
    let e := fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)
    exact ⟨(e.symm ⟨r, hr⟩).1, (e.symm ⟨r, hr⟩).2⟩

/-- Set-level form of `mem_range_iff_not_onMissedCurve`. -/
theorem range_eq_compl_missedCurve [CharZero K] [IsAlgClosed K] :
    Set.range (F K) = {q : K × K × K | ¬ OnMissedCurve q.1 q.2.1 q.2.2} := by
  ext q
  rcases q with ⟨a, b, c⟩
  exact mem_range_iff_not_onMissedCurve a b c

/-- **Sharp packaged statement.**  The Keller map has constant Jacobian
`-2`; every fiber is the simple-root set of its projective binary cubic; every
rational fiber has size `0`, `1`, or `3`; and over an algebraically closed
field its image is exactly the complement of the triple-root curve. -/
theorem projective_structure_and_exact_image
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] :
    jacobian.det = -2 ∧
      (∀ a b c : K,
        Nonempty ({p : K × K × K // F K p = (a, b, c)} ≃
          {r : Option K // projectiveSimpleRoot a b c r})) ∧
      (∀ a b c : K,
        Set.ncard {p : K × K × K | F K p = (a, b, c)} ∈ ({0, 1, 3} : Set ℕ)) ∧
      Set.range (F K) =
        {q : K × K × K | ¬ OnMissedCurve q.1 q.2.1 q.2.2} :=
  ⟨jacobian_det, fun _ _ _ => ⟨fiberEquivSimpleRootsProj⟩,
    fiber_ncard_mem_zero_one_three, range_eq_compl_missedCurve⟩

/-- **The counterexample, explained.**  Over any characteristic-zero field:
the formal Jacobian determinant is the constant `-2`; every fiber over a
target with `c ≠ 0` is equivalent to the simple-root set of the cubic
`c·T³ − 2T² + bT − 2a`; and `F` is neither injective nor surjective.  The
Keller condition is pointwise simplicity of roots, and simplicity does not
control the number of simple roots of a cubic — which jumps `3 → 1 → 0`
across the discriminant wall `W`. -/
theorem counterexample_explained (K : Type*) [Field K] [CharZero K] :
    jacobian.det = -2 ∧
      (∀ a b c : K, c ≠ 0 →
        Nonempty ({ p : K × K × K // F K p = (a, b, c) } ≃
          { t : K // c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
              3 * c * t ^ 2 - 4 * t + b ≠ 0 })) ∧
      ¬ Function.Injective (F K) ∧ ¬ Function.Surjective (F K) :=
  ⟨jacobian_det, fun _ _ _ hc => ⟨fiberEquivSimpleRoots hc⟩,
    not_injective K, not_surjective K⟩

end FiberEquiv


section Stratification

/-! ### The missed curve as a punctured line, and stratum boundaries

`missedCurveEquivNonzero` upgrades the parametrization of the missed curve to
an equivalence with `K \ {0}` (the `K`-points of `𝔾ₘ`): projection to the
`b`-coordinate, with explicit inverse `s ↦ (s²/12, s, 4/(3s))`.
`fiber_ncard_eq_zero_iff` identifies the empty stratum exactly, and
`fiber_ncard_mem_one_three_of_not_onMissedCurve` bounds the remaining strata. -/

variable {K : Type*} [Field K]

/-- The wall polynomial `W` vanishes on the missed curve. -/
theorem wallW_eq_zero_of_onMissedCurve [CharZero K] {a b c : K}
    (h : OnMissedCurve a b c) :
    27 * a ^ 2 * c ^ 2 - 18 * a * b * c + 16 * a + b ^ 3 * c - b ^ 2 = 0 := by
  obtain ⟨h1, h2⟩ := h
  linear_combination
    (9 * a * c ^ 2 / 4 + 3 * b ^ 2 * c ^ 2 / 16 - 3 * b * c / 2 + 4 / 3) * h1 +
      (b ^ 3 * c / 16 - b ^ 2 / 12) * h2

/-- **The missed curve is a punctured line.**  Projection to the
`b`-coordinate is an equivalence onto `K \ {0}`, with inverse
`s ↦ (s²/12, s, 4/(3s))`. -/
def missedCurveEquivNonzero [CharZero K] :
    {q : K × K × K // OnMissedCurve q.1 q.2.1 q.2.2} ≃ {s : K // s ≠ 0} where
  toFun q := ⟨q.1.2.1, fun hb => by
    have h2 := q.2.2
    rw [hb] at h2
    norm_num at h2⟩
  invFun s := ⟨(s.1 ^ 2 / 12, s.1, 4 / (3 * s.1)), by
    refine ⟨by field_simp, ?_⟩
    have hs := s.2
    field_simp⟩
  left_inv q := by
    obtain ⟨⟨a, b, c⟩, h1, h2⟩ := q
    have h1' : 12 * a = b ^ 2 := h1
    have h2' : 3 * b * c = 4 := h2
    have hb : b ≠ 0 := fun hb => by rw [hb] at h2'; norm_num at h2'
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    refine ⟨?_, trivial, ?_⟩
    · field_simp
      linear_combination -h1'
    · field_simp
      linear_combination -h2'
  right_inv s := Subtype.ext rfl

/-- **Empty stratum.**  Over an algebraically closed field of characteristic
zero, the fiber is empty exactly on the missed curve. -/
theorem fiber_ncard_eq_zero_iff [CharZero K] [IsAlgClosed K] (a b c : K) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} = 0 ↔ OnMissedCurve a b c := by
  rw [Set.ncard_eq_zero (fiber_finite a b c)]
  constructor
  · intro hS
    by_contra hC
    obtain ⟨p, hp⟩ := (mem_range_iff_not_onMissedCurve a b c).mpr hC
    have : p ∈ {p : K × K × K | F K p = (a, b, c)} := hp
    rw [hS] at this
    exact Set.notMem_empty p this
  · intro hC
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    exact (mem_range_iff_not_onMissedCurve a b c).mp ⟨p, hp⟩ hC

/-- **Nonempty strata.**  Off the missed curve, the fiber has exactly one or
exactly three rational points. -/
theorem fiber_ncard_mem_one_three_of_not_onMissedCurve [CharZero K] [IsAlgClosed K]
    {a b c : K} (hC : ¬ OnMissedCurve a b c) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} ∈ ({1, 3} : Set ℕ) := by
  have h013 := fiber_ncard_mem_zero_one_three a b c
  have h0 : Set.ncard {p : K × K × K | F K p = (a, b, c)} ≠ 0 := fun h =>
    hC ((fiber_ncard_eq_zero_iff a b c).mp h)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h013 ⊢
  rcases h013 with h | h | h
  · exact absurd h h0
  · exact Or.inl h
  · exact Or.inr h

end Stratification

end Alpoge
