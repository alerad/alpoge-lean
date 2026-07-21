import Alpoge.Basic

/-!
# The wall is the fiber-drop locus; the missed curve is its singular locus

This module identifies the non-properness wall `V(W)`,
`W = 27a²c² − 18abc + 16a + b³c − b²`, with the exact locus where the fiber
count of the Keller map drops, and identifies the missed curve with the
singular locus of `V(W)`.  Headline results:

* `neg_four_mul_wallW_eq_sq_sep` — **discriminant as root separation**: under
  the Vieta relations of the fiber cubic, `−4W = c⁴·∏ᵢ<ⱼ (tᵢ − tⱼ)²`;
* `wallW_ne_zero_of_two_fiber_points` — **arithmetic wall pinch**: over *any*
  field with `2 ≠ 0`, two distinct rational states in one fiber force
  `W ≠ 0`; contrapositive `fiber_ncard_le_one_of_wallW_eq_zero`: on the wall,
  every rational fiber has at most one point — no algebraic closure needed;
* `fiber_ncard_eq_three_iff`, `fiber_ncard_eq_one_iff` — over an
  algebraically closed field of characteristic zero the stratification is
  exact: the fiber has three points iff `W ≠ 0`, one point iff `W = 0` off
  the missed curve, and none iff on the missed curve
  (`fiber_ncard_eq_zero_iff`); packaged in `fiber_ncard_stratification`;
* `onMissedCurve_iff_pderiv_wallPoly_eq_zero`,
  `onMissedCurve_iff_singular_point` — **the missed curve is the singular
  locus of the wall**: with `wallPoly` the formal wall polynomial over `ℤ`
  and `MvPolynomial.pderiv` its formal partials, a `K`-point is critical for
  `W` iff it lies on the missed curve.  The certificate is strikingly small:
  `(3bc − 4)² = W_a + 3c·W_b` (an identity over `ℤ`) and
  `b·W_b + 2(12a − b²) = (b² − 6a)(3bc − 4)`.

Together with `range_eq_compl_missedCurve`, this completes the picture: the
fiber count jumps `3 → 1 → 0` exactly across `V(W)`, and the empty stratum is
exactly the singular curve of `V(W)`.  All proofs are certified polynomial
identities (`linear_combination`) plus the counting layer of
`Alpoge/Basic.lean`.
-/

namespace Alpoge

open MvPolynomial

variable {K : Type*} [Field K]

section WallPinch

/-! ### The arithmetic wall pinch

`third_simpleRoot` showed that two distinct simple rational roots force a
third.  Here we push one step further: three distinct roots force the
discriminant `−4W` to be a product of nonzero squares, so the wall `V(W)`
cannot carry two distinct rational fiber points — over any field. -/

/-- **Discriminant as root separation.**  Under the Vieta relations of the
fiber cubic `cT³ − 2T² + bT − 2a`, the wall satisfies
`−4W = c⁴ (t₁−t₂)² (t₁−t₃)² (t₂−t₃)²`.  This is `fiberCubic_discr` made
explicit on split fibers; the certificate was found by CAS division and is
checked by `linear_combination`. -/
theorem neg_four_mul_wallW_eq_sq_sep {a b c t₁ t₂ t₃ : K}
    (hsum : c * (t₁ + t₂ + t₃) = 2)
    (hpair : c * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) = b)
    (hprod : c * (t₁ * t₂ * t₃) = 2 * a) :
    -4 * wallW a b c =
      c ^ 4 * (t₁ - t₂) ^ 2 * (t₁ - t₃) ^ 2 * (t₂ - t₃) ^ 2 := by
  unfold wallW
  linear_combination
    (-c ^ 3 * t₁ ^ 3 * t₂ ^ 2 + 2 * c ^ 3 * t₁ ^ 3 * t₂ * t₃ -
      c ^ 3 * t₁ ^ 3 * t₃ ^ 2 - c ^ 3 * t₁ ^ 2 * t₂ ^ 3 -
      15 * c ^ 3 * t₁ ^ 2 * t₂ ^ 2 * t₃ - 15 * c ^ 3 * t₁ ^ 2 * t₂ * t₃ ^ 2 -
      c ^ 3 * t₁ ^ 2 * t₃ ^ 3 + 2 * c ^ 3 * t₁ * t₂ ^ 3 * t₃ -
      15 * c ^ 3 * t₁ * t₂ ^ 2 * t₃ ^ 2 + 2 * c ^ 3 * t₁ * t₂ * t₃ ^ 3 -
      c ^ 3 * t₂ ^ 3 * t₃ ^ 2 - c ^ 3 * t₂ ^ 2 * t₃ ^ 3 -
      2 * c ^ 2 * t₁ ^ 2 * t₂ ^ 2 + 4 * c ^ 2 * t₁ ^ 2 * t₂ * t₃ -
      2 * c ^ 2 * t₁ ^ 2 * t₃ ^ 2 + 4 * c ^ 2 * t₁ * t₂ ^ 2 * t₃ +
      4 * c ^ 2 * t₁ * t₂ * t₃ ^ 2 - 2 * c ^ 2 * t₂ ^ 2 * t₃ ^ 2 +
      16 * c * t₁ * t₂ * t₃) * hsum +
    (4 * b ^ 2 * c + 4 * b * c ^ 2 * t₁ * t₂ + 4 * b * c ^ 2 * t₁ * t₃ +
      4 * b * c ^ 2 * t₂ * t₃ - 4 * b + 4 * c ^ 3 * t₁ ^ 2 * t₂ ^ 2 +
      8 * c ^ 3 * t₁ ^ 2 * t₂ * t₃ + 4 * c ^ 3 * t₁ ^ 2 * t₃ ^ 2 +
      8 * c ^ 3 * t₁ * t₂ ^ 2 * t₃ + 8 * c ^ 3 * t₁ * t₂ * t₃ ^ 2 +
      4 * c ^ 3 * t₂ ^ 2 * t₃ ^ 2 - 36 * c ^ 2 * t₁ * t₂ * t₃ -
      4 * c * t₁ * t₂ - 4 * c * t₁ * t₃ - 4 * c * t₂ * t₃) * hpair +
    (54 * a * c ^ 2 - 36 * b * c + 27 * c ^ 3 * t₁ * t₂ * t₃ + 32) * hprod

/-- On the plane `c = 0`, a *single* simple affine root already forces
`W ≠ 0`: on the root locus, `(b − 4t)² = −W`. -/
theorem wallW_ne_zero_of_simpleRoot_czero {a b t : K}
    (hP : -2 * t ^ 2 + b * t - 2 * a = 0) (hd : -4 * t + b ≠ 0) :
    wallW a b 0 ≠ 0 := by
  intro hW
  apply hd
  have hsq : (-4 * t + b) ^ 2 = 0 := by
    unfold wallW at hW
    linear_combination (-8 : K) * hP - hW
  exact sq_eq_zero_iff.mp hsq

/-- Two distinct simple affine roots of a genuine fiber cubic force `W ≠ 0`:
Vieta closure supplies the third root, and the separation identity exhibits
`−4W` as a product of nonzero factors. -/
theorem wallW_ne_zero_of_two_simpleRoots {a b c t₁ t₂ : K} (hc : c ≠ 0)
    (hne : t₁ ≠ t₂)
    (h₁ : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 ∧
      3 * c * t₁ ^ 2 - 4 * t₁ + b ≠ 0)
    (h₂ : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 ∧
      3 * c * t₂ ^ 2 - 4 * t₂ + b ≠ 0) :
    wallW a b c ≠ 0 := by
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
  have hd₁ : 3 * c * t₁ ^ 2 - 4 * t₁ + b = c * (t₁ - t₂) * (t₁ - t₃) := by
    linear_combination 2 * t₁ * hsum - hpair
  have hd₂ : 3 * c * t₂ ^ 2 - 4 * t₂ + b = c * (t₂ - t₁) * (t₂ - t₃) := by
    linear_combination 2 * t₂ * hsum - hpair
  have ht₁₃ : t₁ ≠ t₃ := by
    intro heq
    exact h₁.2 (by rw [hd₁, heq, sub_self, mul_zero])
  have ht₂₃ : t₂ ≠ t₃ := by
    intro heq
    exact h₂.2 (by rw [hd₂, heq, sub_self, mul_zero])
  intro hW
  have hkey := neg_four_mul_wallW_eq_sq_sep hsum hpair hprod
  rw [hW, mul_zero] at hkey
  have hne' : c ^ 4 * (t₁ - t₂) ^ 2 * (t₁ - t₃) ^ 2 * (t₂ - t₃) ^ 2 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero 4 hc)
          (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
        (pow_ne_zero 2 (sub_ne_zero.mpr ht₁₃)))
      (pow_ne_zero 2 (sub_ne_zero.mpr ht₂₃))
  exact hne' hkey.symm

/-- **Wall pinch, projective form.**  Two distinct simple projective roots of
the binary fiber cubic force `W ≠ 0` — over any field, with no
characteristic hypothesis. -/
theorem wallW_ne_zero_of_two_projectiveSimpleRoots {a b c : K}
    {r₁ r₂ : Option K} (h₁ : projectiveSimpleRoot a b c r₁)
    (h₂ : projectiveSimpleRoot a b c r₂) (hne : r₁ ≠ r₂) :
    wallW a b c ≠ 0 := by
  cases r₁ with
  | none =>
      cases r₂ with
      | none => exact (hne rfl).elim
      | some t =>
          have hc : c = 0 := h₁
          subst hc
          obtain ⟨hP, hd⟩ := (h₂ :
            0 * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
              3 * 0 * t ^ 2 - 4 * t + b ≠ 0)
          have hP' : -2 * t ^ 2 + b * t - 2 * a = 0 := by linear_combination hP
          have hd' : -4 * t + b ≠ 0 := fun h0 => hd (by linear_combination h0)
          exact wallW_ne_zero_of_simpleRoot_czero hP' hd'
  | some t₁ =>
      cases r₂ with
      | none =>
          have hc : c = 0 := h₂
          subst hc
          obtain ⟨hP, hd⟩ := (h₁ :
            0 * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 ∧
              3 * 0 * t₁ ^ 2 - 4 * t₁ + b ≠ 0)
          have hP' : -2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by linear_combination hP
          have hd' : -4 * t₁ + b ≠ 0 := fun h0 => hd (by linear_combination h0)
          exact wallW_ne_zero_of_simpleRoot_czero hP' hd'
      | some t₂ =>
          by_cases hc : c = 0
          · subst hc
            obtain ⟨hP, hd⟩ := (h₁ :
              0 * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 ∧
                3 * 0 * t₁ ^ 2 - 4 * t₁ + b ≠ 0)
            have hP' : -2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by
              linear_combination hP
            have hd' : -4 * t₁ + b ≠ 0 := fun h0 => hd (by linear_combination h0)
            exact wallW_ne_zero_of_simpleRoot_czero hP' hd'
          · exact wallW_ne_zero_of_two_simpleRoots hc
              (fun h => hne (congrArg some h)) h₁ h₂

/-- **Arithmetic wall pinch.**  Over any field with `2 ≠ 0`, two distinct
rational states in one fiber force `W ≠ 0`: the wall carries no multiple
rational point of any fiber. -/
theorem wallW_ne_zero_of_two_fiber_points [NeZero (2 : K)] {a b c : K}
    {p₁ p₂ : K × K × K} (h₁ : F K p₁ = (a, b, c)) (h₂ : F K p₂ = (a, b, c))
    (hne : p₁ ≠ p₂) : wallW a b c ≠ 0 := by
  let e := fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)
  let q₁ : {p : K × K × K // F K p = (a, b, c)} := ⟨p₁, h₁⟩
  let q₂ : {p : K × K × K // F K p = (a, b, c)} := ⟨p₂, h₂⟩
  have hq : (e q₁).1 ≠ (e q₂).1 := fun he =>
    hne (Subtype.ext_iff.mp (e.injective (Subtype.ext he)))
  exact wallW_ne_zero_of_two_projectiveSimpleRoots (e q₁).2 (e q₂).2 hq

/-- **The wall pinches rational fibers.**  On `V(W)` every fiber has at most
one rational point — over any field with `2 ≠ 0`, algebraically closed or
not. -/
theorem fiber_ncard_le_one_of_wallW_eq_zero [NeZero (2 : K)] {a b c : K}
    (hW : wallW a b c = 0) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ :=
    (Set.one_lt_ncard (fiber_finite a b c)).mp h
  exact wallW_ne_zero_of_two_fiber_points hp₁ hp₂ hne hW

end WallPinch


section ExactStratification

/-! ### Exact fiber counts across the wall

Over an algebraically closed field of characteristic zero the counting
becomes exact: `3` off the wall, `1` on the wall off the missed curve, `0` on
the missed curve.  The new ingredient beyond the pinch is that off the wall
*every* root of the fiber cubic is automatically simple
(`simpleRoot_of_root_of_wallW_ne_zero`, from the universal certificate
`disc_factorization`), so one square root of the residual discriminant
produces a second fiber point. -/

/-- Off the wall, every root of the fiber cubic is simple: at a double root
both terms of the universal certificate
`−4W = P′(t)²·Δ(t) + λ(t)·P(t)` vanish. -/
theorem simpleRoot_of_root_of_wallW_ne_zero [NeZero (2 : K)] {a b c t : K}
    (hW : wallW a b c ≠ 0)
    (hP : c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0) :
    3 * c * t ^ 2 - 4 * t + b ≠ 0 := by
  intro hd
  apply hW
  have key := disc_factorization a b c t
  rw [hP, mul_zero, add_zero, hd] at key
  have h4 : (-4 : K) ≠ 0 := by
    refine neg_ne_zero.mpr ?_
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero two_ne_zero two_ne_zero
  have hzero : (-4 : K) * wallW a b c = 0 := by
    rw [key]
    ring
  exact (mul_eq_zero.mp hzero).resolve_left h4

/-- Off the wall, over an algebraically closed field of characteristic zero,
the fiber contains two distinct rational states: one from any root of the
fiber cubic (automatically simple), a second from the quadratic formula on
the residual quadratic, whose discriminant is a nonzero perfect square. -/
theorem exists_two_fiber_points_of_wallW_ne_zero [CharZero K] [IsAlgClosed K]
    {a b c : K} (hW : wallW a b c ≠ 0) :
    ∃ p₁ p₂ : K × K × K,
      F K p₁ = (a, b, c) ∧ F K p₂ = (a, b, c) ∧ p₁ ≠ p₂ := by
  by_cases hc : c = 0
  · subst hc
    obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - 16 * a) zero_lt_two
    have hσ0 : σ ≠ 0 := by
      intro h0
      apply hW
      rw [h0] at hσ
      unfold wallW
      linear_combination hσ
    set t : K := (b + σ) / 4 with ht
    have hP : (0 : K) * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 := by
      rw [ht]
      linear_combination (-1 / 8 : K) * hσ
    have hd : 3 * (0 : K) * t ^ 2 - 4 * t + b ≠ 0 := by
      have hval : 3 * (0 : K) * t ^ 2 - 4 * t + b = -σ := by
        rw [ht]
        ring
      rw [hval]
      exact neg_ne_zero.mpr hσ0
    refine ⟨(0, b, a - 4 * b ^ 2), fiberPoint b 0 t,
      plane_section (K := K) a b, fiberPoint_mem hP hd, ?_⟩
    intro heq
    have hx : (fiberPoint b 0 t).1 = 0 := by
      rw [← heq]
    have hx' : (fiberPoint b 0 t).1 ≠ 0 := by
      dsimp only [fiberPoint]
      exact div_ne_zero two_ne_zero hd
    exact hx' hx
  · have hdeg : (fiberCubic a b c).toPoly.degree ≠ 0 := by
      rw [Cubic.degree_of_a_ne_zero]
      · norm_num
      · simpa [fiberCubic] using hc
    obtain ⟨t₁, ht₁⟩ := IsAlgClosed.exists_root (fiberCubic a b c).toPoly hdeg
    have hP₁ : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by
      simp only [Polynomial.IsRoot] at ht₁
      simp [Cubic.toPoly, fiberCubic] at ht₁
      linear_combination ht₁
    have hd₁ := simpleRoot_of_root_of_wallW_ne_zero hW hP₁
    obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq
      ((c * t₁ - 2) ^ 2 - 4 * c * (c * t₁ ^ 2 - 2 * t₁ + b)) zero_lt_two
    have hσ0 : σ ≠ 0 := by
      intro h0
      apply hW
      rw [h0] at hσ
      have key := disc_factorization a b c t₁
      rw [hP₁, mul_zero, add_zero, ← hσ] at key
      have hzero : (-4 : K) * wallW a b c = 0 := by
        rw [key]
        ring
      have h4 : (-4 : K) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp hzero).resolve_left h4
    set t₂ : K := (2 - c * t₁ + σ) / (2 * c) with ht₂
    have hP₂ : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 := by
      rw [ht₂]
      exact sibling_root hc hP₁ hσ
    have hd₂ := simpleRoot_of_root_of_wallW_ne_zero hW hP₂
    have ht₂₁ : t₂ ≠ t₁ := by
      intro heq
      have h2c : (2 : K) * c ≠ 0 := mul_ne_zero two_ne_zero hc
      have hσval : σ = 3 * c * t₁ - 2 := by
        rw [ht₂] at heq
        field_simp at heq
        linear_combination heq
      apply hd₁
      have h0 : (3 * c * t₁ - 2) ^ 2 =
          (c * t₁ - 2) ^ 2 - 4 * c * (c * t₁ ^ 2 - 2 * t₁ + b) := by
        rw [← hσval]
        exact hσ
      have h4c : -4 * c * (3 * c * t₁ ^ 2 - 4 * t₁ + b) = 0 := by
        linear_combination -h0
      have hc4 : (-4 : K) * c ≠ 0 :=
        mul_ne_zero (by norm_num) hc
      exact (mul_eq_zero.mp h4c).resolve_left hc4
    refine ⟨fiberPoint b c t₁, fiberPoint b c t₂,
      fiberPoint_mem hP₁ hd₁, fiberPoint_mem hP₂ hd₂, ?_⟩
    intro heq
    have hres := fiberPoint_resolvent b c t₁
    rw [heq, fiberPoint_resolvent b c t₂] at hres
    exact ht₂₁ hres

/-- **Full stratum.**  Over an algebraically closed characteristic-zero
field, the fiber has exactly three rational points iff the target is off the
wall `V(W)`. -/
theorem fiber_ncard_eq_three_iff [CharZero K] [IsAlgClosed K] (a b c : K) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} = 3 ↔ wallW a b c ≠ 0 := by
  constructor
  · intro h3
    obtain ⟨p₁, p₂, p₃, h12, _, _, hS⟩ := Set.ncard_eq_three.mp h3
    have hp₁ : F K p₁ = (a, b, c) := by
      have hmem : p₁ ∈ {p : K × K × K | F K p = (a, b, c)} := by
        rw [hS]
        exact Set.mem_insert _ _
      exact hmem
    have hp₂ : F K p₂ = (a, b, c) := by
      have hmem : p₂ ∈ {p : K × K × K | F K p = (a, b, c)} := by
        rw [hS]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      exact hmem
    exact wallW_ne_zero_of_two_fiber_points hp₁ hp₂ h12
  · intro hW
    obtain ⟨p₁, p₂, h₁, h₂, hne⟩ := exists_two_fiber_points_of_wallW_ne_zero hW
    have hlt : 1 < Set.ncard {p : K × K × K | F K p = (a, b, c)} :=
      (Set.one_lt_ncard (fiber_finite a b c)).mpr ⟨p₁, h₁, p₂, h₂, hne⟩
    have h013 := fiber_ncard_mem_zero_one_three a b c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h013
    rcases h013 with h | h | h
    · omega
    · omega
    · exact h

/-- **Middle stratum.**  The fiber has exactly one rational point iff the
target is on the wall but off the missed curve. -/
theorem fiber_ncard_eq_one_iff [CharZero K] [IsAlgClosed K] (a b c : K) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} = 1 ↔
      wallW a b c = 0 ∧ ¬ OnMissedCurve a b c := by
  constructor
  · intro h1
    constructor
    · by_contra hW
      have h3 := (fiber_ncard_eq_three_iff a b c).mpr hW
      omega
    · intro hC
      have h0 := (fiber_ncard_eq_zero_iff a b c).mpr hC
      omega
  · rintro ⟨hW, hC⟩
    have h013 := fiber_ncard_mem_zero_one_three a b c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h013
    have h0 : Set.ncard {p : K × K × K | F K p = (a, b, c)} ≠ 0 := fun h =>
      hC ((fiber_ncard_eq_zero_iff a b c).mp h)
    have h3 : Set.ncard {p : K × K × K | F K p = (a, b, c)} ≠ 3 := fun h =>
      (fiber_ncard_eq_three_iff a b c).mp h hW
    rcases h013 with h | h | h
    · exact absurd h h0
    · exact h
    · exact absurd h h3

/-- **The wall stratification, complete.**  Over an algebraically closed
characteristic-zero field the fiber count reads off the wall exactly:
`3` off `V(W)`, `1` on `V(W)` off the missed curve, `0` on the missed
curve.  This upgrades the `0/1/3` law to an exact dictionary and identifies
`V(W)` as the locus of fiber collapse — the `K`-point shadow of
non-properness. -/
theorem fiber_ncard_stratification [CharZero K] [IsAlgClosed K] (a b c : K) :
    (Set.ncard {p : K × K × K | F K p = (a, b, c)} = 3 ↔ wallW a b c ≠ 0) ∧
    (Set.ncard {p : K × K × K | F K p = (a, b, c)} = 1 ↔
      wallW a b c = 0 ∧ ¬ OnMissedCurve a b c) ∧
    (Set.ncard {p : K × K × K | F K p = (a, b, c)} = 0 ↔
      OnMissedCurve a b c) :=
  ⟨fiber_ncard_eq_three_iff a b c, fiber_ncard_eq_one_iff a b c,
    fiber_ncard_eq_zero_iff a b c⟩

end ExactStratification


section SingularLocus

/-! ### The missed curve is the singular locus of the wall

The wall polynomial is now treated formally, over `ℤ`, with genuine
`MvPolynomial.pderiv` partials.  The critical equations `∇W = 0` reduce to
the missed-curve equations through two tiny certificates:

* `(3bc − 4)² = W_a + 3c·W_b` — an identity over `ℤ`, characteristic-free;
* `b·W_b + 2(12a − b²) = (b² − 6a)(3bc − 4)` — needing only `2 ≠ 0`.

In particular a critical point of `W` automatically lies on `V(W)`
(`wallW_eq_zero_of_onMissedCurve`): the critical locus of the wall
polynomial *is* its singular curve, and that curve is exactly the omitted
image locus. -/

/-- The formal wall polynomial over the integers; `X 0, X 1, X 2` are
`a, b, c`. -/
noncomputable def wallPoly : MvPolynomial (Fin 3) ℤ :=
  27 * X 0 ^ 2 * X 2 ^ 2 - 18 * X 0 * X 1 * X 2 + 16 * X 0 +
    X 1 ^ 3 * X 2 - X 1 ^ 2

private theorem pderiv_ofNat' {σ R : Type*} [CommSemiring R] {i : σ} (n : ℕ)
    [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ R) = 0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial σ R) n]
  exact pderiv_C

/-- Evaluating the formal wall polynomial recovers `wallW`. -/
theorem aeval_wallPoly (a b c : K) :
    aeval ![a, b, c] wallPoly = wallW a b c := by
  simp only [wallPoly, wallW, map_add, map_sub, map_mul, map_pow, map_ofNat,
    aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The formal `a`-partial of the wall polynomial, evaluated. -/
theorem aeval_pderiv_wallPoly_zero (a b c : K) :
    aeval ![a, b, c] (pderiv 0 wallPoly) =
      54 * a * c ^ 2 - 18 * b * c + 16 := by
  have hp : pderiv 0 wallPoly =
      54 * X 0 * X 2 ^ 2 - 18 * X 1 * X 2 + 16 := by
    simp only [wallPoly, map_add, map_sub, pderiv_mul, pderiv_pow,
      pderiv_ofNat', pderiv_X_self, pderiv_X, Pi.single_apply,
      Nat.cast_ofNat, Fin.reduceEq, reduceIte]
    ring
  rw [hp]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The formal `b`-partial of the wall polynomial, evaluated. -/
theorem aeval_pderiv_wallPoly_one (a b c : K) :
    aeval ![a, b, c] (pderiv 1 wallPoly) =
      -18 * a * c + 3 * b ^ 2 * c - 2 * b := by
  have hp : pderiv 1 wallPoly =
      -18 * X 0 * X 2 + 3 * X 1 ^ 2 * X 2 - 2 * X 1 := by
    simp only [wallPoly, map_add, map_sub, pderiv_mul, pderiv_pow,
      pderiv_ofNat', pderiv_X_self, pderiv_X, Pi.single_apply,
      Nat.cast_ofNat, Fin.reduceEq, reduceIte]
    ring
  rw [hp]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The formal `c`-partial of the wall polynomial, evaluated. -/
theorem aeval_pderiv_wallPoly_two (a b c : K) :
    aeval ![a, b, c] (pderiv 2 wallPoly) =
      54 * a ^ 2 * c - 18 * a * b + b ^ 3 := by
  have hp : pderiv 2 wallPoly =
      54 * X 0 ^ 2 * X 2 - 18 * X 0 * X 1 + X 1 ^ 3 := by
    simp only [wallPoly, map_add, map_sub, pderiv_mul, pderiv_pow,
      pderiv_ofNat', pderiv_X_self, pderiv_X, Pi.single_apply,
      Nat.cast_ofNat, Fin.reduceEq, reduceIte]
    ring
  rw [hp]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- On the missed curve all three formal partials of the wall vanish.
Certificates are cleared of denominators: `2·W_a`, `2·W_b`, `8·W_c` are
integer combinations of `12a − b²` and `3bc − 4`. -/
theorem pderiv_wallPoly_eq_zero_of_onMissedCurve [NeZero (2 : K)] {a b c : K}
    (h : OnMissedCurve a b c) (i : Fin 3) :
    aeval ![a, b, c] (pderiv i wallPoly) = 0 := by
  obtain ⟨h12, h34⟩ := h
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 ^ 3 by norm_num]
    exact pow_ne_zero 3 h2
  have H0 : aeval ![a, b, c] (pderiv (0 : Fin 3) wallPoly) = 0 := by
    rw [aeval_pderiv_wallPoly_zero]
    apply mul_left_cancel₀ h2
    rw [mul_zero]
    linear_combination 9 * c ^ 2 * h12 + (3 * b * c - 8) * h34
  have H1 : aeval ![a, b, c] (pderiv (1 : Fin 3) wallPoly) = 0 := by
    rw [aeval_pderiv_wallPoly_one]
    apply mul_left_cancel₀ h2
    rw [mul_zero]
    linear_combination (-3 : K) * c * h12 + b * h34
  have H2 : aeval ![a, b, c] (pderiv (2 : Fin 3) wallPoly) = 0 := by
    rw [aeval_pderiv_wallPoly_two]
    apply mul_left_cancel₀ h8
    rw [mul_zero]
    linear_combination (36 * a * c + 3 * b ^ 2 * c - 12 * b) * h12 +
      b ^ 3 * h34
  fin_cases i
  · exact H0
  · exact H1
  · exact H2

/-- **The missed curve is the critical locus of the wall.**  Over any field
with `2 ≠ 0`, the three formal partial derivatives of the wall polynomial
vanish at `(a, b, c)` exactly on the missed curve.  The backward direction
rests on the characteristic-free identity `(3bc − 4)² = W_a + 3c·W_b`. -/
theorem onMissedCurve_iff_pderiv_wallPoly_eq_zero [NeZero (2 : K)]
    (a b c : K) :
    OnMissedCurve a b c ↔
      ∀ i : Fin 3, aeval ![a, b, c] (pderiv i wallPoly) = 0 := by
  constructor
  · exact fun h i => pderiv_wallPoly_eq_zero_of_onMissedCurve h i
  · intro h
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    have hWa := h 0
    have hWb := h 1
    rw [aeval_pderiv_wallPoly_zero] at hWa
    rw [aeval_pderiv_wallPoly_one] at hWb
    have hsq : (3 * b * c - 4) ^ 2 = 0 := by
      linear_combination hWa + 3 * c * hWb
    have h34 : 3 * b * c = 4 := by
      have := sq_eq_zero_iff.mp hsq
      linear_combination this
    have h12 : 12 * a = b ^ 2 := by
      apply mul_left_cancel₀ h2
      linear_combination (b ^ 2 - 6 * a) * h34 - b * hWb
    exact ⟨h12, h34⟩

/-- **The missed curve is the singular locus of `V(W)`.**  Over any
characteristic-zero field, `(a, b, c)` is a singular point of the wall
hypersurface — the wall polynomial and all its formal partials vanish —
exactly when it lies on the missed curve.  The omitted image locus of the
Keller map is precisely where the discriminant hypersurface of its fiber
family is singular. -/
theorem onMissedCurve_iff_singular_point [CharZero K] (a b c : K) :
    OnMissedCurve a b c ↔
      (aeval ![a, b, c] wallPoly = 0 ∧
        ∀ i : Fin 3, aeval ![a, b, c] (pderiv i wallPoly) = 0) := by
  constructor
  · intro h
    refine ⟨?_, fun i => pderiv_wallPoly_eq_zero_of_onMissedCurve h i⟩
    rw [aeval_wallPoly]
    exact wallW_eq_zero_of_onMissedCurve h
  · rintro ⟨_, hcrit⟩
    exact (onMissedCurve_iff_pderiv_wallPoly_eq_zero a b c).mpr hcrit

end SingularLocus

end Alpoge
