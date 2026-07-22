import Alpoge.Counting

/-!
# The sign-biased `S₃` law and the averaged characteristic polynomial

The exact fiber statistics of `Counting.lean` admit a sharp repackaging.
Assign to a fiber with `j ∈ {0, 1, 3}` rational points the unique conjugacy
class of `S₃` with `j` fixed points (`3`-cycles, transpositions, identity),
and to that class the characteristic polynomial `det(I − t·P_σ)` of the
three-dimensional permutation representation:

* `j = 3` : `(1 − t)³`,  `j = 1` : `(1 − t)(1 − t²)`,  `j = 0` : `1 − t³`.

Averaged over the uniform measure on `S₃` these give exactly `1 − t`
(`S3_cycle_index`); averaged over the *fiber-count measure* of the Alpöge
map they give

  `∑_y det(I − t·P_{ν(y)}) = (1 − t) · (q³(1 − t²) + 6N₃t²)`
                          `= (1 − t) · (q³ − b·t²)`,  `b := q³ − 6N₃`,

so the deviation from the uniform (`Chebotarev`) average lies entirely in
the sign-character direction, with exact integer bias `b = (q−1)² + 1`
(characteristic `≠ 3`) resp. `b = q²` (characteristic `3`) — no error term
(`bias_eq_of_three_ne_zero`, `bias_eq_char3`).  Equivalently the counts obey
the sign-biased law `2N₁ = q³ + b`, `3N₀ = q³ − b`, `6N₃ = q³ − b`
(`fiberCount_sign_bias`): the fiber-count distribution is the uniform `S₃`
measure biased by `b/q³ · sgn`.

All statements are division-free consequences of
`finiteField_fiber_statistics`; the bias parameter `κ_q = b/q³` is the
coordinate in which the finite-field law deforms the generic cycle-index
identity, interpolating between `κ = 1` (the map would be a bijection) and
`κ = 0` (uniform `S₃` equidistribution, the `q → ∞` limit).
-/

namespace Alpoge

variable {K : Type*} [Field K]

/-- **The `S₃` cycle-index identity**: the sum of `det(I − t·P_σ)` over the
six elements of `S₃` (in its permutation representation) is `6(1 − t)` — the
uniform average is the single linear factor `1 − t`, independent of the
sheet structure.  Characteristic-free. -/
theorem S3_cycle_index {R : Type*} [CommRing R] (t : R) :
    (1 - t) ^ 3 + 3 * ((1 - t) * (1 - t ^ 2)) + 2 * (1 - t ^ 3) =
      6 * (1 - t) := by
  ring

/-- The characteristic polynomial `det(I − t·P_σ)` of the permutation
representation of the unique `S₃`-class with `j` fixed points, as a function
of `j ∈ {0, 1, 3}` (values outside default to the `j = 0` branch). -/
def permCharPoly (R : Type*) [CommRing R] (j : ℕ) (t : R) : R :=
  if j = 3 then (1 - t) ^ 3
  else if j = 1 then (1 - t) * (1 - t ^ 2)
  else 1 - t ^ 3

section FiniteField

variable [Fintype K] [DecidableEq K] [NeZero (2 : K)]

/-- The number of rational preimages of a target. -/
def fiberCount (v : K × K × K) : ℕ :=
  (Finset.univ.filter fun p : K × K × K => F K p = v).card

theorem fiberCount_mem (v : K × K × K) :
    fiberCount v ∈ ({0, 1, 3} : Set ℕ) := by
  unfold fiberCount
  rw [fiber_filter_card]
  exact card_simpleRootFinset_mem v.1 v.2.1 v.2.2

/-- **The sign-biased `S₃` law.**  With `b := q³ − 6N₃` the exact integer
bias, the fiber counts satisfy `2N₁ = q³ + b` and `3N₀ = q³ − b`: the
fiber-count distribution is the uniform measure on `S₃` deformed by
`(b/q³)·sgn`.  Division-free form over `ℤ`. -/
theorem fiberCount_sign_bias :
    2 * (targetCount (K := K) 1 : ℤ) =
      (Fintype.card K : ℤ) ^ 3 +
        ((Fintype.card K : ℤ) ^ 3 - 6 * (targetCount (K := K) 3 : ℤ)) ∧
    3 * (targetCount (K := K) 0 : ℤ) =
      (Fintype.card K : ℤ) ^ 3 -
        ((Fintype.card K : ℤ) ^ 3 - 6 * (targetCount (K := K) 3 : ℤ)) := by
  have h1 : (targetCount (K := K) 1 : ℤ) + 3 * (targetCount (K := K) 3 : ℤ) =
      (Fintype.card K : ℤ) ^ 3 := by
    exact_mod_cast targetCount_one_add_three (K := K)
  have h0 : (targetCount (K := K) 0 : ℤ) = 2 * (targetCount (K := K) 3 : ℤ) :=
    by exact_mod_cast (finiteField_fiber_statistics (K := K)).2.2.2
  exact ⟨by linear_combination 2 * h1, by linear_combination 3 * h0⟩

/-- **The bias is exactly `(q − 1)² + 1`** in characteristic `≠ 3`: no
error term.  (Generic Chebotarev equidistribution would only force
`b = O(q^{5/2})`.) -/
theorem bias_eq_of_three_ne_zero (h3 : (3 : K) ≠ 0) :
    (Fintype.card K : ℤ) ^ 3 - 6 * (targetCount (K := K) 3 : ℤ) =
      ((Fintype.card K : ℤ) - 1) ^ 2 + 1 := by
  have h6 := six_mul_targetCount_three (K := K)
  rw [if_neg h3] at h6
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  zify [hq] at h6
  linear_combination -h6

/-- **The bias is exactly `q²` in characteristic `3`** — the missed curve is
empty, and the arc `κ_q = b/q³` degenerates to `1/q`. -/
theorem bias_eq_char3 (h3 : (3 : K) = 0) :
    (Fintype.card K : ℤ) ^ 3 - 6 * (targetCount (K := K) 3 : ℤ) =
      (Fintype.card K : ℤ) ^ 2 := by
  have h6 := six_mul_targetCount_three (K := K)
  rw [if_pos h3] at h6
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  zify [hq] at h6
  linear_combination -h6

/-- **The averaged characteristic polynomial of the Alpöge map.**  Summing
`det(I − t·P)` of the virtual Frobenius class over all `q³` targets:

  `∑_y det(I − t·P_{ν(y)}) = (1 − t) · (q³(1 − t²) + 6N₃·t²)`

in every commutative ring — the subtraction-free form of
`q³·(1 − t)(1 − κ_q t²)` with `κ_q = (q³ − 6N₃)/q³`.  The uniform average
would be `q³(1 − t)`; the entire deviation is carried by the
sign-character term. -/
theorem sum_permCharPoly_fiber {R : Type*} [CommRing R] (t : R) :
    ∑ v : K × K × K, permCharPoly R (fiberCount v) t =
      (1 - t) * ((Fintype.card K : R) ^ 3 * (1 - t ^ 2) +
        6 * (targetCount (K := K) 3 : R) * t ^ 2) := by
  -- pointwise: split `permCharPoly` by the 0/1/3 law
  have hpt : ∀ v : K × K × K, permCharPoly R (fiberCount v) t =
      (if fiberCount v = 0 then (1 - t ^ 3 : R) else 0) +
      (if fiberCount v = 1 then ((1 - t) * (1 - t ^ 2) : R) else 0) +
      (if fiberCount v = 3 then ((1 - t) ^ 3 : R) else 0) := by
    intro v
    have h := fiberCount_mem v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;> rw [h] <;> simp [permCharPoly]
  -- each indicator sums to the corresponding target count
  have hcount : ∀ (j : ℕ) (c : R),
      (∑ v : K × K × K, if fiberCount v = j then c else 0) =
        (targetCount (K := K) j : R) * c := by
    intro j c
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  calc ∑ v : K × K × K, permCharPoly R (fiberCount v) t
      = (targetCount (K := K) 0 : R) * (1 - t ^ 3) +
        (targetCount (K := K) 1 : R) * ((1 - t) * (1 - t ^ 2)) +
        (targetCount (K := K) 3 : R) * (1 - t) ^ 3 := by
        simp only [hpt, Finset.sum_add_distrib, hcount]
    _ = (1 - t) * ((Fintype.card K : R) ^ 3 * (1 - t ^ 2) +
        6 * (targetCount (K := K) 3 : R) * t ^ 2) := by
        have h1 : (targetCount (K := K) 1 : R) +
            3 * (targetCount (K := K) 3 : R) = (Fintype.card K : R) ^ 3 := by
          have := congrArg (fun n : ℕ => (n : R))
            (targetCount_one_add_three (K := K))
          push_cast at this
          linear_combination this
        have h0 : (targetCount (K := K) 0 : R) =
            2 * (targetCount (K := K) 3 : R) := by
          have := congrArg (fun n : ℕ => (n : R))
            ((finiteField_fiber_statistics (K := K)).2.2.2)
          push_cast at this
          linear_combination this
        linear_combination (1 - t ^ 3) * h0 + (1 - t) * (1 - t ^ 2) * h1

/-- The averaged characteristic polynomial, fully explicit in
characteristic `≠ 3`: the local factor is
`(1 − t)·(q³(1 − t²) + (q − 1)(q² + 2)·t²) = q³·(1 − t)(1 − κ_q t²)` with
`κ_q = ((q − 1)² + 1)/q³`. -/
theorem sum_permCharPoly_fiber_of_three_ne_zero (h3 : (3 : K) ≠ 0)
    {R : Type*} [CommRing R] (t : R) :
    ∑ v : K × K × K, permCharPoly R (fiberCount v) t =
      (1 - t) * ((Fintype.card K : R) ^ 3 * (1 - t ^ 2) +
        ((Fintype.card K : R) - 1) * ((Fintype.card K : R) ^ 2 + 2) * t ^ 2) := by
  rw [sum_permCharPoly_fiber]
  have h6 := six_mul_targetCount_three (K := K)
  rw [if_neg h3] at h6
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  zify [hq] at h6
  have h6R : 6 * (targetCount (K := K) 3 : R) =
      ((Fintype.card K : R) - 1) * ((Fintype.card K : R) ^ 2 + 2) := by
    have hcast := congrArg (fun n : ℤ => (n : R)) h6
    push_cast at hcast
    linear_combination hcast
  linear_combination (1 - t) * t ^ 2 * h6R

end FiniteField

end Alpoge
