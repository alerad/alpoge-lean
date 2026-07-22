import Alpoge.Basic

/-!
# The double-root slice is affine three-space: Tao's chart, verified

Tao's digestion of the counterexample (2026-07-21) presents the source as
the slice `X = {(L,Q) : Res(L,Q) = 1, D(LQ) = 1}` of the multiplication map
`(L,Q) ↦ LQ` on binary forms, where `D` is a hyperplane of double-root type,
normalized to the `z²w`-coefficient.  In coordinates `L = az + bw`,
`Q = cz² + dzw + ew²` the slice is

`a²e − abd + cb² = 1`  and  `ad + bc = 1`,

and the "affine miracle" is that this variety is polynomially isomorphic to
affine three-space.  This module verifies that chart at the `K`-point level,
over every field with `2 ≠ 0` (extending the characteristic-zero setting):

* `res_eq_key_combination` — the identity
  `Res = b·(ad + bc) + a·(ae − 2bd)` that drives Will Sawin's coordinate
  reduction: on the slice, `b = 1 + a·(2bd − ae)`;
* `sliceChart_mem` — Tao's explicit chart `(x, y, z) ↦ (a, b, c, d, e)`
  lands in the slice (a `ℤ`-polynomial identity, characteristic-free);
* `sliceEquiv` — the slice is equivalent to `K³`, with Tao's polynomial
  chart as inverse; the surjectivity proof follows his structure exactly:
  the `b`- and `c`-identities hold outright, and the `d`- and `e`-identities
  follow by cancelling `a`, with the `a = 0` fiber checked separately.

The cohomological explanation of *why* this trivialization had to exist
(the slice is an affine-line torsor over `𝔸²`, and `H¹(𝔸², O) = 0`,
`Pic(𝔸²) = 0`) is not formalized; this module pins down its `K`-point
content.  All certificates were found by CAS reduction and are checked by
`linear_combination`.
-/

namespace Alpoge

variable {K : Type*} [Field K]

/-- The double-root slice: `Res(L,Q) = 1` and the `z²w`-coefficient of `LQ`
equals `1`, for `L = az + bw`, `Q = cz² + dzw + ew²`, coordinates ordered
`(a, b, c, d, e)`. -/
def OnDoubleRootSlice (v : K × K × K × K × K) : Prop :=
  v.1 ^ 2 * v.2.2.2.2 - v.1 * v.2.1 * v.2.2.2.1 + v.2.2.1 * v.2.1 ^ 2 = 1 ∧
    v.1 * v.2.2.2.1 + v.2.1 * v.2.2.1 = 1

/-- **The key resultant combination** (Sawin): the resultant decomposes as
`Res = b·(ad + bc) + a·(ae − 2bd)`.  On the slice this forces
`b = 1 + a·(2bd − ae)`: the coordinate `y = 2bd − ae` makes `b` polynomial
in `(a, y)`. -/
theorem res_eq_key_combination (a b c d e : K) :
    a ^ 2 * e - a * b * d + c * b ^ 2 =
      b * (a * d + b * c) + a * (a * e - 2 * b * d) := by
  ring

/-- Tao's chart `(x, y, z) ↦ (a, b, c, d, e)`, in the scaling with
`ℤ`-polynomial coefficients (`y` is half of Tao's `y`-coordinate). -/
def sliceChart (x y z : K) : K × K × K × K × K :=
  (x,
   1 + 2 * x * y,
   1 - 3 * x * y + x ^ 2 * z,
   y - x * z + 6 * x * y ^ 2 - 2 * x ^ 2 * y * z,
   -2 * z + 16 * y ^ 2 - 8 * x * y * z + 24 * x * y ^ 3 - 8 * x ^ 2 * y ^ 2 * z)

/-- The chart lands in the slice: two `ℤ`-polynomial identities,
characteristic-free. -/
theorem sliceChart_mem (x y z : K) :
    OnDoubleRootSlice (sliceChart x y z) := by
  constructor <;> · simp only [sliceChart]; ring

/-- The retraction: `(a, b, c, d, e) ↦ (a, (2bd − ae)/2, …)`. -/
noncomputable def sliceCoords (v : K × K × K × K × K) : K × K × K :=
  (v.1,
   (2 * v.2.1 * v.2.2.2.1 - v.1 * v.2.2.2.2) / 2,
   (4 * v.2.2.2.1 ^ 2 + 2 * v.2.2.1 * v.2.2.2.2 +
      12 * v.2.1 * v.2.2.2.1 ^ 2 + 6 * v.2.1 * v.2.2.1 * v.2.2.2.2 -
      9 * v.2.2.2.2) / 2)

/-- Retraction of the chart is the identity: the chart is injective with an
explicit polynomial (in `1/2`) left inverse. -/
theorem sliceCoords_sliceChart [NeZero (2 : K)] (x y z : K) :
    sliceCoords (sliceChart x y z) = (x, y, z) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;>
    · simp only [sliceCoords, sliceChart]
      field_simp
      ring

/-- **Surjectivity of the chart**: every point of the slice is hit, and the
chart inverts the retraction there.  The proof follows Tao's derivation
exactly: with `u = 2bd − ae` and
`w = 4d² + 2ce + 12bd² + 6bce − 9e`, the slice equations force

* `b = 1 + au` (Sawin's observation, an outright consequence of
  `Res = b·(ad + bc) + a·(ae − 2bd)`),
* `2c = 2 − 3au + a²w` (outright),
* `2d = u − aw + 3au² − a²uw` and `e = −w + 4u² − 2auw + 3au³ − a²u²w`
  (after cancelling `a` resp. `a²`; the `a = 0` fibers, where `b = 1` is
  forced, are checked separately).

Every step is a `linear_combination` against a CAS-extracted certificate. -/
theorem sliceChart_sliceCoords [NeZero (2 : K)] (v : K × K × K × K × K)
    (hv : OnDoubleRootSlice v) :
    sliceChart (sliceCoords v).1 (sliceCoords v).2.1 (sliceCoords v).2.2 = v := by
  obtain ⟨a, b, c, d, e⟩ := v
  simp only [OnDoubleRootSlice] at hv
  obtain ⟨hg1, hg2⟩ := hv
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  -- Sawin's coordinate: on the slice `b = 1 + a(2bd − ae)`.
  have hbC : 1 + a * (2 * b * d - a * e) = b := by
    linear_combination -hg1 + b * hg2
  -- Cleared `c`-identity.
  have hcC : 2 - 3 * a * (2 * b * d - a * e) +
      a ^ 2 * (4 * d ^ 2 + 2 * c * e + 12 * b * d ^ 2 + 6 * b * c * e - 9 * e) =
        2 * c := by
    linear_combination (6 * b * c + 2 * c - 6) * hg1 +
      (12 * a * b * d + 4 * a * d - 6 * b ^ 2 * c - 2 * b * c + 4) * hg2
  -- Cleared `d`-identity: cancel one factor of `a`.
  have hdC : (2 * b * d - a * e) -
      a * (4 * d ^ 2 + 2 * c * e + 12 * b * d ^ 2 + 6 * b * c * e - 9 * e) +
      3 * a * (2 * b * d - a * e) ^ 2 -
      a ^ 2 * (2 * b * d - a * e) *
        (4 * d ^ 2 + 2 * c * e + 12 * b * d ^ 2 + 6 * b * c * e - 9 * e) =
        2 * d := by
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      linear_combination (-2 : K) * d * hbC
    · refine mul_left_cancel₀ ha ?_
      linear_combination (-12 * a ^ 3 * d * e) * hg1 +
        (-6 * a ^ 3 * d * e - 12 * a ^ 2 * b * d ^ 2 - 2 * a ^ 2 * c * e -
          4 * a ^ 2 * d ^ 2 - 2 * a * d) * hbC +
        (6 * a ^ 4 * e ^ 2 - 8 * a ^ 2 * e) * hg2
  -- Cleared `e`-identity: cancel a factor of `a²`.
  have heC : -(4 * d ^ 2 + 2 * c * e + 12 * b * d ^ 2 + 6 * b * c * e - 9 * e) +
      4 * (2 * b * d - a * e) ^ 2 -
      2 * a * (2 * b * d - a * e) *
        (4 * d ^ 2 + 2 * c * e + 12 * b * d ^ 2 + 6 * b * c * e - 9 * e) +
      3 * a * (2 * b * d - a * e) ^ 3 -
      a ^ 2 * (2 * b * d - a * e) ^ 2 *
        (4 * d ^ 2 + 2 * c * e + 12 * b * d ^ 2 + 6 * b * c * e - 9 * e) =
        e := by
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      linear_combination (-8 : K) * e * hg2 +
        (-16 * b * d ^ 2 - 4 * d ^ 2 - 2 * c * e) * hbC
    · refine mul_left_cancel₀ (pow_ne_zero 2 ha) ?_
      linear_combination (-(6 * a ^ 2 * b * e + 2 * a ^ 2 * e)) * hg1 +
        (6 * a ^ 4 * b * c * e ^ 2 + 12 * a ^ 4 * b * d ^ 2 * e +
          2 * a ^ 4 * c * e ^ 2 + 4 * a ^ 4 * d ^ 2 * e - 6 * a ^ 4 * e ^ 2 -
          12 * a ^ 3 * b ^ 2 * c * d * e - 24 * a ^ 3 * b ^ 2 * d ^ 3 -
          4 * a ^ 3 * b * c * d * e - 8 * a ^ 3 * b * d ^ 3 +
          6 * a ^ 3 * b * d * e - 6 * a ^ 2 * b ^ 2 * c * e -
          8 * a ^ 2 * b * c * e - 16 * a ^ 2 * b * d ^ 2 - 2 * a ^ 2 * c * e -
          4 * a ^ 2 * d ^ 2 + 6 * a ^ 2 * e) * hbC
  -- Assemble the five components from the cleared identities.
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · simp only [sliceChart, sliceCoords]
    field_simp
    linear_combination hbC
  · simp only [sliceChart, sliceCoords]
    field_simp
    linear_combination hcC
  · simp only [sliceChart, sliceCoords]
    field_simp
    linear_combination 2 * hdC
  · simp only [sliceChart, sliceCoords]
    field_simp
    linear_combination 8 * heC

/-- **The affine miracle at `K`-points.**  The double-root slice
`{Res(L,Q) = 1, D(LQ) = 1}` is in bijection with `K³`, with Tao's polynomial
chart as one direction and the polynomial-in-`1/2` retraction as the other:
machine-verified over every field in which `2 ≠ 0`.  This is the `K`-point
content of the statement that the slice is isomorphic to affine three-space
— the trivialization whose *existence* is forced by
`H¹(𝔸², O) = Pic(𝔸²) = 0` once the slice is recognized as an affine-line
torsor over the `(a, y)`-plane. -/
noncomputable def sliceEquiv [NeZero (2 : K)] :
    {v : K × K × K × K × K // OnDoubleRootSlice v} ≃ K × K × K where
  toFun v := sliceCoords v.1
  invFun p := ⟨sliceChart p.1 p.2.1 p.2.2, sliceChart_mem p.1 p.2.1 p.2.2⟩
  left_inv v := Subtype.ext (sliceChart_sliceCoords v.1 v.2)
  right_inv p := sliceCoords_sliceChart p.1 p.2.1 p.2.2

end Alpoge
