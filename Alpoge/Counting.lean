import Alpoge.Basic

/-!
# Exact fiber statistics over finite fields: the algebraic core

Phase 1 of the finite-field counting theorem.  Everything here is a
certificate-level statement about roots of the fiber cubic over an arbitrary
field with `2 ≠ 0`; the `𝔽_q` counting layer builds on it.

* `vieta_of_three_roots` — three distinct finite roots force the Vieta
  relations, in particular `c·(t₁+t₂+t₃) = 2`;
* `sum_ne_zero_of_three_roots` — hence the root sum cannot vanish: the
  "forbidden" sum-zero triples support no target at all;
* `target_unique_of_three_roots`, `target_unique_of_two_roots_and_inf` —
  a target is determined by three distinct projective roots;
* `exists_target_of_three_roots`, `exists_target_of_two_roots_and_inf` —
  every admissible distinct triple of projective points is the simple-root
  set of an explicit target;
* `ncard_fiber_eq_card_simpleRoots` — the fiber cardinality equals the
  number of simple projective roots, as a `Finset` count.
-/

namespace Alpoge

variable {K : Type*} [Field K]

section VietaCore

/-- **Vieta from three distinct roots.**  If `t₁, t₂, t₃` are pairwise
distinct roots of the fiber cubic of `(a, b, c)`, the three Vieta relations
hold — in particular `c` times the root sum equals `2`. -/
theorem vieta_of_three_roots {a b c t₁ t₂ t₃ : K}
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (H1 : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0)
    (H2 : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0)
    (H3 : c * t₃ ^ 3 - 2 * t₃ ^ 2 + b * t₃ - 2 * a = 0) :
    c * (t₁ + t₂ + t₃) = 2 ∧
      c * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) = b ∧
      c * (t₁ * t₂ * t₃) = 2 * a := by
  have hE12 : c * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) - 2 * (t₁ + t₂) + b = 0 := by
    have hm : (t₁ - t₂) *
        (c * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) - 2 * (t₁ + t₂) + b) = 0 := by
      linear_combination H1 - H2
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h12)
  have hE13 : c * (t₁ ^ 2 + t₁ * t₃ + t₃ ^ 2) - 2 * (t₁ + t₃) + b = 0 := by
    have hm : (t₁ - t₃) *
        (c * (t₁ ^ 2 + t₁ * t₃ + t₃ ^ 2) - 2 * (t₁ + t₃) + b) = 0 := by
      linear_combination H1 - H3
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h13)
  have hsum : c * (t₁ + t₂ + t₃) = 2 := by
    have hm : (t₂ - t₃) * (c * (t₁ + t₂ + t₃) - 2) = 0 := by
      linear_combination hE12 - hE13
    have h0 := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h23)
    linear_combination h0
  have hpair : c * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) = b := by
    linear_combination -hE12 + (t₁ + t₂) * hsum
  have hprod : c * (t₁ * t₂ * t₃) = 2 * a := by
    linear_combination H1 - t₁ ^ 2 * hsum + t₁ * hpair
  exact ⟨hsum, hpair, hprod⟩

/-- The sum of three distinct finite roots of a fiber cubic can never vanish
(over a field with `2 ≠ 0`): the forbidden sum-zero triples support no
target. -/
theorem sum_ne_zero_of_three_roots [NeZero (2 : K)] {a b c t₁ t₂ t₃ : K}
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (H1 : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0)
    (H2 : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0)
    (H3 : c * t₃ ^ 3 - 2 * t₃ ^ 2 + b * t₃ - 2 * a = 0) :
    t₁ + t₂ + t₃ ≠ 0 := by
  intro hs
  obtain ⟨hsum, -, -⟩ := vieta_of_three_roots h12 h13 h23 H1 H2 H3
  rw [hs, mul_zero] at hsum
  exact two_ne_zero hsum.symm

/-- **Uniqueness, all-finite case.**  A target is determined by three
distinct finite roots of its fiber cubic. -/
theorem target_unique_of_three_roots [NeZero (2 : K)]
    {a b c a' b' c' t₁ t₂ t₃ : K}
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (H1 : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0)
    (H2 : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0)
    (H3 : c * t₃ ^ 3 - 2 * t₃ ^ 2 + b * t₃ - 2 * a = 0)
    (H1' : c' * t₁ ^ 3 - 2 * t₁ ^ 2 + b' * t₁ - 2 * a' = 0)
    (H2' : c' * t₂ ^ 3 - 2 * t₂ ^ 2 + b' * t₂ - 2 * a' = 0)
    (H3' : c' * t₃ ^ 3 - 2 * t₃ ^ 2 + b' * t₃ - 2 * a' = 0) :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨hsum, hpair, hprod⟩ := vieta_of_three_roots h12 h13 h23 H1 H2 H3
  obtain ⟨hsum', hpair', hprod'⟩ := vieta_of_three_roots h12 h13 h23 H1' H2' H3'
  have hs : t₁ + t₂ + t₃ ≠ 0 :=
    sum_ne_zero_of_three_roots h12 h13 h23 H1 H2 H3
  have hc : c = c' := by
    have hm : (c - c') * (t₁ + t₂ + t₃) = 0 := by
      linear_combination hsum - hsum'
    have := (mul_eq_zero.mp hm).resolve_right hs
    linear_combination this
  subst hc
  have hb : b = b' := by linear_combination -hpair + hpair'
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have ha : a = a' := by
    have hm : 2 * (a - a') = 0 := by linear_combination hprod' - hprod
    have := (mul_eq_zero.mp hm).resolve_left h2
    linear_combination this
  exact ⟨ha, hb, rfl⟩

/-- **Uniqueness, root-at-infinity case.**  A target is determined by the
root at infinity (`c = 0`) together with two distinct finite roots. -/
theorem target_unique_of_two_roots_and_inf [NeZero (2 : K)]
    {a b a' b' t₁ t₂ : K} (h12 : t₁ ≠ t₂)
    (H1 : -2 * t₁ ^ 2 + b * t₁ - 2 * a = 0)
    (H2 : -2 * t₂ ^ 2 + b * t₂ - 2 * a = 0)
    (H1' : -2 * t₁ ^ 2 + b' * t₁ - 2 * a' = 0)
    (H2' : -2 * t₂ ^ 2 + b' * t₂ - 2 * a' = 0) :
    a = a' ∧ b = b' := by
  have hb : b = b' := by
    have hm : (t₁ - t₂) * (b - b') = 0 := by
      linear_combination H1 - H2 - H1' + H2'
    have := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr h12)
    linear_combination this
  subst hb
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have ha : a = a' := by
    have hm : 2 * (a - a') = 0 := by linear_combination H1' - H1
    have := (mul_eq_zero.mp hm).resolve_left h2
    linear_combination this
  exact ⟨ha, rfl⟩

/-- **Existence, all-finite case.**  Three distinct finite points with
nonvanishing sum are the simple-root set of an explicit target:
`(e₃/s, 2e₂/s, 2/s)` where `s, e₂, e₃` are the elementary symmetric
functions. -/
theorem exists_target_of_three_roots [NeZero (2 : K)] {t₁ t₂ t₃ : K}
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (hs : t₁ + t₂ + t₃ ≠ 0) :
    ∃ a b c : K,
      projectiveSimpleRoot a b c (some t₁) ∧
      projectiveSimpleRoot a b c (some t₂) ∧
      projectiveSimpleRoot a b c (some t₃) := by
  set s : K := t₁ + t₂ + t₃ with hs_def
  refine ⟨t₁ * t₂ * t₃ / s, 2 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) / s, 2 / s,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · field_simp
    ring
  · have : 3 * (2 / s) * t₁ ^ 2 - 4 * t₁ +
        2 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) / s =
        (2 / s) * (t₁ - t₂) * (t₁ - t₃) := by
      field_simp
      ring
    rw [this]
    exact mul_ne_zero
      (mul_ne_zero (div_ne_zero two_ne_zero hs) (sub_ne_zero.mpr h12))
      (sub_ne_zero.mpr h13)
  · field_simp
    ring
  · have : 3 * (2 / s) * t₂ ^ 2 - 4 * t₂ +
        2 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) / s =
        (2 / s) * (t₂ - t₁) * (t₂ - t₃) := by
      field_simp
      ring
    rw [this]
    exact mul_ne_zero
      (mul_ne_zero (div_ne_zero two_ne_zero hs)
        (sub_ne_zero.mpr h12.symm))
      (sub_ne_zero.mpr h23)
  · field_simp
    ring
  · have : 3 * (2 / s) * t₃ ^ 2 - 4 * t₃ +
        2 * (t₁ * t₂ + t₁ * t₃ + t₂ * t₃) / s =
        (2 / s) * (t₃ - t₁) * (t₃ - t₂) := by
      field_simp
      ring
    rw [this]
    exact mul_ne_zero
      (mul_ne_zero (div_ne_zero two_ne_zero hs)
        (sub_ne_zero.mpr h13.symm))
      (sub_ne_zero.mpr h23.symm)

/-- **Existence, root-at-infinity case.**  The point at infinity together
with two distinct finite points is the simple-root set of the explicit
target `(t₁t₂, 2(t₁+t₂), 0)`. -/
theorem exists_target_of_two_roots_and_inf [NeZero (2 : K)] {t₁ t₂ : K}
    (h12 : t₁ ≠ t₂) :
    ∃ a b : K,
      projectiveSimpleRoot a b (0 : K) none ∧
      projectiveSimpleRoot a b (0 : K) (some t₁) ∧
      projectiveSimpleRoot a b (0 : K) (some t₂) := by
  refine ⟨t₁ * t₂, 2 * (t₁ + t₂), rfl, ⟨by ring, ?_⟩, ⟨by ring, ?_⟩⟩
  · have : 3 * (0 : K) * t₁ ^ 2 - 4 * t₁ + 2 * (t₁ + t₂) =
        2 * (t₂ - t₁) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr h12.symm)
  · have : 3 * (0 : K) * t₂ ^ 2 - 4 * t₂ + 2 * (t₁ + t₂) =
        2 * (t₁ - t₂) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr h12)

end VietaCore

section RootCount

/-- Decidability of the simple-root predicate over a `DecidableEq` field. -/
instance decidableProjectiveSimpleRoot [DecidableEq K] (a b c : K) :
    DecidablePred (projectiveSimpleRoot a b c)
  | none => decidable_of_iff (c = 0) Iff.rfl
  | some t =>
      decidable_of_iff
        (c * t ^ 3 - 2 * t ^ 2 + b * t - 2 * a = 0 ∧
          3 * c * t ^ 2 - 4 * t + b ≠ 0) Iff.rfl

variable [Fintype K] [DecidableEq K] [NeZero (2 : K)]

/-- The simple projective roots of a target, as a `Finset`. -/
def simpleRootFinset (a b c : K) : Finset (Option K) :=
  Finset.univ.filter (projectiveSimpleRoot a b c ·)

omit [NeZero (2 : K)] in
theorem mem_simpleRootFinset {a b c : K} {r : Option K} :
    r ∈ simpleRootFinset a b c ↔ projectiveSimpleRoot a b c r := by
  simp [simpleRootFinset]

/-- **The bridge**: the rational fiber count equals the number of simple
projective roots, as a `Finset` cardinality. -/
theorem ncard_fiber_eq_card_simpleRoots (a b c : K) :
    Set.ncard {p : K × K × K | F K p = (a, b, c)} =
      (simpleRootFinset a b c).card := by
  rw [← Nat.card_coe_set_eq]
  have e : {p : K × K × K | F K p = (a, b, c)} ≃
      {r : Option K // r ∈ simpleRootFinset a b c} :=
    (fiberEquivSimpleRootsProj (K := K) (a := a) (b := b) (c := c)).trans
      (Equiv.subtypeEquivRight fun r => mem_simpleRootFinset.symm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

/-- The number of simple projective roots is `0`, `1`, or `3`. -/
theorem card_simpleRootFinset_mem (a b c : K) :
    (simpleRootFinset a b c).card ∈ ({0, 1, 3} : Set ℕ) := by
  rw [← ncard_fiber_eq_card_simpleRoots]
  exact fiber_ncard_mem_zero_one_three a b c

end RootCount

section TripleCount

/-! ### Counting distinct ordered triples

One general fact powers both sides of the double count: ordered pairwise-
distinct triples in a fintype `α` are exactly the embeddings `Fin 3 ↪ α`,
so there are `|α|·(|α|−1)·(|α|−2)` of them. -/

variable {α : Type*} [DecidableEq α]

/-- Ordered pairwise-distinct triples are embeddings of `Fin 3`. -/
def distinctTripleEquivEmbedding :
    {r : α × α × α // r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2} ≃
      (Fin 3 ↪ α) where
  toFun x := ⟨![x.1.1, x.1.2.1, x.1.2.2], by
    obtain ⟨⟨a, b, c⟩, h1, h2, h3⟩ := x
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij h1
        | exact absurd hij h2
        | exact absurd hij h3
        | exact absurd hij.symm h1
        | exact absurd hij.symm h2
        | exact absurd hij.symm h3⟩
  invFun e := ⟨(e 0, e 1, e 2),
    fun h => absurd (e.injective h) (by decide),
    fun h => absurd (e.injective h) (by decide),
    fun h => absurd (e.injective h) (by decide)⟩
  left_inv x := rfl
  right_inv e := by
    ext i
    fin_cases i <;> rfl

/-- The number of ordered pairwise-distinct triples in a fintype. -/
theorem card_filter_distinctTriple (α : Type*) [Fintype α] [DecidableEq α] :
    (Finset.univ.filter fun r : α × α × α =>
        r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2).card =
      (Fintype.card α).descFactorial 3 := by
  rw [← Fintype.card_subtype,
    Fintype.card_congr distinctTripleEquivEmbedding,
    Fintype.card_embedding_eq, Fintype.card_fin]

end TripleCount

section DoubleCount

variable [Fintype K] [DecidableEq K] [NeZero (2 : K)]

/-- Ordered triples of projective points. -/
abbrev Triple (K : Type*) := Option K × Option K × Option K

/-- Pairwise distinctness of a triple. -/
def IsDistinct (r : Triple K) : Prop :=
  r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2

instance : DecidablePred (IsDistinct (K := K)) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- All three entries are simple projective roots of the target. -/
def IsRootTriple (v : K × K × K) (r : Triple K) : Prop :=
  projectiveSimpleRoot v.1 v.2.1 v.2.2 r.1 ∧
  projectiveSimpleRoot v.1 v.2.1 v.2.2 r.2.1 ∧
  projectiveSimpleRoot v.1 v.2.1 v.2.2 r.2.2

instance (v : K × K × K) : DecidablePred (IsRootTriple v) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Triples of affine (finite) points summing to zero — inadmissible
because the slice normalization forces `c·(t₁+t₂+t₃) = 2`. -/
def HasZeroAffineSum : Triple K → Prop
  | (some t₁, some t₂, some t₃) => t₁ + t₂ + t₃ = 0
  | _ => False

instance : DecidablePred (HasZeroAffineSum (K := K))
  | (some _, some _, some _) => inferInstanceAs (Decidable (_ = _))
  | (none, _, _) => .isFalse fun h => h
  | (some _, none, _) => .isFalse fun h => h
  | (some _, some _, none) => .isFalse fun h => h

/-- Distinct root triples of a fixed target. -/
def rootTriples (v : K × K × K) : Finset (Triple K) :=
  Finset.univ.filter fun r => IsDistinct r ∧ IsRootTriple v r

/-- Attaching membership proofs: triples with entries in `s` are triples of
`↥s`. -/
def memTripleEquiv {β : Type*} (s : Finset β) :
    {r : β × β × β // (r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2) ∧
      r.1 ∈ s ∧ r.2.1 ∈ s ∧ r.2.2 ∈ s} ≃
    {r : ↥s × ↥s × ↥s // r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2} where
  toFun x := ⟨(⟨x.1.1, x.2.2.1⟩, ⟨x.1.2.1, x.2.2.2.1⟩, ⟨x.1.2.2, x.2.2.2.2⟩),
    fun h => x.2.1.1 (congrArg Subtype.val h),
    fun h => x.2.1.2.1 (congrArg Subtype.val h),
    fun h => x.2.1.2.2 (congrArg Subtype.val h)⟩
  invFun y := ⟨(y.1.1.1, y.1.2.1.1, y.1.2.2.1),
    ⟨fun h => y.2.1 (Subtype.ext h),
     fun h => y.2.2.1 (Subtype.ext h),
     fun h => y.2.2.2 (Subtype.ext h)⟩,
    y.1.1.2, y.1.2.1.2, y.1.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [NeZero (2 : K)] in
/-- The count of distinct root triples is the descending factorial of the
simple-root count. -/
theorem card_rootTriples (v : K × K × K) :
    (rootTriples v).card =
      ((simpleRootFinset v.1 v.2.1 v.2.2).card).descFactorial 3 := by
  have hfilter : rootTriples v =
      Finset.univ.filter fun r : Triple K =>
        (r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2) ∧
        r.1 ∈ simpleRootFinset v.1 v.2.1 v.2.2 ∧
        r.2.1 ∈ simpleRootFinset v.1 v.2.1 v.2.2 ∧
        r.2.2 ∈ simpleRootFinset v.1 v.2.1 v.2.2 := by
    apply Finset.filter_congr
    intro r _
    simp only [IsDistinct, IsRootTriple, mem_simpleRootFinset]
  rw [hfilter, ← Fintype.card_subtype,
    Fintype.card_congr (memTripleEquiv _),
    Fintype.card_subtype, card_filter_distinctTriple, Fintype.card_coe]

/-- The incidence set: pairs (target, distinct triple of its simple roots). -/
def incidencePairs : Finset ((K × K × K) × Triple K) :=
  Finset.univ.filter fun x => IsDistinct x.2 ∧ IsRootTriple x.1 x.2

/-- Left fiberwise count: over each target, the distinct root triples. -/
theorem card_incidencePairs_left :
    (incidencePairs (K := K)).card = ∑ v : K × K × K, (rootTriples v).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Finset.univ) (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.card_bij' (fun x _ => x.2) (fun r _ => (v, r)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [incidencePairs, Finset.mem_filter, Finset.mem_univ, true_and]
      at hx
    obtain ⟨⟨hd, hr⟩, hv⟩ := hx
    simp only [rootTriples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hd, hv ▸ hr⟩
  · intro r hr
    simp only [rootTriples, Finset.mem_filter, Finset.mem_univ, true_and]
      at hr
    simp only [incidencePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, by trivial⟩
  · intro x hx
    simp only [incidencePairs, Finset.mem_filter, Finset.mem_univ, true_and]
      at hx
    exact Prod.ext hx.2.symm rfl
  · intro r _
    rfl

private theorem psr_some {A B C t : K}
    (h : projectiveSimpleRoot A B C (some t)) :
    C * t ^ 3 - 2 * t ^ 2 + B * t - 2 * A = 0 ∧
      3 * C * t ^ 2 - 4 * t + B ≠ 0 := h

private theorem psr_none {A B C : K}
    (h : projectiveSimpleRoot A B C none) : C = 0 := h

/-- **The per-triple target count.**  A distinct non-forbidden triple is the
simple-root triple of exactly one target; zero-sum or non-distinct triples
support no target. -/
theorem card_targets_of_triple (r : Triple K) :
    (Finset.univ.filter fun v : K × K × K =>
        IsDistinct r ∧ IsRootTriple v r).card =
      if IsDistinct r ∧ ¬ HasZeroAffineSum r then 1 else 0 := by
  by_cases hd : IsDistinct r
  · obtain ⟨r₁, r₂, r₃⟩ := r
    by_cases hf : HasZeroAffineSum ((r₁, r₂, r₃) : Triple K)
    · -- forbidden: no targets
      rw [if_neg (fun h => h.2 hf), Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro v _
      rintro ⟨-, hv1, hv2, hv3⟩
      match r₁, r₂, r₃, hd, hf, hv1, hv2, hv3 with
      | some t₁, some t₂, some t₃, hd, hf, hv1, hv2, hv3 =>
        have h12 : t₁ ≠ t₂ := fun h => hd.1 (congrArg some h)
        have h13 : t₁ ≠ t₃ := fun h => hd.2.1 (congrArg some h)
        have h23 : t₂ ≠ t₃ := fun h => hd.2.2 (congrArg some h)
        exact sum_ne_zero_of_three_roots h12 h13 h23
          (psr_some hv1).1 (psr_some hv2).1 (psr_some hv3).1 hf
    · -- distinct and admissible: exactly one target
      rw [if_pos ⟨hd, hf⟩, Finset.card_eq_one]
      match r₁, r₂, r₃, hd, hf with
      | none, none, _, hd, _ => exact absurd rfl hd.1
      | none, some _, none, hd, _ => exact absurd rfl hd.2.1
      | some _, none, none, hd, _ => exact absurd rfl hd.2.2
      | none, some t₁, some t₂, hd, _ =>
        have h12 : t₁ ≠ t₂ := fun h => hd.2.2 (congrArg some h)
        obtain ⟨a, b, hn, h1, h2⟩ := exists_target_of_two_roots_and_inf
          (K := K) h12
        refine ⟨(a, b, 0), Finset.eq_singleton_iff_unique_mem.mpr
          ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hd, hn, h1, h2⟩
        · rintro ⟨a', b', c'⟩ hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          obtain ⟨-, hn', h1', h2'⟩ := hv
          have hc' : c' = 0 := psr_none hn'
          subst hc'
          have H1' : -2 * t₁ ^ 2 + b' * t₁ - 2 * a' = 0 := by
            linear_combination (psr_some h1').1
          have H2' : -2 * t₂ ^ 2 + b' * t₂ - 2 * a' = 0 := by
            linear_combination (psr_some h2').1
          have H1 : -2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by
            linear_combination (psr_some h1).1
          have H2 : -2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 := by
            linear_combination (psr_some h2).1
          obtain ⟨ha, hb⟩ :=
            target_unique_of_two_roots_and_inf h12 H1' H2' H1 H2
          exact Prod.ext ha (Prod.ext hb rfl)
      | some t₁, none, some t₂, hd, _ =>
        have h12 : t₁ ≠ t₂ := fun h => hd.2.1 (congrArg some h)
        obtain ⟨a, b, hn, h1, h2⟩ := exists_target_of_two_roots_and_inf
          (K := K) h12
        refine ⟨(a, b, 0), Finset.eq_singleton_iff_unique_mem.mpr
          ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hd, h1, hn, h2⟩
        · rintro ⟨a', b', c'⟩ hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          obtain ⟨-, h1', hn', h2'⟩ := hv
          have hc' : c' = 0 := psr_none hn'
          subst hc'
          have H1' : -2 * t₁ ^ 2 + b' * t₁ - 2 * a' = 0 := by
            linear_combination (psr_some h1').1
          have H2' : -2 * t₂ ^ 2 + b' * t₂ - 2 * a' = 0 := by
            linear_combination (psr_some h2').1
          have H1 : -2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by
            linear_combination (psr_some h1).1
          have H2 : -2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 := by
            linear_combination (psr_some h2).1
          obtain ⟨ha, hb⟩ :=
            target_unique_of_two_roots_and_inf h12 H1' H2' H1 H2
          exact Prod.ext ha (Prod.ext hb rfl)
      | some t₁, some t₂, none, hd, _ =>
        have h12 : t₁ ≠ t₂ := fun h => hd.1 (congrArg some h)
        obtain ⟨a, b, hn, h1, h2⟩ := exists_target_of_two_roots_and_inf
          (K := K) h12
        refine ⟨(a, b, 0), Finset.eq_singleton_iff_unique_mem.mpr
          ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hd, h1, h2, hn⟩
        · rintro ⟨a', b', c'⟩ hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          obtain ⟨-, h1', h2', hn'⟩ := hv
          have hc' : c' = 0 := psr_none hn'
          subst hc'
          have H1' : -2 * t₁ ^ 2 + b' * t₁ - 2 * a' = 0 := by
            linear_combination (psr_some h1').1
          have H2' : -2 * t₂ ^ 2 + b' * t₂ - 2 * a' = 0 := by
            linear_combination (psr_some h2').1
          have H1 : -2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by
            linear_combination (psr_some h1).1
          have H2 : -2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 := by
            linear_combination (psr_some h2).1
          obtain ⟨ha, hb⟩ :=
            target_unique_of_two_roots_and_inf h12 H1' H2' H1 H2
          exact Prod.ext ha (Prod.ext hb rfl)
      | some t₁, some t₂, some t₃, hd, hf =>
        have h12 : t₁ ≠ t₂ := fun h => hd.1 (congrArg some h)
        have h13 : t₁ ≠ t₃ := fun h => hd.2.1 (congrArg some h)
        have h23 : t₂ ≠ t₃ := fun h => hd.2.2 (congrArg some h)
        have hs : t₁ + t₂ + t₃ ≠ 0 := hf
        obtain ⟨a, b, c, h1, h2, h3⟩ := exists_target_of_three_roots
          (K := K) h12 h13 h23 hs
        refine ⟨(a, b, c), Finset.eq_singleton_iff_unique_mem.mpr
          ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hd, h1, h2, h3⟩
        · rintro ⟨a', b', c'⟩ hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          obtain ⟨-, h1', h2', h3'⟩ := hv
          obtain ⟨ha, hb, hc⟩ := target_unique_of_three_roots h12 h13 h23
            (psr_some h1').1 (psr_some h2').1 (psr_some h3').1
            (psr_some h1).1 (psr_some h2).1 (psr_some h3).1
          exact Prod.ext ha (Prod.ext hb hc)
  · simp [hd]

/-- Right fiberwise count: the incidence pairs are counted by admissible
distinct triples. -/
theorem card_incidencePairs_right :
    (incidencePairs (K := K)).card =
      (Finset.univ.filter fun r : Triple K =>
        IsDistinct r ∧ ¬ HasZeroAffineSum r).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.snd) (t := Finset.univ) (fun x _ => Finset.mem_univ _),
    Finset.card_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← card_targets_of_triple r]
  refine Finset.card_bij' (fun x _ => x.1) (fun v _ => (v, r)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [incidencePairs, Finset.mem_filter, Finset.mem_univ, true_and]
      at hx
    obtain ⟨⟨hdx, hrx⟩, hr⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr ▸ hdx, hr ▸ hrx⟩
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [incidencePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hv.1, hv.2⟩, by trivial⟩
  · intro x hx
    simp only [incidencePairs, Finset.mem_filter, Finset.mem_univ, true_and]
      at hx
    exact Prod.ext rfl hx.2.symm
  · intro v _
    rfl

/-! ### The combinatorial counts -/

/-- A field with `2 ≠ 0` has at least three elements. -/
theorem three_le_card : 3 ≤ Fintype.card K := by
  by_contra hlt
  push_neg at hlt
  have h2le : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hcard : Fintype.card K = 2 := by omega
  have hc01 : ({0, 1} : Finset K).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  have huniv : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, hcard, hc01])
  have hmem : (2 : K) ∈ ({0, 1} : Finset K) := huniv ▸ Finset.mem_univ _
  rcases Finset.mem_insert.mp hmem with h | h
  · exact two_ne_zero h
  · rw [Finset.mem_singleton] at h
    exact one_ne_zero (α := K) (by linear_combination h)

omit [NeZero (2 : K)] in
/-- The distinct-triple count over the projective line. -/
theorem card_distinct_triples :
    (Finset.univ.filter (IsDistinct (K := K))).card =
      (Fintype.card K + 1).descFactorial 3 := by
  rw [show (Finset.univ.filter (IsDistinct (K := K))) =
      Finset.univ.filter (fun r : Triple K =>
        r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2) from
    Finset.filter_congr fun r _ => Iff.rfl]
  rw [card_filter_distinctTriple, Fintype.card_option]

/-- The allowed second coordinates of a sum-zero pair, as a complement. -/
theorem pair_filter_eq_compl (t : K) :
    (Finset.univ.filter fun y : K =>
        y ≠ t ∧ 2 * t + y ≠ 0 ∧ t + 2 * y ≠ 0) =
      ({t, -2 * t, -(2⁻¹) * t} : Finset K)ᶜ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2', h3⟩ (h | h | h)
    · exact h1 h
    · exact h2' (by rw [h]; ring)
    · refine h3 ?_
      rw [h, show (2 : K) * (-(2⁻¹) * t) = -t from by field_simp]
      ring
  · intro h
    push_neg at h
    obtain ⟨h1, h2', h3⟩ := h
    refine ⟨h1, fun h0 => h2' (by linear_combination h0),
      fun h0 => h3 ?_⟩
    apply mul_left_cancel₀ h2
    have hval : (2 : K) * (-(2⁻¹) * t) = -t := by field_simp
    rw [hval]
    linear_combination h0

/-- The cardinality of the excluded set `{t, −2t, −t/2}`. -/
theorem card_excluded (t : K) :
    ({t, -2 * t, -(2⁻¹) * t} : Finset K).card =
      if (3 : K) = 0 then 1 else if t = 0 then 1 else 3 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  by_cases h3 : (3 : K) = 0
  · rw [if_pos h3]
    have e1 : (-2 * t : K) = t := by linear_combination -t * h3
    have e2 : (-(2⁻¹) * t : K) = t := by
      apply mul_left_cancel₀ h2
      have hval : (2 : K) * (-(2⁻¹) * t) = -t := by field_simp
      rw [hval]
      linear_combination -t * h3
    rw [e1, e2]
    simp
  · rw [if_neg h3]
    have h3ne : ∀ x : K, 3 * x = 0 → x = 0 := fun x hx =>
      (mul_eq_zero.mp hx).resolve_left h3
    by_cases ht : t = 0
    · subst ht
      simp
    · rw [if_neg ht]
      have hval : (2 : K) * (-(2⁻¹) * t) = -t := by field_simp
      have d1 : t ≠ -2 * t := fun h =>
        ht (h3ne t (by linear_combination h))
      have d2 : t ≠ -(2⁻¹) * t := by
        intro h
        apply ht
        apply h3ne
        have h' : (2 : K) * t = 2 * (-(2⁻¹) * t) := congrArg (2 * ·) h
        rw [hval] at h'
        linear_combination h'
      have d3 : (-2 * t : K) ≠ -(2⁻¹) * t := by
        intro h
        apply ht
        apply h3ne
        have h' : (2 : K) * (-2 * t) = 2 * (-(2⁻¹) * t) := congrArg (2 * ·) h
        rw [hval] at h'
        linear_combination -h'
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h)
          · exact d1 h
          · exact d2 h),
        Finset.card_insert_of_notMem
          (by simpa using d3),
        Finset.card_singleton]

/-- The sum-zero pair count. -/
theorem card_forbidden_pairs :
    (Finset.univ.filter fun p : K × K =>
        p.2 ≠ p.1 ∧ 2 * p.1 + p.2 ≠ 0 ∧ p.1 + 2 * p.2 ≠ 0).card =
      if (3 : K) = 0 then Fintype.card K * (Fintype.card K - 1)
      else (Fintype.card K - 1) * (Fintype.card K - 2) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Finset.univ) (fun x _ => Finset.mem_univ _)]
  have hfib : ∀ t : K,
      ((Finset.univ.filter fun p : K × K =>
        p.2 ≠ p.1 ∧ 2 * p.1 + p.2 ≠ 0 ∧ p.1 + 2 * p.2 ≠ 0).filter
          fun p => p.1 = t).card =
      Fintype.card K - (if (3 : K) = 0 then 1 else if t = 0 then 1 else 3) := by
    intro t
    have hbij : ((Finset.univ.filter fun p : K × K =>
        p.2 ≠ p.1 ∧ 2 * p.1 + p.2 ≠ 0 ∧ p.1 + 2 * p.2 ≠ 0).filter
          fun p => p.1 = t).card =
        (Finset.univ.filter fun y : K =>
          y ≠ t ∧ 2 * t + y ≠ 0 ∧ t + 2 * y ≠ 0).card := by
      refine Finset.card_bij' (fun p _ => p.2) (fun y _ => (t, y)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨h1, h2, h3⟩, ht⟩ := hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ht ▸ h1, ht ▸ h2, ht ▸ h3⟩
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hy.1, hy.2.1, hy.2.2⟩, by trivial⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact Prod.ext hp.2.symm rfl
      · intro y _
        rfl
    rw [hbij, pair_filter_eq_compl, Finset.card_compl, card_excluded]
  rw [Finset.sum_congr rfl fun t _ => hfib t]
  by_cases h3 : (3 : K) = 0
  · simp only [if_pos h3, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  · simp only [if_neg h3]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : K)), if_pos rfl]
    have hrest : ∀ t ∈ Finset.univ.erase (0 : K),
        Fintype.card K - (if t = 0 then 1 else 3) = Fintype.card K - 3 := by
      intro t ht
      rw [if_neg (Finset.mem_erase.mp ht).1]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, smul_eq_mul]
    have hq := three_le_card (K := K)
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card K = m + 3 := ⟨Fintype.card K - 3, by omega⟩
    rw [hm]
    have e1 : m + 3 - 1 = m + 2 := by omega
    have e2 : m + 3 - 3 = m := by omega
    have e3 : m + 3 - 2 = m + 1 := by omega
    rw [e1, e2, e3]
    ring

/-- Forbidden distinct triples biject with sum-zero pairs. -/
theorem card_forbidden_triples :
    (Finset.univ.filter fun r : Triple K =>
        IsDistinct r ∧ HasZeroAffineSum r).card =
      (Finset.univ.filter fun p : K × K =>
        p.2 ≠ p.1 ∧ 2 * p.1 + p.2 ≠ 0 ∧ p.1 + 2 * p.2 ≠ 0).card := by
  refine Finset.card_bij' (fun r _ => (r.1.getD 0, r.2.1.getD 0))
    (fun p _ => (some p.1, some p.2, some (-p.1 - p.2))) ?_ ?_ ?_ ?_
  · rintro ⟨r₁, r₂, r₃⟩ hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨hd, hf⟩ := hr
    match r₁, r₂, r₃, hd, hf with
    | some t₁, some t₂, some t₃, hd, hf =>
      have hfe : t₁ + t₂ + t₃ = 0 := hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.getD_some]
      refine ⟨fun h => hd.1 (congrArg some h.symm), fun h0 => ?_, fun h0 => ?_⟩
      · exact hd.2.1 (congrArg some (by linear_combination h0 - hfe))
      · exact hd.2.2 (congrArg some (by linear_combination h0 - hfe))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun h => h1 (Option.some_injective K h).symm,
      fun h => h2 ?_, fun h => h3 ?_⟩, ?_⟩
    · have := Option.some_injective K h
      linear_combination this
    · have := Option.some_injective K h
      linear_combination this
    · show p.1 + p.2 + (-p.1 - p.2) = 0
      ring
  · rintro ⟨r₁, r₂, r₃⟩ hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨hd, hf⟩ := hr
    match r₁, r₂, r₃, hd, hf with
    | some t₁, some t₂, some t₃, hd, hf =>
      have hfe : t₁ + t₂ + t₃ = 0 := hf
      simp only [Option.getD_some]
      refine Prod.ext rfl (Prod.ext rfl (congrArg some ?_))
      linear_combination -hfe
  · intro p _
    rfl

/-! ### The exact statistics -/

/-- The number of targets whose rational fiber has exactly `j` points. -/
def targetCount (j : ℕ) : ℕ :=
  (Finset.univ.filter fun v : K × K × K =>
    (Finset.univ.filter fun p : K × K × K => F K p = v).card = j).card

/-- The fiber filter counts simple roots. -/
theorem fiber_filter_card (v : K × K × K) :
    (Finset.univ.filter fun p : K × K × K => F K p = v).card =
      (simpleRootFinset v.1 v.2.1 v.2.2).card := by
  have h := ncard_fiber_eq_card_simpleRoots v.1 v.2.1 v.2.2
  have hset : {p : K × K × K | F K p = (v.1, v.2.1, v.2.2)} =
      ↑(Finset.univ.filter fun p : K × K × K => F K p = v) := by
    ext p
    simp
  rw [hset, Set.ncard_coe_finset] at h
  exact h

/-- The incidence count is six times the number of three-point fibers. -/
theorem card_incidencePairs_eq :
    (incidencePairs (K := K)).card = 6 * targetCount (K := K) 3 := by
  rw [card_incidencePairs_left]
  have key : ∀ v : K × K × K, (rootTriples v).card =
      if (Finset.univ.filter fun p : K × K × K => F K p = v).card = 3
      then 6 else 0 := by
    intro v
    rw [card_rootTriples, ← fiber_filter_card]
    have h := card_simpleRootFinset_mem v.1 v.2.1 v.2.2
    rw [← fiber_filter_card] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;> rw [h] <;> decide
  rw [Finset.sum_congr rfl fun v _ => key v, Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul,
    mul_comm]
  rfl

omit [NeZero (2 : K)] in
/-- Source points partition into fibers. -/
theorem sum_fiber_filter_cards :
    ∑ v : K × K × K,
      (Finset.univ.filter fun p : K × K × K => F K p = v).card =
      Fintype.card K ^ 3 := by
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun p => F K p) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod]
  ring

/-- One- and three-point fibers exhaust the source. -/
theorem targetCount_one_add_three :
    targetCount (K := K) 1 + 3 * targetCount (K := K) 3 =
      Fintype.card K ^ 3 := by
  rw [← sum_fiber_filter_cards]
  have key : ∀ v : K × K × K,
      (Finset.univ.filter fun p : K × K × K => F K p = v).card =
        (if (Finset.univ.filter fun p : K × K × K => F K p = v).card = 1
          then 1 else 0) +
        3 * (if (Finset.univ.filter fun p : K × K × K => F K p = v).card = 3
          then 1 else 0) := by
    intro v
    have h := card_simpleRootFinset_mem v.1 v.2.1 v.2.2
    rw [← fiber_filter_card] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;> rw [h] <;> decide
  rw [Finset.sum_congr rfl fun v _ => key v, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter]
  rfl

/-- All targets have zero, one, or three preimages. -/
theorem targetCount_partition :
    targetCount (K := K) 0 + targetCount (K := K) 1 +
      targetCount (K := K) 3 = Fintype.card K ^ 3 := by
  have key : ∀ v : K × K × K, (1 : ℕ) =
      (if (Finset.univ.filter fun p : K × K × K => F K p = v).card = 0
        then 1 else 0) +
      ((if (Finset.univ.filter fun p : K × K × K => F K p = v).card = 1
        then 1 else 0) +
      (if (Finset.univ.filter fun p : K × K × K => F K p = v).card = 3
        then 1 else 0)) := by
    intro v
    have h := card_simpleRootFinset_mem v.1 v.2.1 v.2.2
    rw [← fiber_filter_card] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;> rw [h] <;> decide
  have htot : ∑ _v : K × K × K, (1 : ℕ) = Fintype.card K ^ 3 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
      Fintype.card_prod, Fintype.card_prod]
    ring
  rw [← htot, Finset.sum_congr rfl fun v _ => key v,
    Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter]
  rw [add_assoc]
  rfl

/-- **Exact three-point-fiber count over a finite field** (`2 ≠ 0`):
`6·N₃ = (q−1)(q²+2)` away from characteristic three, `6·N₃ = q²(q−1)` in
characteristic three. -/
theorem six_mul_targetCount_three :
    6 * targetCount (K := K) 3 =
      if (3 : K) = 0
      then Fintype.card K ^ 2 * (Fintype.card K - 1)
      else (Fintype.card K - 1) * (Fintype.card K ^ 2 + 2) := by
  have hadm := (card_incidencePairs_eq (K := K)).symm.trans
    card_incidencePairs_right
  have hsplit :
      (Finset.univ.filter fun r : Triple K =>
        IsDistinct r ∧ HasZeroAffineSum r).card +
      (Finset.univ.filter fun r : Triple K =>
        IsDistinct r ∧ ¬ HasZeroAffineSum r).card =
      (Finset.univ.filter (IsDistinct (K := K))).card := by
    rw [← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [← hadm, card_forbidden_triples, card_forbidden_pairs,
    card_distinct_triples] at hsplit
  have hq := three_le_card (K := K)
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card K = m + 3 :=
    ⟨Fintype.card K - 3, by omega⟩
  rw [hm] at hsplit ⊢
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have edf : (m + 3 + 1).descFactorial 3 =
      (m + 2) * (m + 3) * (m + 4) := by
    simp [Nat.descFactorial]
    ring
  rw [e1, e2, edf] at hsplit
  rw [e1]
  by_cases h3 : (3 : K) = 0
  · rw [if_pos h3] at hsplit ⊢
    have hkey : (m + 3) * (m + 2) + (m + 3) ^ 2 * (m + 2) =
        (m + 2) * (m + 3) * (m + 4) := by ring
    omega
  · rw [if_neg h3] at hsplit ⊢
    have hkey : (m + 2) * (m + 1) + (m + 2) * ((m + 3) ^ 2 + 2) =
        (m + 2) * (m + 3) * (m + 4) := by ring
    omega

/-- **Exact fiber statistics of the Alpöge map over every finite field with
`2 ≠ 0`.**  Writing `Nⱼ` for the number of targets with exactly `j` rational
preimages and `q` for the field size: every fiber has `0`, `1`, or `3`
points; `6N₃ = (q−1)(q²+2)` (or `q²(q−1)` in characteristic `3`);
`N₁ + 3N₃ = q³`; `N₀ + N₁ + N₃ = q³`; and consequently `N₀ = 2N₃`.  The
asymptotic fiber-size proportions `(1/2, 1/3, 1/6)` are the class
distribution of `S₃`. -/
theorem finiteField_fiber_statistics :
    (6 * targetCount (K := K) 3 =
      if (3 : K) = 0
      then Fintype.card K ^ 2 * (Fintype.card K - 1)
      else (Fintype.card K - 1) * (Fintype.card K ^ 2 + 2)) ∧
    targetCount (K := K) 1 + 3 * targetCount (K := K) 3 =
      Fintype.card K ^ 3 ∧
    targetCount (K := K) 0 + targetCount (K := K) 1 +
      targetCount (K := K) 3 = Fintype.card K ^ 3 ∧
    targetCount (K := K) 0 = 2 * targetCount (K := K) 3 :=
  ⟨six_mul_targetCount_three, targetCount_one_add_three,
    targetCount_partition, by
      have h1 := targetCount_one_add_three (K := K)
      have h2 := targetCount_partition (K := K)
      omega⟩

end DoubleCount

end Alpoge
