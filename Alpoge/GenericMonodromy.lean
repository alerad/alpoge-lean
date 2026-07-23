import Alpoge.GenericDiscriminant
import Alpoge.Counting

/-!
# Generic function-field monodromy

The normalized generic cubic has splitting-field automorphism group `S₃`.
This is a function-field Galois/monodromy statement; it does not formalize
topological fundamental groups or Frobenius specializations.
-/

namespace Alpoge

open MvPolynomial Polynomial

noncomputable section

variable (k : Type*) [Field k] [CharZero k]

abbrev GenericSplittingField :=
  (genericFiberPoly k).SplittingField

local instance genericFiberPoly_splitsFact :
    Fact
      ((genericFiberPoly k).map
        (algebraMap (GenericTargetField k) (GenericSplittingField k))).Splits :=
  ⟨Polynomial.SplittingField.splits _⟩

theorem genericRootSet_card :
    Fintype.card ((genericFiberPoly k).rootSet (GenericSplittingField k)) = 3 := by
  rw [Polynomial.card_rootSet_eq_natDegree
    (genericFiberPoly_separable k) (Polynomial.SplittingField.splits _)]
  exact genericFiberPoly_natDegree k

/-- An enumeration of the three roots of the generic cubic. -/
def genericRootEquiv :
    (genericFiberPoly k).rootSet (GenericSplittingField k) ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (genericRootSet_card k)

def genericRoot (i : Fin 3) : GenericSplittingField k :=
  ((genericRootEquiv k).symm i : _)

theorem genericRoot_ne {i j : Fin 3} (hij : i ≠ j) :
    genericRoot k i ≠ genericRoot k j := by
  intro h
  apply hij
  apply (genericRootEquiv k).symm.injective
  exact Subtype.ext h

theorem genericRoot_equation (i : Fin 3) :
    algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericC k) *
          genericRoot k i ^ 3 -
        2 * genericRoot k i ^ 2 +
        algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericB k) *
          genericRoot k i -
        2 * algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericA k) =
      0 := by
  have hr := ((genericRootEquiv k).symm i).property
  have haeval := (Polynomial.mem_rootSet.mp hr).2
  simp_rw [IsScalarTower.algebraMap_apply
    (GenericCoeffRing k) (GenericTargetField k) (GenericSplittingField k)]
  simpa [genericFiberPoly, genericFiberPolyRing, genericRoot, map_sub, map_add,
    map_mul, map_pow, map_ofNat, Polynomial.aeval_def] using haeval

/-- The Vandermonde square root of the generic discriminant in the splitting field. -/
def genericDelta : GenericSplittingField k :=
  let c := algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericC k)
  c ^ 2 *
    (genericRoot k 0 - genericRoot k 1) *
    (genericRoot k 0 - genericRoot k 2) *
    (genericRoot k 1 - genericRoot k 2)

theorem genericDelta_sq :
    genericDelta k ^ 2 =
      algebraMap (GenericTargetField k) (GenericSplittingField k)
        (genericFiberPoly k).discr := by
  let a := algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericA k)
  let b := algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericB k)
  let c := algebraMap (GenericCoeffRing k) (GenericSplittingField k) (genericC k)
  let t₀ := genericRoot k 0
  let t₁ := genericRoot k 1
  let t₂ := genericRoot k 2
  have h01 : t₀ ≠ t₁ := genericRoot_ne k (by decide)
  have h02 : t₀ ≠ t₂ := genericRoot_ne k (by decide)
  have h12 : t₁ ≠ t₂ := genericRoot_ne k (by decide)
  have H0 : c * t₀ ^ 3 - 2 * t₀ ^ 2 + b * t₀ - 2 * a = 0 := by
    exact genericRoot_equation k 0
  have H1 : c * t₁ ^ 3 - 2 * t₁ ^ 2 + b * t₁ - 2 * a = 0 := by
    exact genericRoot_equation k 1
  have H2 : c * t₂ ^ 3 - 2 * t₂ ^ 2 + b * t₂ - 2 * a = 0 := by
    exact genericRoot_equation k 2
  obtain ⟨hsum, hpair, hprod⟩ :=
    vieta_of_three_roots h01 h02 h12 H0 H1 H2
  have hsep := neg_four_mul_wallW_eq_sq_sep hsum hpair hprod
  calc
    genericDelta k ^ 2 =
        c ^ 4 * (t₀ - t₁) ^ 2 * (t₀ - t₂) ^ 2 * (t₁ - t₂) ^ 2 := by
      simp [genericDelta, c, t₀, t₁, t₂]
      ring
    _ = -4 * wallW a b c := hsep.symm
    _ = algebraMap (GenericTargetField k) (GenericSplittingField k)
          (genericFiberPoly k).discr := by
      rw [genericFiberPoly_discr]
      simp_rw [map_mul, map_neg, map_ofNat]
      simp [wallW, genericWallPoly, genericA, genericB, genericC, a, b, c,
        map_sub, map_add, map_mul, map_pow, map_ofNat]
      simp_rw [← IsScalarTower.algebraMap_apply
        (GenericCoeffRing k) (GenericTargetField k) (GenericSplittingField k)]

theorem genericDelta_not_mem_base :
    genericDelta k ∉
      (algebraMap (GenericTargetField k) (GenericSplittingField k)).range := by
  rintro ⟨x, hx⟩
  apply genericFiberPoly_discr_not_isSquare k
  refine ⟨x, ?_⟩
  apply (algebraMap (GenericTargetField k) (GenericSplittingField k)).injective
  rw [map_mul]
  calc
    algebraMap (GenericTargetField k) (GenericSplittingField k)
        (genericFiberPoly k).discr =
        genericDelta k ^ 2 := (genericDelta_sq k).symm
    _ = algebraMap (GenericTargetField k) (GenericSplittingField k) x *
          algebraMap (GenericTargetField k) (GenericSplittingField k) x := by
      rw [hx, pow_two]

theorem genericDelta_minpoly_natDegree :
    (minpoly (GenericTargetField k) (genericDelta k)).natDegree = 2 := by
  let d := (genericFiberPoly k).discr
  let q : Polynomial (GenericTargetField k) := Polynomial.X ^ 2 - Polynomial.C d
  have hδ : IsIntegral (GenericTargetField k) (genericDelta k) :=
    IsIntegral.of_finite _ _
  have hqeval : Polynomial.aeval (genericDelta k) q = 0 := by
    simp [q, d, genericDelta_sq]
  have hdvd : minpoly (GenericTargetField k) (genericDelta k) ∣ q :=
    minpoly.dvd _ _ hqeval
  have hqne : q ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [q] at this
  have hle :
      (minpoly (GenericTargetField k) (genericDelta k)).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hqne
    simpa [q] using this
  have hne1 :
      (minpoly (GenericTargetField k) (genericDelta k)).natDegree ≠ 1 := by
    intro hdeg
    have hminne : minpoly (GenericTargetField k) (genericDelta k) ≠ 0 :=
      minpoly.ne_zero hδ
    have hdegree :
        (minpoly (GenericTargetField k) (genericDelta k)).degree = 1 :=
      (Polynomial.degree_eq_iff_natDegree_eq hminne).mpr hdeg
    exact genericDelta_not_mem_base k
      (minpoly.degree_eq_one_iff.mp hdegree)
  have hpos :=
    minpoly.natDegree_pos hδ
  omega

theorem two_dvd_genericSplittingField_finrank :
    2 ∣ Module.finrank (GenericTargetField k) (GenericSplittingField k) := by
  have hδ : IsIntegral (GenericTargetField k) (genericDelta k) :=
    IsIntegral.of_finite _ _
  have hdvd :=
    (minpoly.irreducible hδ).natDegree_dvd_finrank
      (Normal.splits' (genericDelta k))
  rwa [genericDelta_minpoly_natDegree] at hdvd

theorem genericGal_card :
    Nat.card (genericFiberPoly k).Gal = 6 := by
  classical
  have h2 : 2 ∣ Nat.card (genericFiberPoly k).Gal := by
    rw [Polynomial.Gal.card_of_separable (genericFiberPoly_separable k)]
    exact two_dvd_genericSplittingField_finrank k
  have h3 : 3 ∣ Nat.card (genericFiberPoly k).Gal := by
    have h := Polynomial.Gal.prime_degree_dvd_card
      (genericFiberPoly_irreducible k) (by
        rw [genericFiberPoly_natDegree]
        norm_num)
    rwa [genericFiberPoly_natDegree] at h
  have h6 : 6 ∣ Nat.card (genericFiberPoly k).Gal := by
    exact (by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
  have hle : Nat.card (genericFiberPoly k).Gal ≤ 6 := by
    calc
      Nat.card (genericFiberPoly k).Gal ≤
          Nat.card (Equiv.Perm
            ((genericFiberPoly k).rootSet (GenericSplittingField k))) :=
        Nat.card_le_card_of_injective
          (Polynomial.Gal.galActionHom (genericFiberPoly k) (GenericSplittingField k))
          (Polynomial.Gal.galActionHom_injective
            (genericFiberPoly k) (GenericSplittingField k))
      _ = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, genericRootSet_card]
        norm_num
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h6)

/-- The faithful action on the three roots, with the roots numbered by `Fin 3`. -/
def genericGalActionHom :
    (genericFiberPoly k).Gal →* Equiv.Perm (Fin 3) :=
  by
    classical
    exact (Equiv.permCongrHom (genericRootEquiv k)).toMonoidHom.comp
      (Polynomial.Gal.galActionHom (genericFiberPoly k) (GenericSplittingField k))

theorem genericGalActionHom_injective :
    Function.Injective (genericGalActionHom k) := by
  classical
  exact (Equiv.permCongrHom (genericRootEquiv k)).injective.comp
    (Polynomial.Gal.galActionHom_injective
      (genericFiberPoly k) (GenericSplittingField k))

/-- **Generic monodromy is `S₃`.**  The splitting-field automorphism group of
`cT³ - 2T² + bT - 2a` over `k(a,b,c)` is the full permutation group on its
three roots. -/
def genericMonodromyEquiv :
    (genericFiberPoly k).Gal ≃* Equiv.Perm (Fin 3) := by
  apply MulEquiv.ofBijective (genericGalActionHom k)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨genericGalActionHom_injective k, ?_⟩
  rw [← Nat.card_eq_fintype_card, genericGal_card, Fintype.card_perm,
    Fintype.card_fin]
  norm_num

end

end Alpoge
