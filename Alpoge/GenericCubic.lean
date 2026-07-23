import Alpoge.Wall
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The generic fiber cubic

This module places the normalized fiber cubic

`cT³ - 2T² + bT - 2a`

over the rational function field `k(a,b,c)`.  It proves the elementary
function-field layer needed for generic monodromy: degree three,
irreducibility, separability in characteristic zero, and discriminant
`-4W`.
-/

namespace Alpoge

open MvPolynomial Polynomial

noncomputable section

variable (k : Type*) [Field k]

/-- The polynomial coefficient ring `k[a,b,c]`.  The variables are encoded
as `none = a`, `some 0 = b`, `some 1 = c`. -/
abbrev GenericCoeffRing := MvPolynomial (Option (Fin 2)) k

/-- The generic target field `k(a,b,c)`. -/
abbrev GenericTargetField := FractionRing (GenericCoeffRing k)

def genericA : GenericCoeffRing k := MvPolynomial.X none
def genericB : GenericCoeffRing k := MvPolynomial.X (some 0)
def genericC : GenericCoeffRing k := MvPolynomial.X (some 1)

/-- The generic wall polynomial in `k[a,b,c]`. -/
def genericWallPoly : GenericCoeffRing k :=
  27 * genericA k ^ 2 * genericC k ^ 2 -
    18 * genericA k * genericB k * genericC k +
    16 * genericA k + genericB k ^ 3 * genericC k - genericB k ^ 2

/-- The generic fiber cubic before passing to the fraction field. -/
def genericFiberPolyRing : Polynomial (GenericCoeffRing k) :=
  Polynomial.C (genericC k) * Polynomial.X ^ 3 -
    Polynomial.C 2 * Polynomial.X ^ 2 +
    Polynomial.C (genericB k) * Polynomial.X -
    Polynomial.C (2 * genericA k)

/-- The generic fiber cubic over `k(a,b,c)`. -/
def genericFiberPoly : Polynomial (GenericTargetField k) :=
  (genericFiberPolyRing k).map (algebraMap (GenericCoeffRing k) (GenericTargetField k))

/-- The four-variable relation whose `T`-polynomial is
`genericFiberPolyRing`.  Here the outer `none` is `T`. -/
def genericFiberRelation : MvPolynomial (Option (Option (Fin 2))) k :=
  MvPolynomial.X (some (some 1)) * MvPolynomial.X none ^ 3 -
    2 * MvPolynomial.X none ^ 2 +
    MvPolynomial.X (some (some 0)) * MvPolynomial.X none -
    2 * MvPolynomial.X (some none)

theorem optionEquivLeft_genericFiberRelation :
    optionEquivLeft k (Option (Fin 2)) (genericFiberRelation k) =
      genericFiberPolyRing k := by
  simp [genericFiberRelation, genericFiberPolyRing, genericA, genericB, genericC,
    map_ofNat]

/-- Swap the roles of `T` and `a` in the four-variable relation. -/
def genericSwapTA : Equiv.Perm (Option (Option (Fin 2))) :=
  Equiv.swap none (some none)

theorem genericFiberRelation_irreducible [CharZero k] :
    Irreducible (genericFiberRelation k) := by
  let q : Polynomial (MvPolynomial (Option (Fin 2)) k) :=
    Polynomial.C (-2) * Polynomial.X +
      Polynomial.C
        (MvPolynomial.X (some 1) * MvPolynomial.X none ^ 3 -
          2 * MvPolynomial.X none ^ 2 +
          MvPolynomial.X (some 0) * MvPolynomial.X none)
  have hq :
      optionEquivLeft k (Option (Fin 2))
          ((renameEquiv k genericSwapTA) (genericFiberRelation k)) = q := by
    simp [q, genericSwapTA, genericFiberRelation, Equiv.swap_apply_def, map_ofNat]
    ring
  have h2k : IsUnit (-2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h2 : IsUnit (-2 : MvPolynomial (Option (Fin 2)) k) := by
    simpa only [map_neg, map_ofNat] using
      h2k.map (MvPolynomial.C : k →+* MvPolynomial (Option (Fin 2)) k)
  have hqirr : Irreducible q := by
    apply Polynomial.irreducible_C_mul_X_add_C
    · exact h2.ne_zero
    · exact h2.isRelPrime_left
  have hswap : Irreducible
      ((renameEquiv k genericSwapTA) (genericFiberRelation k)) := by
    have := hqirr.map (optionEquivLeft k (Option (Fin 2))).symm
    simpa [← hq] using this
  have := hswap.map (renameEquiv k genericSwapTA).symm
  have hback :
      (renameEquiv k genericSwapTA).symm
          ((renameEquiv k genericSwapTA) (genericFiberRelation k)) =
        genericFiberRelation k :=
    (renameEquiv k genericSwapTA).symm_apply_apply _
  rwa [hback] at this

theorem genericFiberPolyRing_irreducible [CharZero k] :
    Irreducible (genericFiberPolyRing k) := by
  rw [← optionEquivLeft_genericFiberRelation]
  exact (genericFiberRelation_irreducible k).map (optionEquivLeft k (Option (Fin 2)))

theorem genericFiberPolyRing_isPrimitive [CharZero k] :
    (genericFiberPolyRing k).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hd : r ∣ (genericFiberPolyRing k).coeff 2 :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 2
  have hc : (genericFiberPolyRing k).coeff 2 = -2 := by
    simp [genericFiberPolyRing]
  rw [hc] at hd
  have h2k : IsUnit (-2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h2 : IsUnit (-2 : GenericCoeffRing k) :=
    by simpa only [map_neg, map_ofNat] using
      h2k.map (MvPolynomial.C : k →+* GenericCoeffRing k)
  exact isUnit_iff_dvd_one.mpr (hd.trans (isUnit_iff_dvd_one.mp h2))

/-- The generic normalized cubic is irreducible over `k(a,b,c)`. -/
theorem genericFiberPoly_irreducible [CharZero k] :
    Irreducible (genericFiberPoly k) := by
  rw [genericFiberPoly, ←
    (genericFiberPolyRing_isPrimitive k).irreducible_iff_irreducible_map_fraction_map]
  exact genericFiberPolyRing_irreducible k

theorem genericFiberPolyRing_natDegree :
    (genericFiberPolyRing k).natDegree = 3 := by
  unfold genericFiberPolyRing
  compute_degree <;> simp [genericC]

theorem genericFiberPoly_natDegree :
    (genericFiberPoly k).natDegree = 3 := by
  rw [genericFiberPoly, Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (GenericCoeffRing k) (GenericTargetField k))]
  exact genericFiberPolyRing_natDegree k

/-- In characteristic zero the generic cubic is separable. -/
theorem genericFiberPoly_separable [CharZero k] :
    (genericFiberPoly k).Separable :=
  (genericFiberPoly_irreducible k).separable

/-- The polynomial discriminant of the generic cubic is `-4W`. -/
theorem genericFiberPoly_discr :
    (genericFiberPoly k).discr =
      algebraMap (GenericCoeffRing k) (GenericTargetField k) (-4 * genericWallPoly k) := by
  have hn := genericFiberPoly_natDegree k
  have hne : genericFiberPoly k ≠ 0 := by
    intro h
    rw [h] at hn
    norm_num at hn
  have hd : (genericFiberPoly k).degree = 3 :=
    (Polynomial.degree_eq_iff_natDegree_eq hne).mpr hn
  rw [Polynomial.discr_of_degree_eq_three hd]
  simp [genericFiberPoly, genericFiberPolyRing, genericWallPoly, genericA, genericB,
    genericC, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

end

end Alpoge
