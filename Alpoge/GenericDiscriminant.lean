import Alpoge.GenericCubic
import Mathlib.RingTheory.Localization.NumDen

/-- An irreducible element of a UFD does not become a square in its fraction field. -/
theorem irreducible_not_isSquare_fractionRing
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {p : R} (hp : Irreducible p) :
    ¬ IsSquare (algebraMap R (FractionRing R) p) := by
  intro hs
  obtain ⟨x, hx⟩ := hs
  let n : R := IsFractionRing.num R x
  let d : R := IsFractionRing.den R x
  have hxd :
      x * algebraMap R (FractionRing R) d =
        algebraMap R (FractionRing R) n := by
    exact (IsFractionRing.num_mul_den_eq_num_iff_eq (A := R)).mpr rfl
  have heq : n ^ 2 = p * d ^ 2 := by
    apply IsFractionRing.injective R (FractionRing R)
    simp only [map_pow, map_mul]
    rw [← hxd, mul_pow, pow_two x, ← hx]
  have hpn : p ∣ n := hp.prime.dvd_of_dvd_pow ⟨d ^ 2, heq⟩
  obtain ⟨m, hm⟩ := hpn
  rw [hm] at heq
  have hpn' : p ∣ n := ⟨m, hm⟩
  have hd2 : d ^ 2 = p * m ^ 2 := by
    have hc : p * d ^ 2 = p * (p * m ^ 2) := by
      calc
        p * d ^ 2 = (p * m) ^ 2 := heq.symm
        _ = p * (p * m ^ 2) := by ring
    exact mul_left_cancel₀ hp.ne_zero hc
  have hpd : p ∣ d := by
    apply hp.prime.dvd_of_dvd_pow
    exact ⟨m ^ 2, hd2⟩
  exact hp.not_isUnit
    ((IsFractionRing.num_den_reduced R x) hpn' hpd)

namespace Alpoge

open MvPolynomial Polynomial

noncomputable section

variable (k : Type*) [Field k] [CharZero k]

abbrev GenericBCring := MvPolynomial (Fin 2) k

def genericBCObstruction : GenericBCring k :=
  4 - 3 * MvPolynomial.X 0 * MvPolynomial.X (Fin.succ 0)

theorem genericBCObstruction_irreducible :
    Irreducible (genericBCObstruction k) := by
  let q : Polynomial (MvPolynomial (Fin 1) k) :=
    Polynomial.C (-3 * MvPolynomial.X 0) * Polynomial.X + Polynomial.C 4
  have hq :
      MvPolynomial.finSuccEquiv k 1 (genericBCObstruction k) = q := by
    simp only [genericBCObstruction, map_sub, map_mul, map_ofNat,
      MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    norm_num [q]
    have h3 :
        Polynomial.C (3 : MvPolynomial (Fin 1) k) =
          (3 : Polynomial (MvPolynomial (Fin 1) k)) :=
      Polynomial.C_ofNat 3
    rw [h3, Polynomial.C_ofNat]
    ring
  have h4k : IsUnit (4 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h4 : IsUnit (4 : MvPolynomial (Fin 1) k) := by
    simpa only [map_ofNat] using
      h4k.map (MvPolynomial.C : k →+* MvPolynomial (Fin 1) k)
  have hcoeff : (-3 * MvPolynomial.X 0 : MvPolynomial (Fin 1) k) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact MvPolynomial.X_ne_zero 0
  have hqirr : Irreducible q := by
    apply Polynomial.irreducible_C_mul_X_add_C
    · exact hcoeff
    · exact h4.isRelPrime_right
  have := hqirr.map (MvPolynomial.finSuccEquiv k 1).symm
  simpa [← hq] using this

def genericWallAPoly : Polynomial (GenericBCring k) :=
  Polynomial.C (27 * MvPolynomial.X (Fin.succ 0) ^ 2) * Polynomial.X ^ 2 +
    Polynomial.C
      (16 - 18 * MvPolynomial.X 0 * MvPolynomial.X (Fin.succ 0)) *
        Polynomial.X +
    Polynomial.C
      (MvPolynomial.X 0 ^ 3 * MvPolynomial.X (Fin.succ 0) -
        MvPolynomial.X 0 ^ 2)

omit [CharZero k] in
theorem optionEquivLeft_genericWallPoly :
    optionEquivLeft k (Fin 2) (genericWallPoly k) = genericWallAPoly k := by
  simp [genericWallPoly, genericWallAPoly, genericA, genericB, genericC, map_ofNat]
  ring

def genericWallAPolyFrac :
    Polynomial (FractionRing (GenericBCring k)) :=
  (genericWallAPoly k).map
    (algebraMap (GenericBCring k) (FractionRing (GenericBCring k)))

theorem genericWallAPoly_natDegree :
    (genericWallAPoly k).natDegree = 2 := by
  unfold genericWallAPoly
  compute_degree <;> simp

theorem genericWallAPolyFrac_natDegree :
    (genericWallAPolyFrac k).natDegree = 2 := by
  rw [genericWallAPolyFrac, Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (GenericBCring k) (FractionRing (GenericBCring k)))]
  exact genericWallAPoly_natDegree k

theorem genericBCObstruction_not_isSquare :
    ¬ IsSquare
      (algebraMap (GenericBCring k) (FractionRing (GenericBCring k))
      (genericBCObstruction k)) :=
  irreducible_not_isSquare_fractionRing (genericBCObstruction_irreducible k)

theorem genericWallAPolyFrac_not_isRoot
    (r : FractionRing (GenericBCring k)) :
    ¬ (genericWallAPolyFrac k).IsRoot r := by
  intro hr
  let ι := algebraMap (GenericBCring k) (FractionRing (GenericBCring k))
  let b : FractionRing (GenericBCring k) := ι (MvPolynomial.X 0)
  let c : FractionRing (GenericBCring k) := ι (MvPolynomial.X (Fin.succ 0))
  let q : FractionRing (GenericBCring k) := ι (genericBCObstruction k)
  let A : FractionRing (GenericBCring k) := 27 * c ^ 2
  let B : FractionRing (GenericBCring k) := 16 - 18 * b * c
  let C : FractionRing (GenericBCring k) := b ^ 3 * c - b ^ 2
  have heval : A * r ^ 2 + B * r + C = 0 := by
    simpa [genericWallAPolyFrac, genericWallAPoly, A, B, C, b, c, ι,
      Polynomial.IsRoot, map_sub, map_add, map_mul, map_pow, map_ofNat] using hr
  have hdisc : B ^ 2 - 4 * A * C = 4 * q ^ 3 := by
    simp [A, B, C, q, genericBCObstruction, b, c, ι, map_sub, map_mul, map_ofNat]
    ring
  have hsquare : (2 * A * r + B) ^ 2 = 4 * q ^ 3 := by
    calc
      (2 * A * r + B) ^ 2 =
          B ^ 2 - 4 * A * C + 4 * A * (A * r ^ 2 + B * r + C) := by ring
      _ = B ^ 2 - 4 * A * C := by rw [heval]; ring
      _ = 4 * q ^ 3 := hdisc
  have hqne : q ≠ 0 := by
    intro hq
    have hbase : genericBCObstruction k = 0 :=
      (IsFractionRing.injective (GenericBCring k)
        (FractionRing (GenericBCring k))) (by simpa [q, ι] using hq)
    exact (genericBCObstruction_irreducible k).ne_zero hbase
  apply genericBCObstruction_not_isSquare k
  refine ⟨(2 * A * r + B) / (2 * q), ?_⟩
  field_simp [hqne]
  change q * 2 ^ 2 * q ^ 2 = (2 * A * r + B) ^ 2
  calc
    q * 2 ^ 2 * q ^ 2 = 4 * q ^ 3 := by ring
    _ = (2 * A * r + B) ^ 2 := hsquare.symm

omit [CharZero k] in
theorem genericBC_X_zero_irreducible :
    Irreducible (MvPolynomial.X (0 : Fin 2) : GenericBCring k) := by
  have hx : Irreducible
      (Polynomial.X : Polynomial (MvPolynomial (Fin 1) k)) :=
    Polynomial.irreducible_X
  have := hx.map (MvPolynomial.finSuccEquiv k 1).symm
  have heq :
      (MvPolynomial.finSuccEquiv k 1).symm Polynomial.X =
        (MvPolynomial.X 0 : GenericBCring k) := by
    apply (MvPolynomial.finSuccEquiv k 1).injective
    rw [(MvPolynomial.finSuccEquiv k 1).apply_symm_apply]
    exact (MvPolynomial.finSuccEquiv_X_zero (R := k) (n := 1)).symm
  rwa [heq] at this

omit [CharZero k] in
theorem genericBC_X_one_irreducible :
    Irreducible (MvPolynomial.X (Fin.succ 0) : GenericBCring k) := by
  let e : Equiv.Perm (Fin 2) := Equiv.swap 0 (Fin.succ 0)
  have h := (genericBC_X_zero_irreducible k).map (MvPolynomial.renameEquiv k e)
  have he : e 0 = Fin.succ 0 := Equiv.swap_apply_left _ _
  simpa [MvPolynomial.renameEquiv_apply, he] using h

theorem genericBC_c_isRelPrime_b :
    IsRelPrime
      (MvPolynomial.X (Fin.succ 0) : GenericBCring k)
      (MvPolynomial.X 0) := by
  rw [(genericBC_X_one_irreducible k).isRelPrime_iff_not_dvd]
  intro h
  have hm := map_dvd (MvPolynomial.eval ![1, 0]) h
  norm_num at hm

theorem genericBC_c_isRelPrime_bc_sub_one :
    IsRelPrime
      (MvPolynomial.X (Fin.succ 0) : GenericBCring k)
      (MvPolynomial.X 0 * MvPolynomial.X (Fin.succ 0) - 1) := by
  rw [(genericBC_X_one_irreducible k).isRelPrime_iff_not_dvd]
  intro h
  have hm := map_dvd (MvPolynomial.eval ![1, 0]) h
  norm_num at hm

set_option maxHeartbeats 800000 in
theorem genericWallAPoly_isPrimitive :
    (genericWallAPoly k).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have h2 : r ∣ (genericWallAPoly k).coeff 2 :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 2
  have h0 : r ∣ (genericWallAPoly k).coeff 0 :=
    (Polynomial.C_dvd_iff_dvd_coeff r _).mp hr 0
  have h2' : r ∣ MvPolynomial.X (Fin.succ 0) ^ 2 := by
    have hu : IsUnit (27 : GenericBCring k) := by
      exact (isUnit_iff_ne_zero.mpr (by norm_num : (27 : k) ≠ 0)).map MvPolynomial.C
    apply hu.dvd_mul_left.mp
    simp only [genericWallAPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_false, if_true,
      OfNat.ofNat, Nat.reduceEqDiff] at h2
    change r ∣ 27 * MvPolynomial.X (Fin.succ 0) ^ 2 + 0 + 0 at h2
    simpa using h2
  have h0' :
      r ∣ MvPolynomial.X 0 ^ 2 *
        (MvPolynomial.X 0 * MvPolynomial.X (Fin.succ 0) - 1) := by
    simp only [genericWallAPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_false, if_true,
      OfNat.ofNat, Nat.reduceEqDiff] at h0
    change r ∣ 0 + 0 +
      (MvPolynomial.X 0 ^ 3 * MvPolynomial.X (Fin.succ 0) -
        MvPolynomial.X 0 ^ 2) at h0
    have heq :
        (MvPolynomial.X (0 : Fin 2) : GenericBCring k) ^ 3 *
              MvPolynomial.X (Fin.succ 0) -
            MvPolynomial.X (0 : Fin 2) ^ 2 =
          MvPolynomial.X (0 : Fin 2) ^ 2 *
            (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (Fin.succ 0) - 1) := by
      ring
    rw [heq] at h0
    simpa only [zero_add] using h0
  have hcb : IsRelPrime
      (MvPolynomial.X (Fin.succ 0) ^ 2 : GenericBCring k)
      (MvPolynomial.X 0 ^ 2) :=
    by
      have hc2b :
          IsRelPrime
            (MvPolynomial.X (Fin.succ 0) * MvPolynomial.X (Fin.succ 0) :
              GenericBCring k)
            (MvPolynomial.X 0) :=
        (genericBC_c_isRelPrime_b k).mul_left (genericBC_c_isRelPrime_b k)
      have hc2b2 := hc2b.mul_right hc2b
      simpa [pow_two] using hc2b2
  have hcw : IsRelPrime
      (MvPolynomial.X (Fin.succ 0) ^ 2 : GenericBCring k)
      (MvPolynomial.X 0 * MvPolynomial.X (Fin.succ 0) - 1) :=
    by
      simpa [pow_two] using
        (genericBC_c_isRelPrime_bc_sub_one k).mul_left
          (genericBC_c_isRelPrime_bc_sub_one k)
  exact (hcb.mul_right hcw) h2' h0'

theorem genericWallAPolyFrac_irreducible :
    Irreducible (genericWallAPolyFrac k) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [genericWallAPolyFrac_natDegree]
  · exact genericWallAPolyFrac_not_isRoot k

theorem genericWallAPoly_irreducible :
    Irreducible (genericWallAPoly k) := by
  apply (genericWallAPoly_isPrimitive k).irreducible_of_irreducible_map_of_injective
    (IsFractionRing.injective (GenericBCring k) (FractionRing (GenericBCring k)))
  exact genericWallAPolyFrac_irreducible k

theorem genericWallPoly_irreducible :
    Irreducible (genericWallPoly k) := by
  have h := (genericWallAPoly_irreducible k).map
    (MvPolynomial.optionEquivLeft k (Fin 2)).symm
  rw [← optionEquivLeft_genericWallPoly] at h
  simpa using h

theorem neg_four_mul_genericWallPoly_irreducible :
    Irreducible (-4 * genericWallPoly k) := by
  have hu : IsUnit (-4 : GenericCoeffRing k) := by
    simpa only [map_neg, map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (-4 : k) ≠ 0)).map
        (MvPolynomial.C : k →+* GenericCoeffRing k)
  exact (associated_unit_mul_right (genericWallPoly k) (-4) hu).irreducible
    (genericWallPoly_irreducible k)

theorem genericFiberPoly_discr_not_isSquare :
    ¬ IsSquare (genericFiberPoly k).discr := by
  rw [genericFiberPoly_discr]
  exact irreducible_not_isSquare_fractionRing
    (neg_four_mul_genericWallPoly_irreducible k)

end

end Alpoge
