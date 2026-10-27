/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalProperty
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Seminormal and Absolutely Weakly Normal Rings

This leaf provides the ring-level conditions underlying seminormalization and
absolute weak normalization. They depend only on commutative-ring algebra and
can therefore be reused independently of schemes.
-/

@[expose] public section

universe u

section

variable (A : Type u) [CommRing A]

/-- A commutative ring `A` is seminormal if whenever `x ^ 3 = y ^ 2` in `A`, there is a
unique `a : A` such that `x = a ^ 2` and `y = a ^ 3`. -/
@[stacks 0EUL]
class SeminormalRing : Prop where
  /-- A compatible square-cube pair has a unique common root. -/
  existsUnique_sq_cube_of_cube_eq_sq :
    ∀ ⦃x y : A⦄, x ^ 3 = y ^ 2 → ∃! a : A, x = a ^ 2 ∧ y = a ^ 3

/-- Unfold `SeminormalRing` into its square-cube root criterion. -/
theorem seminormalRing_iff :
    SeminormalRing A ↔
      ∀ ⦃x y : A⦄, x ^ 3 = y ^ 2 → ∃! a : A, x = a ^ 2 ∧ y = a ^ 3 := by
  exact ⟨fun h ↦ h.existsUnique_sq_cube_of_cube_eq_sq, fun h ↦ ⟨h⟩⟩

namespace SeminormalRing

/-- A compatible square-cube pair in a seminormal ring has a unique common root. -/
theorem existsUnique_of_cube_eq_sq [SeminormalRing A] {x y : A} (h : x ^ 3 = y ^ 2) :
    ∃! a : A, x = a ^ 2 ∧ y = a ^ 3 :=
  SeminormalRing.existsUnique_sq_cube_of_cube_eq_sq h

/-- Seminormality is local for principal-open finite covers of commutative rings. -/
@[stacks 0EUM, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ SeminormalRing A) := sorry

/-- Seminormality of commutative rings is preserved under ring isomorphisms. -/
instance isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ SeminormalRing A) where
  of_iso {R S} i hR := by
    let e := i.commRingCatIsoToRingEquiv
    letI : SeminormalRing R := hR
    constructor
    intro x y hxy
    have hxy' : (e.symm x) ^ 3 = (e.symm y) ^ 2 := by
      simpa only [map_pow] using congrArg e.symm hxy
    simpa only [← map_pow, e.symm.injective.eq_iff] using
      e.symm.bijective.existsUnique_iff.mp (existsUnique_of_cube_eq_sq R hxy')

end SeminormalRing

/-- A commutative ring `A` is absolutely weakly normal if it is seminormal and, for every prime
number `p` and all `x, y : A` with `(p : A) ^ p * x = y ^ p`, there is a unique `a : A` such
that `x = a ^ p` and `y = (p : A) * a`. -/
@[stacks 0EUL]
class AbsolutelyWeaklyNormalRing : Prop extends SeminormalRing A where
  /-- The prime-power root condition that supplements seminormality. -/
  existsUnique_pow_of_prime_pow_mul_eq_pow :
    ∀ ⦃p : ℕ⦄, Nat.Prime p →
      ∀ ⦃x y : A⦄, ((p : A) ^ p) * x = y ^ p →
        ∃! a : A, x = a ^ p ∧ y = (p : A) * a

/-- Unfold `AbsolutelyWeaklyNormalRing` into seminormality and its prime-power root condition. -/
theorem absolutelyWeaklyNormalRing_iff :
    AbsolutelyWeaklyNormalRing A ↔
      SeminormalRing A ∧
        ∀ ⦃p : ℕ⦄, Nat.Prime p →
          ∀ ⦃x y : A⦄, ((p : A) ^ p) * x = y ^ p →
            ∃! a : A, x = a ^ p ∧ y = (p : A) * a := by
  exact ⟨fun h ↦ ⟨h.toSeminormalRing, h.existsUnique_pow_of_prime_pow_mul_eq_pow⟩,
    fun ⟨h, h'⟩ ↦ {
      toSeminormalRing := h
      existsUnique_pow_of_prime_pow_mul_eq_pow := h' }⟩

namespace AbsolutelyWeaklyNormalRing

/-- The prime-power root condition holds in every absolutely weakly normal ring. -/
theorem existsUnique_of_prime_pow_mul_eq_pow [AbsolutelyWeaklyNormalRing A]
    {p : ℕ} (hp : Nat.Prime p) {x y : A} (h : ((p : A) ^ p) * x = y ^ p) :
    ∃! a : A, x = a ^ p ∧ y = (p : A) * a :=
  AbsolutelyWeaklyNormalRing.existsUnique_pow_of_prime_pow_mul_eq_pow hp h

/-- Absolute weak normality is local for principal-open finite covers of commutative rings. -/
@[stacks 0EUM, instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) := sorry

/-- Absolute weak normality of commutative rings is preserved under ring isomorphisms. -/
instance isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) where
  of_iso {R S} i hR := by
    let e := i.commRingCatIsoToRingEquiv
    letI : AbsolutelyWeaklyNormalRing R := hR
    refine {
      toSeminormalRing := CategoryTheory.ObjectProperty.prop_of_iso
        (fun A : CommRingCat.{u} ↦ SeminormalRing A) i hR.toSeminormalRing
      existsUnique_pow_of_prime_pow_mul_eq_pow := ?_ }
    intro p hp x y hxy
    have hxy' : ((p : R) ^ p) * e.symm x = (e.symm y) ^ p := by
      simpa only [map_mul, map_pow, map_natCast] using congrArg e.symm hxy
    simpa only [← map_pow, ← map_natCast e.symm, ← map_mul, e.symm.injective.eq_iff] using
      e.symm.bijective.existsUnique_iff.mp
        (existsUnique_of_prime_pow_mul_eq_pow R hp hxy')

end AbsolutelyWeaklyNormalRing

/-- Every seminormal ring is reduced. -/
@[instance]
theorem isReduced_of_seminormalRing [SeminormalRing A] :
    IsReduced A := by
  apply Ideal.isRadical_bot_iff.mp
  apply (Ideal.isRadical_iff_pow_one_lt (I := (⊥ : Ideal A)) 2 (by decide)).mpr
  intro x hx
  have hx2 : x ^ 2 = 0 := hx
  have hx3 : x ^ 3 = 0 := by
    rw [pow_succ, hx2, zero_mul]
  exact (SeminormalRing.existsUnique_of_cube_eq_sq A
    (x := 0) (y := 0) (by simp)).unique ⟨hx2.symm, hx3.symm⟩ (by simp)

/-- Every absolutely weakly normal ring is reduced. -/
theorem isReduced_of_absolutelyWeaklyNormalRing [AbsolutelyWeaklyNormalRing A] :
    IsReduced A :=
  isReduced_of_seminormalRing A

end
