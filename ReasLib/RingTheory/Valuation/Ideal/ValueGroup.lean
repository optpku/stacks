/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Ideal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ideals of a Valuation Ring and Its Value Group

@stack 00IH

The ideal lattice of a valuation ring is identified with order ideals in the integral cone of its
canonical value group.
-/

universe u

namespace ValuationRing

/-- The integral cone `Γ_{≤ 1}` in the multiplicatively written canonical value group of a
valuation ring, including the zero value. -/
abbrev IntegralCone (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :=
  {gamma : ValueGroup A (FractionRing A) // gamma ≤ (1 : ValueGroup A (FractionRing A))}

/-- The canonical valuation of a ring element, regarded as a value in the integral cone. -/
noncomputable def integralValue
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (a : A) : IntegralCone A :=
  ⟨valuation A (FractionRing A) (algebraMap A (FractionRing A) a),
    (mem_integer_iff A (FractionRing A) _).mpr ⟨a, rfl⟩⟩

/-- The value in the integral cone has the canonical valuation as its underlying value. -/
@[simp]
theorem integralValue_val
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (a : A) :
    (integralValue A a).val = valuation A (FractionRing A) (algebraMap A (FractionRing A) a) :=
  rfl

end ValuationRing

namespace Order.Ideal

/-- The multiplicative form of primality for an order ideal in the integral cone of a valuation
ring's canonical value group. -/
def IsValuationPrime
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (J : Order.Ideal (ValuationRing.IntegralCone A)) : Prop :=
  (⟨1, le_rfl⟩ : ValuationRing.IntegralCone A) ∉ J ∧
    ∀ ⦃gamma delta : ValuationRing.ValueGroup A (FractionRing A)⦄,
      ∀ hgamma : gamma ≤ 1, ∀ hdelta : delta ≤ 1,
        (⟨gamma * delta, mul_le_one' hgamma hdelta⟩ : ValuationRing.IntegralCone A) ∈ J →
          (⟨gamma, hgamma⟩ : ValuationRing.IntegralCone A) ∈ J ∨
            (⟨delta, hdelta⟩ : ValuationRing.IntegralCone A) ∈ J

end Order.Ideal

namespace ValuationRing

/-- Lemma 10.50.17 (1): ideals of a valuation ring correspond order-isomorphically to order ideals
in the integral cone of its canonical value group. -/
@[stacks 00IH "(1) ideal correspondence"]
noncomputable def idealOrderIso
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    Ideal A ≃o Order.Ideal (IntegralCone A) where
  toFun I :=
    { carrier := integralValue A '' (I : Set A)
      lower' := by sorry
      nonempty' := ⟨integralValue A 0, 0, I.zero_mem, rfl⟩
      directed' := by sorry }
  invFun J :=
    { carrier := {a : A | integralValue A a ∈ J}
      zero_mem' := by sorry
      add_mem' := by sorry
      smul_mem' := by sorry }
  left_inv := by sorry
  right_inv := by sorry
  map_rel_iff' := by sorry

/-- An integral value lies in the corresponding order ideal precisely when it is the value
of an element of the ring ideal. -/
@[simp, stacks 00IH "(1) values of an ideal"]
theorem mem_idealOrderIso
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (I : Ideal A) (gamma : IntegralCone A) :
    gamma ∈ idealOrderIso A I ↔ ∃ a ∈ I, integralValue A a = gamma := by
  rfl

/-- The inverse correspondence consists of the ring elements whose values lie in the order
ideal. -/
@[simp, stacks 00IH "(1) ideal of an order ideal"]
theorem mem_idealOrderIso_symm
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (J : Order.Ideal (IntegralCone A)) (a : A) :
    a ∈ (idealOrderIso A).symm J ↔ integralValue A a ∈ J := by
  rfl

/-- The zero ring ideal corresponds to the singleton zero-value order ideal. -/
@[simp, stacks 00IH "(1) zero ideal"]
theorem idealOrderIso_bot
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    idealOrderIso A ⊥ = Order.Ideal.principal (integralValue A 0) := sorry

/-- Lemma 10.50.17 (2): `idealOrderIso` identifies prime ideals with multiplicatively prime order
ideals. -/
@[stacks 00IH "(2) prime ideals"]
theorem idealOrderIso_isPrime_iff
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (I : Ideal A) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (idealOrderIso A I) := sorry

end ValuationRing
