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
valuation ring. -/
abbrev IntegralCone (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :=
  {gamma : ValueGroup A (FractionRing A) // gamma ≤ (1 : ValueGroup A (FractionRing A))}

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
    Ideal A ≃o Order.Ideal (IntegralCone A) := sorry

/-- Lemma 10.50.17 (2): `idealOrderIso` identifies prime ideals with multiplicatively prime order
ideals. -/
@[stacks 00IH "(2) prime ideals"]
theorem idealOrderIso_isPrime_iff
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (I : Ideal A) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (idealOrderIso A I) := sorry

end ValuationRing
