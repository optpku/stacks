module

public import ReasLib.RingTheory.Localization.FractionRing.Algebra
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated

@[expose] public section

/-!
# Separable extensions of fraction fields

Mathlib deliberately keeps `FractionRing.liftAlgebra` out of global instance
search because registering it can create algebra diamonds.  This leaf packages
separability for that canonical algebra structure as a named property, so
downstream statements do not need theorem-local fraction-field instances.
-/

universe u v

namespace FractionRing

/-- The fraction-field extension induced by a faithful map of domains is
separable over the canonical `FractionRing.liftAlgebra` structure. -/
@[stacks 0BJ7 "separable fraction-field extension"]
class IsSeparableExtension (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] : Prop where
  /-- Separability of the induced extension of fraction fields. -/
  isSeparableOver :
    @Algebra.IsSeparableOver (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))

/-- Unfold `FractionRing.IsSeparableExtension` to the underlying canonical
fraction-field algebra structure. -/
theorem isSeparableExtension_iff (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] :
    IsSeparableExtension R S ↔
      @Algebra.IsSeparableOver (FractionRing R) (FractionRing S) _ _
        (FractionRing.liftAlgebra R (FractionRing S)) := sorry

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]

/-- Separability of the fraction-field extension induced by an explicit
injective map of domains. This keeps the injectivity witness explicit and
fixes the resulting algebra structure without installing global instances. -/
@[stacks 07ND "separable fraction-field extension from an injective map"]
noncomputable def isSeparableOf
    (hinj : Function.Injective (algebraMap R S)) : Prop :=
  @Algebra.IsSeparableOver (FractionRing R) (FractionRing S) _ _
    (algebraOfInjective (R := R) (S := S) hinj)

/-- Unfold separability of the fraction-field extension induced by an
injective map to the fixed induced algebra structure. -/
theorem isSeparableOf_iff
    (hinj : Function.Injective (algebraMap R S)) :
    isSeparableOf (R := R) (S := S) hinj ↔
      @Algebra.IsSeparableOver (FractionRing R) (FractionRing S) _ _
        (algebraOfInjective (R := R) (S := S) hinj) := sorry

end

end FractionRing
