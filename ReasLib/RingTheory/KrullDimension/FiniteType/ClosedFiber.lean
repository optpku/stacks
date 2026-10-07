module

public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsDomain A] [IsDomain B]
variable [IsLocalRing A] [IsLocalRing B]

/-!
# Principal quotients of closed fibers

This module records an injectivity consequence of the dimension formula for
essentially finite-type local homomorphisms of local domains.
-/

/-- For an injective essentially finite-type local homomorphism of local domains,
quotienting the target by an element of its maximal ideal that avoids the minimal
primes of the closed fiber preserves injectivity when the closed-fiber dimension
formula holds. -/
@[stacks 053S]
public theorem RingHom.DimensionFormula.principalQuotient_injective
    (f : A →+* B) [IsLocalHom f] (h_injective : Function.Injective f)
    (h_essentiallyFiniteType : f.EssFiniteType) (g : B)
    (h_g : g ∈ IsLocalRing.maximalIdeal B)
    (h_minimal : ∀ p ∈ ((IsLocalRing.maximalIdeal A).map f).minimalPrimes, g ∉ p)
    (h_dimension :
      -- Local instance justification (defeq pin): `f.toAlgebra` identifies `algebraMap A B` with the named local homomorphism in both transcendence-degree terms.
      letI : Algebra A B := f.toAlgebra
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map f) +
          (Cardinal.toNat
            (Algebra.trdeg (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
            WithBot ℕ∞) =
        (Cardinal.toNat (Algebra.trdeg A B) : WithBot ℕ∞)) :
    Function.Injective ((Ideal.Quotient.mk (Ideal.span {g})).comp f) := sorry

end
