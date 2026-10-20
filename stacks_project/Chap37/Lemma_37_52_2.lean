/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.FiniteType.ClosedFiber

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsDomain A] [IsDomain B]
variable [IsLocalRing A] [IsLocalRing B]

/- Lemma 37.52.2: for an injective essentially finite-type local map of local
domains, quotienting the target by an element of its maximal ideal that avoids
the minimal primes of the closed fiber preserves injectivity when the stated
dimension formula holds. -/
@[stacks 053S] #check
  (RingHom.DimensionFormula.principalQuotient_injective :
    ∀ (f : A →+* B) [IsLocalHom f] (h_injective : Function.Injective f)
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
            (Cardinal.toNat (Algebra.trdeg A B) : WithBot ℕ∞)),
      Function.Injective ((Ideal.Quotient.mk (Ideal.span {g})).comp f))

end
