/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

universe u v

/- Theorem 41.12.2: an essentially finite-type, formally unramified local homomorphism of
local rings is a quotient of a localization at a prime of a standard étale algebra. -/
@[stacks 039O] #check
  (RingHom.FormallyUnramified.exists_standardEtale_quotient_localizationAtPrime :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} [IsLocalHom φ],
      φ.FormallyUnramified → φ.EssFiniteType →
        ∃ (P : StandardEtalePair A) (q : Ideal P.Ring) (_ : q.IsPrime)
          (ψ : Localization.AtPrime q →+* B),
          Function.Surjective ψ ∧
            φ = ψ.comp ((algebraMap P.Ring (Localization.AtPrime q)).comp
              (algebraMap A P.Ring)))
