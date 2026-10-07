module

public import ReasLib.RingTheory.Etale.LocalStructure
import StacksCheckRecall

@[expose] public section

universe u v

/- Theorem 59.26.4: a finitely presented commutative algebra is étale at a prime
exactly when a localization away from an element outside that prime is standard étale. -/
@[stacks 03PE] #check (Algebra.isEtaleAt_iff_exists_isStandardEtale :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [Algebra.FinitePresentation A B] (q : Ideal B) [q.IsPrime],
      Algebra.IsEtaleAt A q ↔
        ∃ g : B, g ∉ q ∧ Algebra.IsStandardEtale A (Localization.Away g))
