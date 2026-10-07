module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Henselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.8.2: for a henselian pair `(A, I)`, base change along the
quotient-induced spectrum morphism is an equivalence on finite étale schemes. -/
@[stacks 09ZS] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChangeIsEquivalenceOfHenselianPair :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I],
      Functor.IsEquivalence
        (Scheme.finiteEtaleBaseChange
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))))

end AlgebraicGeometry.Scheme
