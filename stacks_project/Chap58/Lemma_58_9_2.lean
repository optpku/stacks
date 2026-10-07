module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.HenselianPair
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 58.9.2: for a proper scheme over a henselian pair, restriction to the
special-fibre pullback is an equivalence on finite étale schemes. -/
@[stacks 0GS2] #check
  (AlgebraicGeometry.Scheme.Hom.finiteEtaleBaseChangeIsEquivalenceOfHenselianPair :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f],
      Functor.IsEquivalence
        (Scheme.finiteEtaleBaseChange (pullback.fst f (Spec.quotientMap I))))
