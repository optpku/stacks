module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 58.17.2: If completion is an equivalence on finite locally free objects,
then restriction along the closed subscheme is an equivalence on finite étale schemes. -/
@[stacks 0EL9] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_isEquivalence_of_completion :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
      [Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.CoherentCompletion.onFiniteLocallyFreeToFiniteLocallyFree I)],
      Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.finiteEtaleBaseChange I.subschemeι))
