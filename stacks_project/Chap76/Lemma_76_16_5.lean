module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.16.5: A base change of a formally étale morphism is formally
étale. -/
@[stacks 0613] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@FormallyEtale S : MorphismProperty (AlgebraicSpace S)))
