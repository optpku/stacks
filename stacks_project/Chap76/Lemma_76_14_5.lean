module

public import stacks_project.Chap76.Lemma_76_14_5_Pullback
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.14.5: A base change of a formally unramified morphism is formally
unramified. -/
@[stacks 0600] #check
  (FormallyUnramified.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified S : MorphismProperty (AlgebraicSpace S)))
