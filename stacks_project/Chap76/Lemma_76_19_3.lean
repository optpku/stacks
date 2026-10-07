module

public import stacks_project.Chap76.Lemma_76_19_3_Pullback
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.19.3: A base change of a formally smooth morphism is formally
smooth. -/
@[stacks 061F] #check
  (FormallySmooth.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@FormallySmooth S : MorphismProperty (AlgebraicSpace S)))
