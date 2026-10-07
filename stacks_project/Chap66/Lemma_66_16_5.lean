module

public import stacks_project.Chap66.Lemma_66_16_5_Pullback
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MorphismProperty

/- Lemma 66.16.5: The base change of an étale morphism of algebraic spaces by
any morphism of algebraic spaces is étale. -/
@[stacks 03FU] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.Etale S :
        MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
