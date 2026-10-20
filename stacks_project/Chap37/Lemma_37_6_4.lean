module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.BaseChange
import StacksCheckRecall

/- Lemma 37.6.4: A base change of a formally unramified morphism is formally
unramified. -/
@[stacks 02HB] #check
  (AlgebraicGeometry.FormallyUnramified.isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      @AlgebraicGeometry.FormallyUnramified)
