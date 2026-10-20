module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.19.3: A base change of a formally smooth morphism is formally
smooth. -/
@[stacks 061F] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@FormallySmooth S : MorphismProperty (AlgebraicSpace S)))
