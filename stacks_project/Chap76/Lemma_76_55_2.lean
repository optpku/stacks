module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
  MorphismProperty

/- Lemma 76.55.2: The property of being at-worst-nodal of relative dimension 1
is preserved under base change. -/
@[stacks 0DSF] #check
  (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}},
      (etaleLocal (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) :
        MorphismProperty (AlgebraicSpace S)).IsStableUnderBaseChange)
