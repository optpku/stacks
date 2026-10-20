module

public import stacks_project.Chap67.Lemma_67_30_4_Pullback
import StacksCheckRecall

/-!
# Base change of flat morphisms of algebraic spaces

The base change of a flat morphism of algebraic spaces by any morphism of
algebraic spaces is again a flat morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.30.4: The base change of a flat morphism is flat. -/
@[stacks 03MO] #check (AlgebraicGeometry.AlgebraicSpace.flat_isStableUnderBaseChange :
  ∀ {S : Scheme.{u}}, CategoryTheory.MorphismProperty.IsStableUnderBaseChange
    (@AlgebraicGeometry.AlgebraicSpace.Flat S :
      CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
