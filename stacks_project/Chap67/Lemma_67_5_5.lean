module

public import stacks_project.Chap67.Lemma_67_5_5_Pullback

/-!
# Base change of surjective morphisms of algebraic spaces

The base change of a surjective morphism of algebraic spaces by any morphism of
algebraic spaces is again a surjective morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.5.5: The base change of a surjective morphism of algebraic spaces is
surjective. -/
@[stacks 03MH]
instance surjective_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Surjective S : MorphismProperty (AlgebraicSpace S)) := sorry

#check Surjective.of_isPullback
#check Surjective.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
