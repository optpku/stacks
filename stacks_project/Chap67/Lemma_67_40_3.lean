module

public import stacks_project.Chap67.Lemma_67_40_3_Pullback

/-!
# Base change of proper morphisms of algebraic spaces

The base change of a proper morphism of algebraic spaces by any morphism of
algebraic spaces is again proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.40.3: A base change of a proper morphism of algebraic spaces is
proper. -/
@[stacks 04WP]
instance proper_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Proper S : MorphismProperty (AlgebraicSpace S)) := sorry

#check Proper.of_isPullback
#check Proper.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
