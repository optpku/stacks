module

public import stacks_project.Chap67.Lemma_67_30_4_Pullback

/-!
# Base change of flat morphisms of algebraic spaces

The base change of a flat morphism of algebraic spaces by any morphism of
algebraic spaces is again a flat morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.4: The base change of a flat morphism is flat. -/
@[stacks 03MO]
instance flat_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Flat S : MorphismProperty (AlgebraicSpace S)) := sorry

#check Flat.of_isPullback
#check Flat.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
