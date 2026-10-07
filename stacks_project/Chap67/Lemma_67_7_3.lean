module

public import stacks_project.Chap67.Definition_67_7_2_Submersive

/-!
# Base change of universally submersive morphisms of algebraic spaces

The base change of a universally submersive morphism of algebraic spaces by any
morphism of algebraic spaces is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.7.3: The base change of a universally submersive morphism of algebraic
spaces by any morphism of algebraic spaces is universally submersive. -/
@[stacks 0CFR]
instance universallySubmersive_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversallySubmersive S : MorphismProperty (AlgebraicSpace S)) := sorry

#check UniversallySubmersive.of_isPullback
#check UniversallySubmersive.pullback_snd

end AlgebraicGeometry.AlgebraicSpace
