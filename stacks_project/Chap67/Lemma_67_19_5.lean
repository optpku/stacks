module

public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective

/-!
# Base change of universally injective morphisms of algebraic spaces

The base change of a universally injective morphism of algebraic spaces by any
morphism of algebraic spaces is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.19.5: The base change of a universally injective morphism of algebraic
spaces by any morphism of algebraic spaces is universally injective. -/
@[stacks 03MW]
instance universallyInjective_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversallyInjective S : MorphismProperty (AlgebraicSpace S)) := sorry

#check UniversallyInjective.of_isPullback

end AlgebraicGeometry.AlgebraicSpace
