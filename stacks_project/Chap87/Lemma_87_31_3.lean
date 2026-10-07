module

public import stacks_project.Chap87.Lemma_87_31_3_Pullback

/-!
# Base change of proper morphisms of formal algebraic spaces

The base change of a proper morphism of formal algebraic spaces by any
morphism of formal algebraic spaces is again proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.31.3: Proper morphisms of formal algebraic spaces are preserved by
base change. -/
@[stacks 0GBT]
instance proper_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Proper S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
