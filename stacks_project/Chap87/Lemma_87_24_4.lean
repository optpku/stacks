module

public import stacks_project.Chap87.Lemma_87_24_4_FiniteType
public import stacks_project.Chap87.Lemma_87_24_4_Pullback

/-!
# Base change of finite-type morphisms of formal algebraic spaces

The base change of a finite-type morphism of formal algebraic spaces by any
morphism of formal algebraic spaces is again of finite type. The same holds
for morphisms locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.24.4 (1): The base change of a finite type morphism of formal
algebraic spaces is finite type. -/
@[stacks 0AQ5]
instance finiteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

/-- Lemma 87.24.4 (2): The base change of a locally of finite type morphism of
formal algebraic spaces is locally of finite type. -/
@[stacks 0AQ5]
instance locallyOfFiniteType_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
