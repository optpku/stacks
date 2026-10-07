module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType

/-!
# Composition of finite type morphisms of formal algebraic spaces

The composition of a pair of finite type morphisms of formal algebraic
spaces is of finite type, and the same holds for morphisms locally of
finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.24.3 (1): The composition of finite type morphisms of formal
algebraic spaces is of finite type. -/
@[stacks 0AQ4]
instance finiteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- The composition of finite type morphisms of formal algebraic spaces is of
finite type. -/
instance finiteType_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) := sorry

/-- Lemma 87.24.3 (2): The composition of locally of finite type morphisms of
formal algebraic spaces is locally of finite type. -/
@[stacks 0AQ4]
instance locallyOfFiniteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFiniteType S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)) := sorry

/-- The composition of locally of finite type morphisms of formal algebraic
spaces is locally of finite type. -/
instance locallyOfFiniteType_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
