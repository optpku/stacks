module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
import StacksCheckRecall

/-!
# Composition of finite type morphisms of formal algebraic spaces

The composition of a pair of finite type morphisms of formal algebraic
spaces is of finite type, and the same holds for morphisms locally of
finite type.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 87.24.3: The composition of finite type morphisms of formal algebraic
spaces is of finite type. The same holds for locally of finite type. -/
@[stacks 0AQ4] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.finiteType_isStableUnderComposition :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.FormalAlgebraicSpace.FiniteType S :
          CategoryTheory.MorphismProperty ((CategoryTheory.Over S)ᵒᵖ ⥤ Type u)))

#check
  (AlgebraicGeometry.FormalAlgebraicSpace.locallyOfFiniteType_isStableUnderComposition :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType S :
          CategoryTheory.MorphismProperty ((CategoryTheory.Over S)ᵒᵖ ⥤ Type u)))
