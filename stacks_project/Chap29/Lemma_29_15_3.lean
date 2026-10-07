module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.15.3 (1): the composition of two morphisms which are locally of finite type is locally of finite type. -/
@[stacks 01T3] #check
  (locallyOfFiniteType_comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType f] [LocallyOfFiniteType g], LocallyOfFiniteType (f ≫ g))

/- Lemma 29.15.3 (2): the composition of two morphisms of finite type is of finite type. -/
@[stacks 01T3] #check
  (Scheme.Hom.FiniteType.comp :
    ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
      Scheme.Hom.FiniteType f → Scheme.Hom.FiniteType g → Scheme.Hom.FiniteType (f ≫ g))
