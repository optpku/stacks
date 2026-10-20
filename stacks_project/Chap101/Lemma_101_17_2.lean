module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType.Composition
import StacksCheckRecall

/-!
# Composition of finite type morphisms of algebraic stacks

The composition of a pair of finite type morphisms of algebraic stacks is of
finite type, and the composition of a pair of locally of finite type morphisms
of algebraic stacks is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.17.2: The composition of finite type morphisms of algebraic stacks
is of finite type. The same holds for locally of finite type. -/
@[stacks 06FT] #check (AlgebraicGeometry.AlgebraicStack.FiniteType.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicStack.FiniteType f] [AlgebraicStack.FiniteType g],
    AlgebraicStack.FiniteType (f ≫ g))

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicStack.LocallyOfFiniteType f] [AlgebraicStack.LocallyOfFiniteType g],
    AlgebraicStack.LocallyOfFiniteType (f ≫ g))
