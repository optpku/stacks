module

public import stacks_project.Chap101.Definition_101_37_1_FiniteType

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

namespace AlgebraicGeometry.AlgebraicStack

namespace FiniteType

/-- Lemma 101.17.2 (1): The composition of a pair of finite type morphisms of
algebraic stacks is of finite type. -/
@[stacks 06FT]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) :=
  sorry

end FiniteType

namespace LocallyOfFiniteType

/-- Lemma 101.17.2 (2): The composition of a pair of locally of finite type
morphisms of algebraic stacks is locally of finite type. -/
@[stacks 06FT]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicStack
