/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType

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

/-- The composition of a pair of finite type morphisms of algebraic stacks is
of finite type. -/
@[stacks 06FT]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) :=
  sorry

end FiniteType

namespace LocallyOfFiniteType

/-- The composition of a pair of locally of finite type morphisms of algebraic
stacks is locally of finite type. -/
@[stacks 06FT]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicStack
