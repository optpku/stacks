/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth

/-!
# Smooth morphisms of algebraic stacks are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom renaming Smooth → RepresentablySmooth

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- A representable smooth morphism of algebraic stacks is locally of finite type. -/
instance of_representable_smooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [RepresentablySmooth f] :
    LocallyOfFiniteType f :=
  sorry

/-- A smooth morphism of algebraic stacks is locally of finite type. -/
instance of_smooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicStack.Smooth f] : LocallyOfFiniteType f := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
