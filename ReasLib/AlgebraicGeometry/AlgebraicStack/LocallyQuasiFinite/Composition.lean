/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-!
# Composition of locally quasi-finite morphisms of algebraic stacks

A composition of locally quasi-finite morphisms of algebraic stacks is
locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- A composition of locally quasi-finite morphisms of algebraic stacks is
locally quasi-finite. -/
@[stacks 06UD]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite f] [LocallyQuasiFinite g] :
    LocallyQuasiFinite (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
