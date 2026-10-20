/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.Composition

/-!
# Composition of quasi-finite morphisms of algebraic stacks

A composition of quasi-finite morphisms of algebraic stacks is quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-- A composition of quasi-finite morphisms of algebraic stacks is quasi-finite. -/
@[stacks 0G2N]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiFinite f] [QuasiFinite g] :
    QuasiFinite (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiFinite
