/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

/-! # Formal branches through a field-valued point -/

#check (AlgebraicGeometry.AlgebraicStack.FormalBranches :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    Type (u + 1))
