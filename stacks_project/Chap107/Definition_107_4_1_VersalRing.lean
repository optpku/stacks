/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped Bicategory

universe u

/-! # Versal rings at field-valued points -/

#check (AlgebraicGeometry.AlgebraicStack.IsVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    CompleteLocalSAlgebra S → Prop)

#check (AlgebraicGeometry.AlgebraicStack.StageOneMarking :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S},
    AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X →
      GroupoidsOver.FormalObject X → Type u)
