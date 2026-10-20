/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective
public import stacks_project.Chap87.Definition_87_25_1_Surjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 87.25.1: a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` is surjective if it induces a surjective morphism
`reduction X ⟶ reduction Y` of underlying reduced algebraic spaces. -/
@[stacks 0GHP] #check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.Surjective :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y],
    AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X →
      AlgebraicGeometry.FormalAlgebraicSpace.ReductionData Y → (X ⟶ Y) → Prop)
