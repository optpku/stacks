/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.IsSmoothSurjectivePresentation :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {U V : AlgebraicSpace S}
      (f : X ⟶ Y) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      Prop)
