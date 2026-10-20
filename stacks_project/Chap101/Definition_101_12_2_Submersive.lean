/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Submersive

/-!
# Submersive morphisms of algebraic stacks

Submersiveness is the quotient-map property of the induced map on canonical
point spaces; universal submersiveness requires this after every base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.pointsIsQuotientMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)
