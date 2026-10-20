/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal

/-!
# Smooth-local-on-source-and-target morphisms of algebraic stacks

A morphism property of algebraic spaces that is smooth local on the
source-and-target lifts to morphisms of algebraic stacks by testing it on a
smooth algebraic-space presentation square with surjective source atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget_def :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    AlgebraicStack.hasSmoothLocalAtSourceAndTarget P f ↔
      AlgebraicStack.existsSurjectiveSmoothSquare P f)
