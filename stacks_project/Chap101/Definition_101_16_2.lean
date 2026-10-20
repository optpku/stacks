/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.16.2: let `P` be a property of morphisms of algebraic spaces
which is smooth local on the source-and-target. We say a morphism `f : X ⟶ Y`
of algebraic stacks has property `P` if the equivalent conditions of Lemma
101.16.1 hold. -/
@[stacks 06FN] #check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y), Prop)
