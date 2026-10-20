/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.Composition
import StacksCheckRecall

/-!
# Composition of smooth-local-on-source-and-target morphisms of algebraic stacks

If a morphism property of algebraic spaces is smooth local on the
source-and-target and stable under composition, then so is its lift to
morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Remark 101.16.3: if a morphism property `P` of algebraic spaces is smooth
local on the source-and-target and stable under composition, then the lift of
`P` to morphisms of algebraic stacks from Definition 101.16.2 is also stable
under composition. In particular, if `f : X ⟶ Y` and `g : Y ⟶ Z` have
`hasSmoothLocalAtSourceAndTarget P`, then so does `f ≫ g` (source `g ∘ f`). -/
@[stacks 06FP] #check
  (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget.comp :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : AlgebraicStack.hasSmoothLocalAtSourceAndTarget P f)
    (hg : AlgebraicStack.hasSmoothLocalAtSourceAndTarget P g),
    AlgebraicStack.hasSmoothLocalAtSourceAndTarget P (f ≫ g))
