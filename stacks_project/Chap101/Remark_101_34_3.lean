/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.Composition
import StacksCheckRecall

/-!
# Composition of étale-smooth-local-on-source-and-target DM morphisms

If a morphism property of algebraic spaces is étale-smooth local on the
source-and-target and stable under composition, then so is its lift to DM
morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 101.34.3: if a morphism property `P` of algebraic spaces is
étale-smooth local on the source-and-target and stable under composition, then
the lift of `P` to DM morphisms of algebraic stacks from Definition 101.34.2 is
also stable under composition. In particular, if `f : X ⟶ Y` and `g : Y ⟶ Z`
are DM and have `hasEtaleSmoothLocalAtSourceAndTarget P`, then so does `f ≫ g`
(source `g ∘ f`). -/
@[stacks 0CIH] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget.comp :
  ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] {f : X ⟶ Y} {g : Y ⟶ Z} [DM f] [DM g]
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f)
    (hg : hasEtaleSmoothLocalAtSourceAndTarget P g),
    hasEtaleSmoothLocalAtSourceAndTarget P (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
