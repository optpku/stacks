/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.SmoothLocal
import StacksCheckRecall

/-!
# Monotonicity of smooth-local-on-source-and-target morphisms of algebraic stacks

If two morphism properties of algebraic spaces are smooth local on the
source-and-target and one implies the other, then the same implication holds
for their lifts to morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Remark 101.16.5: if `P` and `P'` are morphism properties of algebraic
spaces that are smooth local on the source-and-target and `P ≤ P'`, then the
lifts of `P` and `P'` to morphisms of algebraic stacks from Definition 101.16.2
satisfy the same implication. In particular, if `f : X ⟶ Y` has
`hasSmoothLocalAtSourceAndTarget P`, then it has
`hasSmoothLocalAtSourceAndTarget P'`. -/
@[stacks 06PS]
#check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAtSourceAndTarget.of_le :
    ∀ {S : Scheme.{u}} {P P' : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P'] (h : P ≤ P')
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} (hf : AlgebraicStack.hasSmoothLocalAtSourceAndTarget P f),
    AlgebraicStack.hasSmoothLocalAtSourceAndTarget P' f)
