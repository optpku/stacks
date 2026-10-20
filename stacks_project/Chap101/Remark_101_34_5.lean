/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal
import StacksCheckRecall

/-!
# Monotonicity of étale-smooth-local-on-source-and-target morphisms of algebraic stacks

If two morphism properties of algebraic spaces are étale-smooth local on the
source-and-target and one implies the other, then the same implication holds
for their lifts to morphisms of algebraic stacks.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Remark 101.34.5: if `P` and `P'` are morphism properties of algebraic
spaces that are étale-smooth local on the source-and-target and `P ≤ P'`, then
the lifts of `P` and `P'` to morphisms of algebraic stacks from
Definition 101.34.2 satisfy the same implication. In particular, if
`f : X ⟶ Y` has `hasEtaleSmoothLocalAtSourceAndTarget P`, then it has
`hasEtaleSmoothLocalAtSourceAndTarget P'`. -/
@[stacks 0CIJ] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget.of_le :
    ∀ {S : Scheme.{u}} {P P' : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P'] (h : P ≤ P')
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y} (hf : hasEtaleSmoothLocalAtSourceAndTarget P f),
    hasEtaleSmoothLocalAtSourceAndTarget P' f)
