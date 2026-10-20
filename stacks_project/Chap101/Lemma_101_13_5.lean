/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed.LocalAtTarget

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.13.5: A morphism of algebraic stacks is universally closed iff
all scheme-valued base-change projections are closed on points, iff all affine
scheme-valued base-change projections are closed on points, iff some surjective
smooth algebraic-space atlas of the target has universally closed base change. -/
@[stacks 0CL3] #check (AlgebraicGeometry.AlgebraicStack.UniversallyClosed.tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    List.TFAE [UniversallyClosed f, Closed.forallScheme f, Closed.forallAffine f,
      UniversallyClosed.existsSmoothOnTarget f])
