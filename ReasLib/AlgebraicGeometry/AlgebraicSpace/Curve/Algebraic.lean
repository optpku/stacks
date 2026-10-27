/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GroupoidsOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic

/-!
# Algebraicity of stacks of curves

The stack of families of curves and the stack of such families with a map from
their base scheme to an algebraic space are algebraic.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The stack of flat, proper, finitely presented families of algebraic spaces
of relative dimension at most one over schemes over `S` is algebraic. -/
instance Curves.instAlgebraicStack (S : Scheme.{u}) :
    CohStack.AlgebraicStack (Curves.toGroupoids S) := sorry

/-- The stack of families of curves equipped with a map from their base scheme
to an algebraic space `B` over `S` is algebraic. -/
instance CurvesGroupoidsOver.instAlgebraicStack {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CohStack.AlgebraicStack (CurvesGroupoidsOver.toGroupoids B) := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
