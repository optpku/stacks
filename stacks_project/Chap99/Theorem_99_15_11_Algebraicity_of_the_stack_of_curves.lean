/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Algebraic
import StacksCheckRecall

/-!
# Theorem 99.15.11

The stack Curves of Situation 99.15.1 is algebraic. For any algebraic space
`B`, the stack `B`-Curves of Remark 99.15.5 is algebraic.
-/

universe u

/- Theorem 99.15.11 (Algebraicity of the stack of curves) (1): the stack of
families of curves over any base scheme is algebraic. -/
@[stacks 0D5A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instAlgebraicStack :
  ∀ (S : AlgebraicGeometry.Scheme.{u}),
    AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.toGroupoids S))

/- Theorem 99.15.11 (Algebraicity of the stack of curves) (2): for every
algebraic space `B` over `S`, the stack of families of curves with a map from
their base scheme to `B` is algebraic. -/
@[stacks 0D5A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.CurvesGroupoidsOver.instAlgebraicStack :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (B : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack
      (AlgebraicGeometry.AlgebraicSpace.Spaces.CurvesGroupoidsOver.toGroupoids B))

