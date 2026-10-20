/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.AlgebraicStack
import StacksCheckRecall

/-!
# Theorem 99.14.15

The stack Polarized of Situation 99.14.1 is algebraic. For any algebraic space
`B`, the stack `B`-Polarized of Remark 99.14.5 is algebraic.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Theorem 99.14.15 (Algebraicity of the stack of polarized schemes)
The stack of polarized proper schemes is algebraic. For every algebraic space
`B` over `Spec ℤ`, the stack of polarized families with a base map to `B` is
also algebraic. -/
@[stacks 0D4X]
#check (AlgebraicGeometry.Polarized.instAlgebraicStack :
  AlgebraicStack AlgebraicGeometry.Polarized.toGroupoidsOverSpecZ.{u})

#check (AlgebraicGeometry.Polarized.polarizedOver.instAlgebraicStack :
  ∀ B : AlgebraicSpace AlgebraicGeometry.Polarized.specZ.{u},
    AlgebraicStack (AlgebraicGeometry.Polarized.polarizedOver.toGroupoids B))
