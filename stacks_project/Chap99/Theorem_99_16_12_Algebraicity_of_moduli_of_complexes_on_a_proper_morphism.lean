/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Algebraic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Theorem 99.16.12 (Algebraicity of moduli of complexes on a proper morphism).
For a proper, flat morphism of finite presentation between algebraic spaces over
`S`, the moduli stack of complexes is algebraic over `S`. -/
@[stacks 0DLN] #check
  (AlgebraicGeometry.AlgebraicSpace.Complexes.instAlgebraicStack :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [Proper f] [Flat f] [FinitePresentation f],
      AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack
        (AlgebraicGeometry.AlgebraicSpace.Complexes.toGroupoids f))
