/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.«104_5_1_1_Homology»
public import stacks_project.Chap104.«104_5_1_1_Reflector»
import StacksCheckRecall

/- 104.5.1.1 The cohomological functor
`H^i : D_QCoh(𝒪_X) ⟶ QCoh(𝒪_X)` on an algebraic stack. -/
@[stacks 07B7] #check AlgebraicGeometry.AlgebraicStack.DerivedQCoh.homologyFunctor
