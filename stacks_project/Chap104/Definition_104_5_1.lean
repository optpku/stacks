/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh
import StacksCheckRecall

/- Definition 104.5.1: for an algebraic stack `X`, the derived category of
`𝒪_X`-modules with quasi-coherent cohomology sheaves is the Verdier quotient
`D_{LQCoh^{fbc}}(𝒪_X) / D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)`. -/
@[stacks 07B6] #check AlgebraicGeometry.AlgebraicStack.DerivedQCoh
