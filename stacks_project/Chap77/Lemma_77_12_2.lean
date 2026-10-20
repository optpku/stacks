/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_12_2_HomotopyLimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.12.2: in Situation 77.12.1, the object
K = Rlim in D_QCoh(𝒪_X) of the stage sheaves ℱ n, equivalently
((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj for an ambient
homotopy limit Klim of the pushforwards of ℱ n in D(𝒪_X), lies in
Dᵇ_QCoh(𝒪_X) and has cohomology sheaves only in degrees ≥ 0. -/
@[stacks 0CX5] #check ProperFlatFormalSystem.coheratorHomotopyLimit_isBounded
