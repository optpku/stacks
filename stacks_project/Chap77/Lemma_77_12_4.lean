/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_12_4_PseudoCoherentOver
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.12.4: in Situation 77.12.1, let K be as in Lemma 77.12.2,
equivalently ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj for an
ambient homotopy limit Klim of a tower identified with the pushed stage
sheaves ℱ n, including successor maps, in D(𝒪_X). Then K is
pseudo-coherent relative to A, i.e.
ModuleDerived.IsPseudoCoherentOver (toBase X) K. -/
@[stacks 0CX7] #check ProperFlatFormalSystem.coheratorHomotopyLimit_isPseudoCoherentOver
