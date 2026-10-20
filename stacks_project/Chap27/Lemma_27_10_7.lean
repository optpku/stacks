/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap27.Lemma_27_10_7_Counit
import StacksCheckRecall

@[expose] public section

/- Lemma 27.10.7: the associated sheaf of
`⨁ n : Int, Γ(Proj calA, F(n))` has a functorial counit to `F`, whose degree-zero map is the
identity under the canonical identification `F(0) ≅ F`. -/
@[stacks 0B5I] #check AlgebraicGeometry.ProjTwistedGlobalSections.counit_degreeZero
