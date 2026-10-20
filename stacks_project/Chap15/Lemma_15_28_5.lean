/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Homotopy
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.28.5

@stack 0626
-/

/-!
# Scalar null-homotopies on Koszul complexes

The reusable owner is the canonical left-wedge homotopy in
`ReasLib.RingTheory.Sequence.Koszul.Homotopy`.
-/

/- Lemma 15.28.5 (Tag 0626): multiplication by the value of a linear form on its Koszul complex
is homotopic to zero via left exterior multiplication. -/
@[stacks 0626 "scalar multiplication on a Koszul complex is null-homotopic"]
#check @KoszulComplex.scalarHomotopyZero

#check @KoszulComplex.leftWedge
#check @KoszulComplex.leftWedgeHomotopyComponent
#check @KoszulComplex.smulId_eq_nullHomotopicMap
