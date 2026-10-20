/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Homotopy.Cofiber
import StacksCheckRecall

/-!
# Adjoining a scalar as a Koszul homotopy cofiber

@stack 0628
-/

@[expose] public section

/- Lemma 15.28.7: adjoining multiplication by a scalar to a linear form identifies the new
Koszul complex with the homotopy cofiber of scalar multiplication on the original complex. -/
@[stacks 0628 "Lemma 15.28.7"]
#check @KoszulComplex.Cofiber.coprodScalarIso

#check @KoszulComplex.Cofiber.succSplitHom
#check @KoszulComplex.Cofiber.succSplitInv
#check @KoszulComplex.Cofiber.componentIso
