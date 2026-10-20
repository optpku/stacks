/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Graded
import StacksCheckRecall

/-!
# Lemma 15.25.3

@stack 053C

The local weighted-graded finite-presentation theorem is owned by the reusable graded
finite-presentation API.
-/

@[expose] public section

/- Lemma 15.25.3: a finite graded module over a positively weighted polynomial ring over a local
ring is finitely presented when it is flat over the base. -/
@[stacks 053C "Lemma 15.25.3"]
#check @Module.FinitePresentation.ofWeightedGradedFlat
