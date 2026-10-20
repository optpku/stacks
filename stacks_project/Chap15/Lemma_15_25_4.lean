/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Graded
import StacksCheckRecall

/-!
# Lemma 15.25.4

@stack 053D

The two graded flatness criteria are owned by the reusable graded finite-presentation API.  The
module clause does not impose the algebra-flatness hypothesis belonging only to the first clause.
-/

@[expose] public section

/- Lemma 15.25.4 (1): a flat finite-type graded algebra with finite degree-zero part is finitely
presented when finitely many prime localizations detect equality. -/
@[stacks 053D "Lemma 15.25.4 (1)"]
#check @Algebra.FinitePresentation.ofGradedFlat

/- Lemma 15.25.4 (2): a finite graded module over the same graded algebra is finitely presented
when the module is flat over the base. -/
@[stacks 053D "Lemma 15.25.4 (2)"]
#check @Module.FinitePresentation.ofGradedFlat
