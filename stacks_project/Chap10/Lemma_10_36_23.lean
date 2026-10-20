/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
import StacksCheckRecall

/-!
# Lemma 10.36.23

@stack 0564
-/

@[expose] public section

/- Lemma 10.36.23: finite presentation is unchanged by restriction of scalars along a finite,
finitely presented algebra. -/
@[stacks 0564]
#check @Module.FinitePresentation.iff_restrictScalars_of_finite
