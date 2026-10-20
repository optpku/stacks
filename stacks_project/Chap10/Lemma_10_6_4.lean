/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
import StacksCheckRecall

/-!
# Lemma 10.6.4

@stack 0561
-/

@[expose] public section

/- Chap10 Lemma 10 6 4: a module finitely presented after restricting scalars to `R` remains
finitely presented over a finite-type `R`-algebra. -/
@[stacks 0561]
#check @Module.FinitePresentation.of_restrictScalars
