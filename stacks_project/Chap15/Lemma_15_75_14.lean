/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Regular
import StacksCheckRecall

/-!
# Perfect complexes over regular rings

Lemma 15.75.14 (066Z) identifies perfect modules with finite modules and perfect derived objects
with bounded objects having finite homology. The reusable statements are owned by ReasLib.

@stack 066Z
-/

@[expose] public section

@[stacks 066Z "Lemma 15.75.14 (1)"]
#check @CategoryTheory.ModuleCat.isPerfect_iff_finite

@[stacks 066Z "Lemma 15.75.14 (2)"]
#check @CategoryTheory.DerivedCategory.isPerfect_iff_bounded_and_finite_homology
