/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Retracts
import StacksCheckRecall

/-!
# Lemma 15.75.5

@stack 066S

The retract-stability instance and its direct-summand consequence are owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

@[stacks 066S "source direct-summand theorem"]
#check @DerivedCategory.isPerfect_summands_of_biprod

@[stacks 066S "perfect objects are retract-stable"]
#check @DerivedCategory.isPerfect_isStableUnderRetracts

@[stacks 0657 "perfect derived object predicate"]
#check @DerivedCategory.IsPerfect
