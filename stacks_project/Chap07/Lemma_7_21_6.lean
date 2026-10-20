/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits

/-!
# Lemma 7.21.6

The topology-independent Kan-extension criterion and its site-level
sheaf-pullback consequence are reusable ReasLib APIs.  This source file keeps
only the labeled recall.
-/

@[expose] public section

/- Lemma 7.21.6 (00XS): the lower shriek along a continuous functor that preserves pullbacks and
equalizers preserves finite connected limits of `Type`-valued sheaves. -/
@[stacks 00XS] #check @CategoryTheory.Functor.SheafPullback.Pullbacks.ofEqualizers

#check @CategoryTheory.Functor.SheafPullback.Pullbacks.preservesPullbacks
#check @CategoryTheory.Functor.SheafPullback.Pullbacks.preservesEqualizers
