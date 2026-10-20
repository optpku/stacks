/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.15

@stack 0AVA

The prime-local reflexivity-or-depth criterion is exposed by the shared reflexive-module owner.
-/

@[expose] public section

/- Lemma 15.23.15: a finite module over a Noetherian domain is reflexive exactly when every
prime localization is reflexive or has depth at least two. -/
@[stacks 0AVA "Lemma 15.23.15"]
#check @Module.IsReflexive.iff_forall_localization_or_depth_ge_two
