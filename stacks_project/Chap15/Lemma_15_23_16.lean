/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.16

@stack 0EBA

The two consequences of finite reflexivity are recalled from the shared depth and Serre-condition
API.
-/

@[expose] public section

/- Lemma 15.23.16 (1): at a prime where the localized ring has depth at least two, a finite
reflexive module also has localized depth at least two. -/
@[stacks 0EBA "Lemma 15.23.16 (1)"]
#check @Module.IsReflexive.moduleDepth_localizationAtPrime_ge_two

/- Lemma 15.23.16 (2): a finite reflexive module over an `(S₂)` ring satisfies module `(S₂)`. -/
@[stacks 0EBA "Lemma 15.23.16 (2)"]
#check @Module.IsReflexive.instSerreConditionSTwo
