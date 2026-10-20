/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

@[expose] public section

open CategoryTheory Limits

/- Lemma 26.23.5: a base change of a monomorphism is a monomorphism. -/
@[stacks 02YC] #check pullback.snd_of_mono
