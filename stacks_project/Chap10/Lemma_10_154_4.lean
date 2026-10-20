/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.4, tag `0GIM`, is the directed-arrow-colimit form of the
shared ind-etale closure API.

@stack 0GIM
-/

@[stacks 0GIM]
#check @RingHom.IndEtale.Raw.colimit_of_directed
