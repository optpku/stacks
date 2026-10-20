/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.1, tag `0BSH`, is the tensor-product base-change instance of
the shared ind-etale ring-map API.

@stack 0BSH
-/

@[stacks 0BSH]
#check @RingHom.IndEtale.Raw.isStableUnderBaseChange

@[stacks 0BSH "ind-etale base-change map"]
#check @RingHom.IndEtale.Raw.baseChange
