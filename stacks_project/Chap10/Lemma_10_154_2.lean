/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Composition
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.2, tag `0BSI`, is the canonical composition theorem for
ind-etale ring maps.

@stack 0BSI
-/

@[stacks 0BSI]
#check @RingHom.IndEtale.Raw.comp
