/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.MittagLeffler.CountablyGenerated

@[expose] public section

/-!
Chapter 10, Lemma 10.92.2 is provided by the reusable countably generated Mittag-Leffler
approximation API.

@stack 05D2
-/

@[stacks 05D2]
#check Module.MittagLeffler.exists_finitePresentation_factorization

@[stacks 05D2 "directed-system factorization"]
#check Module.IsMittagLefflerDirectedSystem.exists_factorization
