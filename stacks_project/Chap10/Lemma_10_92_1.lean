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
Chapter 10, Lemma 10.92.1 is provided by the reusable countable-subpresentation API for
Mittag-Leffler modules.  Its minimal core only assumes tail factorization of the diagram.

@stack 059W
-/

@[stacks 059W]
#check @Module.MittagLeffler.exists_countable_subpresentation

@[stacks 059W "directed-system countable subpresentation"]
#check @Module.IsMittagLefflerDirectedSystem.exists_countable_subpresentation

@[stacks 059W "tail-factorization countable subpresentation"]
#check @CategoryTheory.Functor.HasTailFactorization.exists_countable_subpresentation
