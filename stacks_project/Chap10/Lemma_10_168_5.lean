/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit.Unramified
import StacksCheckRecall

/-!
# Lemma 10.168.5

@stack 0C4F
-/

@[expose] public section

/- Lemma 10.168.5 [stacks 0C4F]: canonical recall.  The reusable owner is
`CommAlgCat.FilteredColimit.Unramified.exists_stage`, stated for an arbitrary
filtered diagram of commutative algebras. -/
@[stacks 0C4F]
#check @CommAlgCat.FilteredColimit.Unramified.exists_stage
