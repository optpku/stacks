/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Operations
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.105.11 (092L)

@stack 092L

Let `A` be a ring and let `B ⟶ C` be a map of `A`-algebras. If `A ⟶ B` and
`A ⟶ C` are weakly etale, then `B ⟶ C` is weakly etale.
-/

/- Lemma 15.105.11: an algebra map between weakly-etale algebras over a common base is weakly
etale. -/
@[stacks 092L "Lemma 15.105.11"]
#check @Algebra.WeaklyEtale.of_tower
