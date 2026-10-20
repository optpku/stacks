/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.WLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.2.4: a closed subset of a w-local spectral space is w-local. -/
@[stacks 096B] #check (IsClosed.wLocal : ∀ {X : Type u} [TopologicalSpace X]
  [WLocalSpace X] {Y : Set X} [IsClosed Y], WLocalSpace Y)
