/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Compactness.Compact

@[expose] public section

universe u

namespace TopologicalSpace

/-- A topological space is quasi-compact if every open cover has a finite subcover,
without any separation assumption. -/
def IsQuasiCompact (X : Type u) [TopologicalSpace X] : Prop :=
  IsCompact (Set.univ : Set X)

end TopologicalSpace
