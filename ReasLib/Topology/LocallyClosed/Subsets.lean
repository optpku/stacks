/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled locally closed subsets

This module provides the locally closed analogue of the bundled carriers
`TopologicalSpace.Opens` and `TopologicalSpace.Closeds`.
-/

@[expose] public section

open Set

universe u

namespace TopologicalSpace

/-- A locally closed subset, bundled with its locally closedness property. -/
@[stacks 0F2L "bundled locally closed subset"]
abbrev LocallyCloseds (X : Type u) [TopologicalSpace X] :=
  { T : Set X // IsLocallyClosed T }

end TopologicalSpace
