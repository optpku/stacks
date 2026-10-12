/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Cardinal bounds from dense maps into Hausdorff spaces
-/

@[expose] public section

universe u v

open Cardinal

namespace DenseRange

variable {X : Type u} {Y : Type v} [TopologicalSpace Y] [T2Space Y] {f : X → Y}

/-- A dense map into a Hausdorff space bounds the cardinality of the codomain by the double
powerset of the domain. -/
@[stacks 0909 "Hausdorff cardinal bound from a dense map"]
theorem cardinalMk_le_doublePowerset (h : DenseRange f) :
    lift.{u} #Y ≤ lift.{v} #(Set (Set X)) := sorry

end DenseRange
