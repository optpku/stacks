/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension

/-!
# Proper intersections of closed subsets

Proper intersection for closed subsets is expressed by an additive Krull-dimension inequality.
-/

@[expose] public section

universe u

namespace TopologicalSpace.Closeds

variable {X : Type u} [TopologicalSpace X]

/-- Two closed subsets intersect properly when their intersection has at most the expected
topological Krull dimension. -/
def IntersectProperly (W V : Closeds X) : Prop :=
  topologicalKrullDim (W ⊓ V : Closeds X) + topologicalKrullDim X ≤
    topologicalKrullDim W + topologicalKrullDim V

/-- Proper intersection of closed subsets is characterized by the expected-dimension
inequality. -/
theorem intersectProperly_iff (W V : Closeds X) :
    IntersectProperly W V ↔
      topologicalKrullDim (W ⊓ V : Closeds X) + topologicalKrullDim X ≤
        topologicalKrullDim W + topologicalKrullDim V := sorry

/-- Proper intersection of closed subsets is symmetric. -/
theorem intersectProperly_comm (W V : Closeds X) :
    IntersectProperly W V ↔ IntersectProperly V W := sorry

end TopologicalSpace.Closeds
