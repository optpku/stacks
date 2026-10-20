/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Geometry.Manifold.Complex.MeromorphicFunctionField
import StacksCheckRecall

@[expose] public section

open scoped Manifold Topology

universe u

/-!
Example 9.6.5 (Tag 09FY): the constant functions give an injective algebra map
`ℂ → ℂ(X)`. This is the canonical injection associated to the field structure on the meromorphic
function field.
-/

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

@[stacks 09FY]
#check (algebraMap ℂ (MeromorphicFunctionField X)).injective
