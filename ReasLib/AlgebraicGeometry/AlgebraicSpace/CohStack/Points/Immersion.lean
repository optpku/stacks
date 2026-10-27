/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion
public import Mathlib.Topology.Defs.Induced

/-!
# Open immersions on points of lifted algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

namespace Points

variable {S : Scheme.{u}}
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
  [AlgebraicStack X]

/-- An open immersion of algebraic stacks induces an open embedding of their
canonical point spaces. -/
theorem isOpenEmbedding_map
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f] :
    Topology.IsOpenEmbedding (map f) := sorry

end Points

end AlgebraicGeometry.AlgebraicSpace.CohStack
