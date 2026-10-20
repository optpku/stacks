/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Dimension

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

#check
  (GroupScheme.instEquidimensionalSpace :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G],
      EquidimensionalSpace G.left)

#check
  (GroupScheme.topologicalKrullDim_eq_topologicalKrullDimAt :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G]
      (g : G.left),
      topologicalKrullDim G.left = topologicalKrullDimAt g)

#check
  (GroupScheme.topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [LocallyAlgebraic G]
      (g : G.left),
      IsClosed ({g} : Set G.left) →
        topologicalKrullDim G.left = ringKrullDim (SchemeOverField.stalkRing G g))
