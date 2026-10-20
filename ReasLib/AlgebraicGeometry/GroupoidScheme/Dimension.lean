/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiberComparison.Field
public import ReasLib.AlgebraicGeometry.GroupoidScheme.OverField
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic

/-!
# Dimensions of groupoid arrow schemes over fields

This module records equidimensionality and dimension comparisons for the arrow scheme of a
groupoid scheme whose object scheme is a field spectrum.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.GroupoidScheme

section FieldBase

variable {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]

/-- The arrow scheme of a groupoid scheme over a field spectrum is equidimensional when its
source and target maps are locally of finite type. -/
theorem equidimensionalSpaceArrow
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] :
    EquidimensionalSpace G.R.left := sorry

/-- The arrow scheme and the stabilizer of a groupoid scheme over a field spectrum have
the same topological Krull dimension when the source and target maps are locally of finite type. -/
theorem topologicalKrullDim_arrow_eq_stabilizer
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] :
    topologicalKrullDim G.R.left = topologicalKrullDim G.stabilizer.X.left.left := sorry

/-- The dimension of the arrow scheme equals its local dimension at every point. -/
theorem topologicalKrullDim_eq_topologicalKrullDimAt
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] (r : G.R.left) :
    topologicalKrullDim G.R.left = topologicalKrullDimAt r := sorry

/-- At every point of the arrow scheme, the field structures induced by the source and target
maps have the same base-field transcendence degree. -/
theorem source_residueFieldTrdegAt_eq_target
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left] (r : G.R.left) :
    SchemeOverField.baseFieldTrdegAt (arrowSourceOverField G uIso) r =
      SchemeOverField.baseFieldTrdegAt (arrowTargetOverField G uIso) r := sorry

/-- At a closed point of the arrow scheme, its dimension equals the Krull dimension of the
local ring. -/
theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_isClosed
    (uIso : G.U.left ≅ Spec (CommRingCat.of k))
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    (r : G.R.left) (h_r : IsClosed ({r} : Set G.R.left)) :
    topologicalKrullDim G.R.left =
      ringKrullDim (SchemeOverField.stalkRing (arrowSourceOverField G uIso) r) := sorry

end FieldBase

end AlgebraicGeometry.GroupoidScheme
