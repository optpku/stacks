/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.Topology.IrreducibleComponents.AtPoint
public import ReasLib.Data.Set.Card

/-!
# Branches through étale neighbourhoods

This file characterizes branch counts and unibranch properties at a scheme
point using irreducible components through points of étale neighbourhoods.
-/

@[expose] public section

open TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- The branch number at a point is the supremum of the numbers of irreducible components
through the selected points of its elementary étale neighbourhoods. -/
@[stacks 0CB4]
theorem branchNumberAt_eq_iSup_elementaryComponents
    {X : Scheme.{u}} (x : X) (Ah : Type v) [CommRing Ah]
    [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (irreducibleComponentsAt U.obj.point).encard := sorry

/-- The geometric branch number at a point is the supremum of the numbers of irreducible
components through the selected points of its étale neighbourhoods. -/
@[stacks 0CB4]
theorem geometricBranchNumberAt_eq_iSup_etaleComponents
    {X : Scheme.{u}} (x : X) (Ash : Type v) [CommRing Ash]
    [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash =
      ⨆ U : EtaleNeighborhood X x,
        (irreducibleComponentsAt U.point).encard := sorry

/-- A scheme is unibranch at a point exactly when every elementary étale neighbourhood has
a unique irreducible component through its selected point. -/
@[stacks 0CB4]
theorem isUnibranchAt_iff_uniqueComponent_elementary {X : Scheme.{u}} (x : X) :
    X.isUnibranchAt x ↔
      ∀ U : EtaleNeighborhood.Elementary X x,
        ∃! Z, Z ∈ irreducibleComponentsAt U.obj.point := sorry

/-- A scheme is geometrically unibranch at a point exactly when every étale neighbourhood
has a unique irreducible component through its selected point. -/
@[stacks 0CB4]
theorem isGeometricallyUnibranchAt_iff_uniqueComponent_etale
    {X : Scheme.{u}} (x : X) :
    X.isGeometricallyUnibranchAt x ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z : irreducibleComponents U.toEtale.left,
          Z ∈ irreducibleComponentsAt U.point := sorry

end AlgebraicGeometry.Scheme
