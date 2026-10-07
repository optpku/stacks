module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Fiber

/-!
# Branches of scheme-theoretic fibres

This file characterizes branch counts and unibranch properties of fibres using
irreducible components through points induced by étale neighbourhoods.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- The number of branches of a fibre at the selected point is the supremum of the
numbers of irreducible components through the selected points of fibres of elementary
étale neighbourhoods. -/
@[stacks 0CB5]
theorem branchNumberAt_fiber_eq_iSup_elementaryComponents
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (Ah : Type v) [CommRing Ah]
    [Algebra ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ah]
    [IsHenselizationOf ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ah] :
    (f.fiber (f x)).branchNumberAt (f.asFiber x) Ah =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (irreducibleComponentsAt (EtaleNeighborhood.fiber f U.obj).point).encard := sorry

/-- The number of geometric branches of a fibre at the selected point is the supremum of
the numbers of irreducible components through the selected points of fibres of étale
neighbourhoods. -/
@[stacks 0CB5]
theorem geometricBranchNumberAt_fiber_eq_iSup_etaleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (Ash : Type v) [CommRing Ash]
    [Algebra ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ash]
    [IsStrictHenselizationOf ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ash] :
    (f.fiber (f x)).geometricBranchNumberAt (f.asFiber x) Ash =
      ⨆ U : EtaleNeighborhood X x,
        (irreducibleComponentsAt (EtaleNeighborhood.fiber f U).point).encard := sorry

/-- A fibre is unibranch at the selected point exactly when every elementary étale
neighbourhood has a fibre with a unique irreducible component through its selected point. -/
@[stacks 0CB5]
theorem isUnibranchAt_fiber_iff_uniqueComponent_elementary
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (f.fiber (f x)).isUnibranchAt (f.asFiber x) ↔
      ∀ U : EtaleNeighborhood.Elementary X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (EtaleNeighborhood.fiber f U.obj).point := sorry

/-- A fibre is geometrically unibranch at the selected point exactly when every étale
neighbourhood has a fibre with a unique irreducible component through its selected point. -/
@[stacks 0CB5]
theorem isGeometricallyUnibranchAt_fiber_iff_uniqueComponent_etale
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (f.fiber (f x)).isGeometricallyUnibranchAt (f.asFiber x) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z : irreducibleComponents (EtaleNeighborhood.fiber f U).toEtale.left,
          Z ∈ irreducibleComponentsAt (EtaleNeighborhood.fiber f U).point := sorry

end AlgebraicGeometry.Scheme.Hom
