module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Branch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme

universe u v

/- Lemma 37.36.3 (1): the number of branches of a fibre at the selected point is the
supremum of the numbers of irreducible components through the selected points of fibres of
elementary étale neighbourhoods. -/
@[stacks 0CB5]
#check (AlgebraicGeometry.Scheme.Hom.branchNumberAt_fiber_eq_iSup_elementaryComponents :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (Ah : Type v) [CommRing Ah]
      [Algebra ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ah]
      [IsHenselizationOf ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ah],
    (f.fiber (f x)).branchNumberAt (f.asFiber x) Ah =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (irreducibleComponentsAt (EtaleNeighborhood.fiber f U.obj).point).encard)

/- Lemma 37.36.3 (2): the number of geometric branches of a fibre at the selected point is
the supremum of the numbers of irreducible components through the selected points of fibres
of étale neighbourhoods. -/
@[stacks 0CB5]
#check (AlgebraicGeometry.Scheme.Hom.geometricBranchNumberAt_fiber_eq_iSup_etaleComponents :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (Ash : Type v) [CommRing Ash]
      [Algebra ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ash]
      [IsStrictHenselizationOf ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) Ash],
    (f.fiber (f x)).geometricBranchNumberAt (f.asFiber x) Ash =
      ⨆ U : EtaleNeighborhood X x,
        (irreducibleComponentsAt (EtaleNeighborhood.fiber f U).point).encard)

/- Lemma 37.36.3 (3): a fibre is unibranch at the selected point exactly when every
elementary étale neighbourhood has a fibre with a unique irreducible component through its
selected point. -/
@[stacks 0CB5]
#check (AlgebraicGeometry.Scheme.Hom.isUnibranchAt_fiber_iff_uniqueComponent_elementary :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    (f.fiber (f x)).isUnibranchAt (f.asFiber x) ↔
      ∀ U : EtaleNeighborhood.Elementary X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (EtaleNeighborhood.fiber f U.obj).point)

/- Lemma 37.36.3 (4): a fibre is geometrically unibranch at the selected point exactly when
every étale neighbourhood has a fibre with a unique irreducible component through its
selected point. -/
@[stacks 0CB5]
#check (AlgebraicGeometry.Scheme.Hom.isGeometricallyUnibranchAt_fiber_iff_uniqueComponent_etale :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    (f.fiber (f x)).isGeometricallyUnibranchAt (f.asFiber x) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z : irreducibleComponents (EtaleNeighborhood.fiber f U).toEtale.left,
          Z ∈ irreducibleComponentsAt (EtaleNeighborhood.fiber f U).point)
