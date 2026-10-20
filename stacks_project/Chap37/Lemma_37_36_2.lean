module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Branch
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 37.36.2 (1): the number of branches at a point is the supremum of the numbers
of irreducible components through the selected points of its elementary étale neighbourhoods. -/
@[stacks 0CB4]
#check
  (AlgebraicGeometry.Scheme.branchNumberAt_eq_iSup_elementaryComponents :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (x : X) (Ah : Type v) [CommRing Ah]
      [Algebra (X.presheaf.stalk x) Ah]
      [IsHenselizationOf (X.presheaf.stalk x) Ah],
      X.branchNumberAt x Ah =
        ⨆ U : AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary X x,
          (TopologicalSpace.irreducibleComponentsAt U.obj.point).encard)

/- Lemma 37.36.2 (2): the number of geometric branches at a point is the supremum of
the numbers of irreducible components through the selected points of its étale neighbourhoods. -/
@[stacks 0CB4]
#check
  (AlgebraicGeometry.Scheme.geometricBranchNumberAt_eq_iSup_etaleComponents :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (x : X) (Ash : Type v) [CommRing Ash]
      [Algebra (X.presheaf.stalk x) Ash]
      [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
      X.geometricBranchNumberAt x Ash =
        ⨆ U : AlgebraicGeometry.Scheme.EtaleNeighborhood X x,
          (TopologicalSpace.irreducibleComponentsAt U.point).encard)

/- Lemma 37.36.2 (3): a scheme is unibranch at a point exactly when every elementary étale
neighbourhood has a unique irreducible component through its selected point. -/
@[stacks 0CB4]
#check
  (AlgebraicGeometry.Scheme.isUnibranchAt_iff_uniqueComponent_elementary :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (x : X),
      X.isUnibranchAt x ↔
        ∀ U : AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary X x,
          ∃! Z, Z ∈ TopologicalSpace.irreducibleComponentsAt U.obj.point)

/- Lemma 37.36.2 (4): a scheme is geometrically unibranch at a point exactly when every
étale neighbourhood has a unique irreducible component through its selected point. -/
@[stacks 0CB4]
#check
  (AlgebraicGeometry.Scheme.isGeometricallyUnibranchAt_iff_uniqueComponent_etale :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (x : X),
      X.isGeometricallyUnibranchAt x ↔
        ∀ U : AlgebraicGeometry.Scheme.EtaleNeighborhood X x,
          ∃! Z : irreducibleComponents U.toEtale.left,
            Z ∈ TopologicalSpace.irreducibleComponentsAt U.point)
