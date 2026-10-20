module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.CategoryTheory.Sites.Topos.Point.TypeImage

/-!
# Points of the small étale topos of an algebraic space

Every point of the small étale site or topos of an algebraic space is represented,
up to a natural isomorphism of fiber functors, by a geometric point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Every point of the small étale site of an algebraic space is isomorphic, as a fiber
functor, to the site point associated to a geometric point. -/
theorem exists_iso_toSmallEtalePoint (p : (smallEtaleTopology X).Point.{u}) :
    ∃ xbar : GeometricPoint X,
      Nonempty (p.fiber ≅ (toSmallEtalePoint xbar).fiber) :=
  sorry

/-- The inverse image of every point of the small étale topos of an algebraic space is
naturally isomorphic to the sheaf fiber functor at a geometric point. -/
theorem exists_iso_stalkFunctor
    (p : MorphismOfTopoiIn (smallEtaleTopology X) typesGrothendieckTopology.{u + 1}) :
    ∃ xbar : GeometricPoint X,
      Nonempty
        (p.typeInverseImage ≅
          ((toSmallEtalePoint xbar).sheafFiber :
            Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
