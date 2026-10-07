module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.CategoryTheory.Sites.Topos.Point.TypeImage

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- Every point of the small étale site of a scheme is isomorphic, as a fiber functor,
to the canonical site point associated to a geometric point. -/
theorem exists_iso_toSmallEtalePoint (p : (smallEtaleTopology S).Point) :
    ∃ s : GeometricPoint S, Nonempty (p.fiber ≅ (toSmallEtalePoint s).fiber) := sorry

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}}

/-- The inverse image of every point of the small étale topos of a scheme is naturally
isomorphic to the sheaf stalk functor at a geometric point. -/
theorem exists_iso_stalkFunctor
    (p : MorphismOfTopoiIn (smallEtaleTopology S) typesGrothendieckTopology.{u + 1}) :
    ∃ s : Scheme.GeometricPoint S,
      Nonempty (p.typeInverseImage ≅
        ((Scheme.GeometricPoint.toSmallEtalePoint s).sheafFiber :
          Sheaf (smallEtaleTopology S) (Type (u + 1)) ⥤ Type (u + 1))) := sorry

end AlgebraicGeometry.Scheme.Etale
