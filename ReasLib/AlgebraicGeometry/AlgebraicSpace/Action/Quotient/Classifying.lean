module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Trivial

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.QuotientStack

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Classifying

/-- Forgetting the equivariant map to the trivial action on the base gives an
equivalence between the torsor-with-map quotient and the torsor stack. -/
instance toTorsors_trivialAction_isEquivalence {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (GroupAction.toTorsors G (trivialAction G)).toBasedFunctor.IsEquivalence := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Classifying
