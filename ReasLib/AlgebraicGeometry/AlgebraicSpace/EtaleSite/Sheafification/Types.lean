module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Type-valued weak sheafification exists on the small étale topology of an algebraic space. -/
instance smallEtaleTopology_hasWeakSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) (Type u) :=
  (SmallEtale.Sheafification.adjunction (X := X) (Type u)).isRightAdjoint

end AlgebraicGeometry.AlgebraicSpace
