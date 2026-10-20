module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An absolutely locally separated algebraic space is decent. -/
instance instIsDecent_of_isAbsolutelyLocallySeparated {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsAbsolutelyLocallySeparated X] : IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
