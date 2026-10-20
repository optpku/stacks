module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Decency of affine algebraic spaces

Affine algebraic spaces are decent and therefore have residue fields.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine algebraic space is decent. -/
instance instIsDecent_of_isAffine {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAffine X] : IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
