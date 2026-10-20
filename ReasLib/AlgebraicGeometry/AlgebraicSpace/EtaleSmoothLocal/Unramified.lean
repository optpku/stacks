module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Unramified morphisms of algebraic spaces are étale-smooth local on the
source-and-target. -/
instance Unramified.isEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget (@Unramified S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
