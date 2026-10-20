module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Thickening

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback_isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') [IsThickening i],
      (spacesEtalePullback i).IsEquivalence)
