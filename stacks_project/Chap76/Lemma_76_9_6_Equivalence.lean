module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Thickening

open AlgebraicGeometry CategoryTheory

universe u

#check
  (@AlgebraicGeometry.AlgebraicSpace.smallEtalePullback.isEquivalence_of_isThickening :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
      [AlgebraicGeometry.AlgebraicSpace.IsThickening i]
      (hf : yoneda.relativelyRepresentable i),
      (AlgebraicGeometry.AlgebraicSpace.smallEtalePullback i hf).IsEquivalence)
