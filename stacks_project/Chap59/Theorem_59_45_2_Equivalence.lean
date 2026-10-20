module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.TopologicalInvariance

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isEquivalence_of_universalHomeomorphism :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f],
      (AlgebraicGeometry.Scheme.smallEtalePullback f).IsEquivalence)
