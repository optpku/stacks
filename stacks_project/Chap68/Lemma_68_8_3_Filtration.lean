module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Stratification

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.stratumPoints :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    (ℕ → AlgebraicGeometry.AlgebraicSpace.OpenSubspace X) → ℕ →
      Set (AlgebraicGeometry.AlgebraicSpace.Points X))
