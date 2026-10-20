module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Pushforward

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.K0'.pushforward :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.IsProper f],
      AlgebraicGeometry.Scheme.K0' X →+ AlgebraicGeometry.Scheme.K0' Y)
