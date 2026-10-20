module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.componentMultiplicity :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X],
    (Y : ClosedSubspace X) → genericPoints Y.X → ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.associatedCycle :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X],
    (Y : ClosedSubspace X) → (Points X → ℤ) → ℤ →
      Function.locallyFinsupp (Points X) ℤ)
