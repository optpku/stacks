module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PushforwardAlgebra

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.pushforwardStructureAlgebra :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Sheaf (smallEtaleTopology Y) RingCat.{u})
