module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Hom

/-! # The structure morphism of the finite-part functor -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.toY :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    finitePart f ⟶ Y.functorOfPoints)
