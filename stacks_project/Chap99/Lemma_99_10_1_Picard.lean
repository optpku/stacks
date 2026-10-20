module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Category

/-! # The category of invertible modules on scheme-valued fibers -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Picard.category :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    CategoryTheory.Cat.{u + 1, u + 1})
