module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.InDimensions

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverInDimensionsGE :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    X.Modules → (X ⟶ Y) → ℕ → Prop)
