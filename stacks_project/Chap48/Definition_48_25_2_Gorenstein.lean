module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein

@[expose] public section

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → X → Prop)

#check
  (AlgebraicGeometry.Gorenstein :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
