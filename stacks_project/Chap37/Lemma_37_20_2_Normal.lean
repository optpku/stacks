module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Normal :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
