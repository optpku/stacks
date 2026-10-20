module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.naiveCotangent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → CochainComplex X.Modules ℤ)
