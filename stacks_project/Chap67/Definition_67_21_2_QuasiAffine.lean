module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine

@[expose] public section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}, (X ⟶ Y) → Prop)
