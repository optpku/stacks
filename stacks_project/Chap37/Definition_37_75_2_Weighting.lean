module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting

open CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.IsWeighting :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.LocallyQuasiFinite f], (X → ℤ) → Prop)
