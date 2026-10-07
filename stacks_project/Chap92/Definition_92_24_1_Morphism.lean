module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex

/-!
# Cotangent complexes of morphisms of schemes

This leaf specializes the ringed-space cotangent complex to a morphism of schemes
`f : X ⟶ Y`, taking `L_{X/Y}` to be the cotangent complex of `f` as a morphism of
ringed spaces.
-/

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.cotangentComplex :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → CochainComplex X.Modules ℤ)
