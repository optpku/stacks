module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSite

@[expose] public section

open CategoryTheory

universe u

/- Polynomial base change induces the opposite functor on polynomial sites. -/
#check (RingedSite.Cotangent.Functoriality.mapOp :
  ∀ {A A' B B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'}
    {β : A' ⟶ B'} {φ : B ⟶ B'},
    CommSq ρ α β φ → RingedSite.Cotangent.polynomialSite α ⥤
      RingedSite.Cotangent.polynomialSite β)
