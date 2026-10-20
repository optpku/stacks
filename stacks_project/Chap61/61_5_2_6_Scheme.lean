module

public import ReasLib.AlgebraicGeometry.WLocalHull.Limit

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.WLocal.Construction.scheme_π :
  ∀ (A : Type u) [CommRing A] (E : Finset A),
    AlgebraicGeometry.WLocal.Construction.scheme A ⟶ Algebra.WLocalHull.spectrum A E)
