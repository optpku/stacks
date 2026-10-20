module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf

universe u

#check (@AlgebraicGeometry.Scheme.PreRelation.quotientPresheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U : CategoryTheory.Over S},
    AlgebraicGeometry.Scheme.PreRelation U →
      CategoryTheory.Functor (CategoryTheory.Over S)ᵒᵖ (Type u))
