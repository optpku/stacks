module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SpacesQuotient

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The induced fppf topology on schemes over an algebraic space. -/
abbrev schemesOverFppf {S : AlgebraicGeometry.Scheme.{u}}
    (B : AlgebraicGeometry.AlgebraicSpace S) :
    CategoryTheory.GrothendieckTopology
      (CategoryTheory.CostructuredArrow (AlgebraicGeometry.AlgebraicSpace.ofOverFunctor S) B) :=
  AlgebraicGeometry.AlgebraicSpace.SchemesOver.fppfTopology B

end AlgebraicGeometry.AlgebraicSpace.PreRelation

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.spacesQuotientPresheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    {U : CategoryTheory.Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U),
    (CategoryTheory.Over B)ᵒᵖ ⥤ Type (u + 1))
