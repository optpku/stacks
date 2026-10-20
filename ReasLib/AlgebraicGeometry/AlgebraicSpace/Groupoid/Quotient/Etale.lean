module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf

/-!
# Étale quotients of open groupoids

An open groupoid whose object space is flat and locally of finite presentation over
the base has an algebraic-space quotient étale over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid with flat, locally finitely presented object space over its base and
open relation map has a quotient represented by an algebraic space étale over the
base. Its sheaf of points is the canonical fppf quotient sheaf, compatibly with the
atlas and the structure morphism. -/
theorem exists_etale_quotient {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace Y)
    [AlgebraicSpace.Flat G.U.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.U.hom]
    [AlgebraicSpace.IsOpenImmersion G.toPreRelation.hom.left] :
    ∃ (X : AlgebraicSpace S) (e : SmallQuotient.quotientStack G ≌ X.toGroupoids)
      (f : X ⟶ Y),
      atlasSpace G e ≫ f = G.U.hom ∧ AlgebraicSpace.Etale f ∧
        ∃ i : AlgebraicSpace.toSheaf.obj X ≅ G.toPreRelation.quotientSheaf,
          AlgebraicSpace.toSheaf.map (atlasSpace G e) ≫ i.hom =
              G.toPreRelation.quotientMap ∧
            i.hom ≫ G.toPreRelation.toBaseSheaf = AlgebraicSpace.toSheaf.map f :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
