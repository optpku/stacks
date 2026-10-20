module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Etale
import StacksCheckRecall

/-!
# Quotient of an open groupoid over a flat locally finitely presented atlas

If `(U, R, s, t, c)` is a groupoid in algebraic spaces over an algebraic space
`Y` with `U ⟶ Y` flat and locally of finite presentation and
`R ⟶ U ×_Y U` an open immersion, then `[U / R]` is an algebraic space and the
structure morphism to `Y` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 101.32.1. A groupoid in algebraic spaces over `Y` with flat, locally
finitely presented object space and open relation map has an algebraic-space
quotient `[U/R] = U/R` étale over `Y`. -/
@[stacks 0DU1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.exists_etale_quotient :
    ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S} (G : GroupoidAlgebraicSpace Y)
      [AlgebraicSpace.Flat G.U.hom]
      [AlgebraicSpace.LocallyOfFinitePresentation G.U.hom]
      [AlgebraicSpace.IsOpenImmersion G.toPreRelation.hom.left],
      ∃ (X : AlgebraicSpace S) (e : SmallQuotient.quotientStack G ≌ X.toGroupoids)
        (f : X ⟶ Y),
        atlasSpace G e ≫ f = G.U.hom ∧ AlgebraicSpace.Etale f ∧
          ∃ i : AlgebraicSpace.toSheaf.obj X ≅ G.toPreRelation.quotientSheaf,
            AlgebraicSpace.toSheaf.map (atlasSpace G e) ≫ i.hom =
                G.toPreRelation.quotientMap ∧
              i.hom ≫ G.toPreRelation.toBaseSheaf = AlgebraicSpace.toSheaf.map f)

end AlgebraicGeometry.GroupoidAlgebraicSpace
