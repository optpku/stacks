/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation.Hom

/- The quotient maps are natural with respect to a morphism of scheme pre-relations. -/
#check (AlgebraicGeometry.Scheme.PreRelation.Hom.quotientMap_naturality :
  ∀ {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U} {Q : PreRelation U'}
    (f : Hom P Q) (J : GrothendieckTopology (Over S)) [J.Subcanonical],
    P.quotientMap J ≫ f.quotientSheafMap J =
      J.uliftYoneda.{u + 1}.map f.obj ≫ Q.quotientMap J)

end AlgebraicGeometry.Scheme.PreRelation.Hom
