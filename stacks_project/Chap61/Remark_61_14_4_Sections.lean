module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedSections

/-!
# Global sections on the small pro-étale site

The identity object of `X.ProEt` and the derived global sections functor
`RΓ(X, -)` on abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProEt
open ComplexShape

universe u

#check (AlgebraicGeometry.Scheme.ProEt.globalProEt : (X : Scheme.{u}) → X.ProEt)

#check (AlgebraicGeometry.Scheme.ProEt.globalProEt_hom :
  (X : Scheme.{u}) → (globalProEt X).hom = 𝟙 X)

#check (AlgebraicGeometry.Scheme.ProEt.globalProEt_isTerminal :
  (X : Scheme.{u}) → IsTerminal (globalProEt X))

#check (AlgebraicGeometry.Scheme.ProEt.globalSectionsDerived :
  (X : Scheme.{u}) → [HasSheafify (topology X) AddCommGrpCat.{u}] →
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})] →
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (topology X) (globalProEt X)))
      (HomologicalComplex.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}) (up ℤ))] →
    DerivedCategory (Sheaf (topology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.ProEt.globalSectionsDerived_eq :
  (X : Scheme.{u}) → [HasSheafify (topology X) AddCommGrpCat.{u}] →
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})] →
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor (topology X) (globalProEt X)))
      (HomologicalComplex.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}) (up ℤ))] →
    globalSectionsDerived X = siteAbelianSectionsDerived (topology X) (globalProEt X))
