module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedCompleteness
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProEt
open DerivedCategory.Truncation.Lower
open ComplexShape

universe u

/- Remark 61.14.4 (1): because the small pro-étale site `X.ProEt` has enough weakly
contractible objects, every `K` in `D(X.ProEt)` satisfies
`K = Rlim τ≥(-n) K` by Cohomology on Sites, Proposition 21.51.2. -/
@[stacks 09A4] #check
  (AlgebraicGeometry.Scheme.ProEt.isHomotopyLimit_lowerTruncationTower :
    (X : Scheme.{u}) → [HasSheafify (topology X) AddCommGrpCat.{u}] →
      (K : DerivedCategory (Sheaf (topology X) AddCommGrpCat.{u})) →
      HomotopyLimit.IsOf (tower K) K)

/- Remark 61.14.4 (2): since `RΓ` commutes with `Rlim` by Injectives, Lemma 19.13.6,
`RΓ(X, K) = Rlim RΓ(X, τ≥(-n) K)` in `D(AddCommGrpCat)`. This will sometimes allow
us to extend results from bounded below complexes to all complexes. -/
@[stacks 09A4] #check
  (AlgebraicGeometry.Scheme.ProEt.globalSectionsDerived_isHomotopyLimit_lowerTruncationTower :
    (X : Scheme.{u}) → [HasSheafify (topology X) AddCommGrpCat.{u}] →
      [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})] →
      [HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          (siteAbelianSectionsFunctor (topology X) (globalProEt X)))
        (HomologicalComplex.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}) (up ℤ))] →
      (K : DerivedCategory (Sheaf (topology X) AddCommGrpCat.{u})) →
      HomotopyLimit.IsOf (tower K ⋙ globalSectionsDerived X)
        ((globalSectionsDerived X).obj K))
