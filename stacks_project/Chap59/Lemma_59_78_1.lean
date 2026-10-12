/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Torsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Lemma 59.78.1 (1): on a quasi-compact quasi-separated scheme `X`, étale
cohomology `H^n_étale(X, F)` of a torsion abelian sheaf `F` on `X_étale` is a
torsion abelian group for every `n`. -/
@[stacks 0DDC] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_isTorsion :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      IsLocallyTorsion F → (n : ℕ) →
        AddMonoid.IsTorsion (F.H' n (globalEtale X)))

/- Lemma 59.78.1 (2): on a quasi-compact quasi-separated scheme `X`, if
`K ∈ D⁺(X_étale)` has torsion cohomology sheaves, then
`H^n_étale(X, K)` is a torsion abelian group for every `n`. -/
@[stacks 0DDC] #check
  (AlgebraicGeometry.Scheme.Etale.derivedEtaleCohomology_isTorsion :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
      [Functor.HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)))
        (HomologicalComplex.quasiIso
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K →
      (n : ℤ) →
        AddMonoid.IsTorsion
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
            ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj
              (DerivedCategory.Plus.ι.obj K))))

end AlgebraicGeometry.Scheme.Etale

end
