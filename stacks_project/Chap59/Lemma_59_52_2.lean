/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open scoped GrothendieckTopologyDerivedSections

universe u

/- Lemma 59.52.2 -/
@[stacks 0GIS] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedSections_preservesCoproduct :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
      [Functor.HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)))
        (HomologicalComplex.quasiIso
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
      {I : Type u}
      (K : I → DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
      [HasCoproductsOfShape I
        (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
      [HasCoproductsOfShape I (DerivedCategory AddCommGrpCat.{u})]
      (a : ℤ) (hK : ∀ i : I, (K i).IsGE a),
      IsIso
        (CategoryTheory.Limits.sigmaComparison
          (siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)) K))

end
