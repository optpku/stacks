module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Colimits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 30.6.1: for a quasi-compact and quasi-separated morphism of schemes `f : X ⟶ S`, the
canonical map from the filtered colimit of the degree-`p` higher direct images of abelian sheaves
to the degree-`p` higher direct image of their filtered colimit is an isomorphism. -/
@[stacks 07TB] #check
  (AlgebraicGeometry.Scheme.higherDirectImageColimitComparison_isIso_of_quasiCompact_quasiSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}
      [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
      [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
      [HasInjectiveResolutions (X.carrier.Sheaf AddCommGrpCat.{u})]
      (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      {I : Type v} [SmallCategory I] [IsFiltered I]
      [HasColimitsOfShape I (X.carrier.Sheaf AddCommGrpCat.{u})]
      [HasColimitsOfShape I (S.carrier.Sheaf AddCommGrpCat.{u})]
      [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).Additive]
      (ℱ : I ⥤ X.carrier.Sheaf AddCommGrpCat.{u}) (p : ℕ),
      IsIso
        (colimit.post ℱ
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived p)))
