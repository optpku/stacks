/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.AddCommGrp.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Shriek.PointedComparison
public import ReasLib.CategoryTheory.Sites.Point.PointedForgetful
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Remark 63.6.6: a locally quasi-finite morphism induces a left adjoint on pointed étale sheaves. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek_isLeftAdjoint :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}],
      (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f).IsLeftAdjoint)

/- Remark 63.6.6: the stalk of pointed lower shriek is a coproduct over the geometric fibre. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.pointedLowerShriekStalkIso_nonempty :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}] (ybar : GeometricPoint Y),
      Nonempty (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f ⋙
        (GeometricPoint.toSmallEtalePoint ybar).sheafFiber ≅
          AlgebraicGeometry.Scheme.Etale.pointedStalkCoproduct f ybar))

/- Remark 63.6.6: the upper shriek of a pointed skyscraper is a product over the geometric fibre. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.pointedUpperShriekSkyscraperIso_nonempty :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    (h : (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f).IsLeftAdjoint)
    (ybar : GeometricPoint Y),
      Nonempty ((GeometricPoint.toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙
        AlgebraicGeometry.Scheme.Etale.pointedUpperShriek f h ≅
          AlgebraicGeometry.Scheme.Etale.pointedSkyscraperProduct f ybar))

/- Remark 63.6.6: forgetting abelian coefficients gives the lower shriek comparison. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.forgetfulLowerShriekComparison :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed],
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed) ⋙
          AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f ⟶
        AlgebraicGeometry.Scheme.Etale.lowerShriek f ⋙
          sheafCompose Y.smallEtaleTopology AddCommGrpCat.toPointed)

/- Remark 63.6.6: the lower comparison is compatible with coherent stalk descriptions. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.forgetfulLowerShriekComparison_stalk :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [PreservesFilteredColimits AddCommGrpCat.toPointed]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y),
      ∃ eP : AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f ⋙
          (GeometricPoint.toSmallEtalePoint z).sheafFiber ≅
            AlgebraicGeometry.Scheme.Etale.pointedStalkCoproduct f z,
      ∃ eA : AlgebraicGeometry.Scheme.Etale.lowerShriek f ⋙
          (GeometricPoint.toSmallEtalePoint z).sheafFiber ≅
            AlgebraicGeometry.Scheme.Etale.abelianStalkCoproduct f z,
        (GeometricPoint.toSmallEtalePoint z).sheafFiber.map
            ((AlgebraicGeometry.Scheme.Etale.forgetfulLowerShriekComparison f).app G) ≫
          ((GeometricPoint.toSmallEtalePoint z).sheafFiberCompIso AddCommGrpCat.toPointed).hom.app
            ((AlgebraicGeometry.Scheme.Etale.lowerShriek f).obj G) ≫
          AddCommGrpCat.toPointed.map (eA.hom.app G) =
        eP.hom.app ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) ≫
          AlgebraicGeometry.Scheme.Etale.forgetfulLowerShriekComparisonStalk f G z)

/- Remark 63.6.6: forgetting abelian coefficients gives the upper shriek mate comparison. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.forgetfulUpperShriekComparison :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    {A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : AlgebraicGeometry.Scheme.Etale.lowerShriek f ⊣ A)
    (h : (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f).IsLeftAdjoint),
      A ⋙ sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed ⟶
        sheafCompose Y.smallEtaleTopology AddCommGrpCat.toPointed ⋙
          AlgebraicGeometry.Scheme.Etale.pointedUpperShriek f h)

/- Remark 63.6.6: the upper comparison is compatible with fibrewise skyscraper products. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.forgetfulUpperShriekComparison_skyscraper :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [PreservesFilteredColimits AddCommGrpCat.toPointed]
    {A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : AlgebraicGeometry.Scheme.Etale.lowerShriek f ⊣ A)
    (h : (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f).IsLeftAdjoint)
    (z : GeometricPoint Y),
      ∃ eA : (GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor ⋙ A ≅
          AlgebraicGeometry.Scheme.Etale.abelianSkyscraperProduct f z,
      ∃ eP : (GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor ⋙
          AlgebraicGeometry.Scheme.Etale.pointedUpperShriek f h ≅
            AlgebraicGeometry.Scheme.Etale.pointedSkyscraperProduct f z,
        ∀ A : AddCommGrpCat.{u},
          (AlgebraicGeometry.Scheme.Etale.forgetfulUpperShriekComparison f adj h).app
              ((GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor.obj A) ≫
            (AlgebraicGeometry.Scheme.Etale.pointedUpperShriek f h).map
              ((CategoryTheory.GrothendieckTopology.Point.toPointedSkyscraperComparison
                Y.smallEtaleTopology (GeometricPoint.toSmallEtalePoint z)).app A) ≫
            eP.hom.app (AddCommGrpCat.toPointed.obj A) =
          (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).map (eA.hom.app A) ≫
            (AlgebraicGeometry.Scheme.Etale.forgetfulSkyscraperProductComparison f z).app A)

/- Remark 63.6.6: the upper forgetful comparison is an isomorphism. -/
@[stacks 0F5L]
#check (AlgebraicGeometry.Scheme.Etale.forgetfulUpperShriekComparison_isIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology Pointed.{u}]
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    [PreservesFilteredColimits AddCommGrpCat.toPointed]
    {A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : AlgebraicGeometry.Scheme.Etale.lowerShriek f ⊣ A)
    (h : (AlgebraicGeometry.Scheme.Etale.pointedLowerShriek f).IsLeftAdjoint),
      IsIso (AlgebraicGeometry.Scheme.Etale.forgetfulUpperShriekComparison f adj h))

end
