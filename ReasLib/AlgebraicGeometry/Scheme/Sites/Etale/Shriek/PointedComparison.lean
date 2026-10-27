/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.AddCommGrp.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.SkyscraperProduct
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Pointed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.Pointed
public import ReasLib.CategoryTheory.Sites.Point.PointedForgetful

/-!
# Coefficient comparisons for pointed shriek functors

Forgetting abelian coefficients gives lower and upper shriek comparisons compatible with their fibre descriptions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}
variable (f : X ⟶ Y) [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology Pointed.{u}]
variable [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
variable [Y.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
variable [PreservesFilteredColimits AddCommGrpCat.toPointed]

/-- A supported abelian section determines its pointed supported section. -/
def forgetfulSupportedSections (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : FiniteSupport.Admissible f V) :
    AddCommGrpCat.toPointed.obj (FiniteSupport.sections f G A) ⟶
      pointedSectionsSupportedIn f ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) A where
  toFun σ := ⟨σ.1, sorry⟩
  map_point := sorry

/-- A pointed supported section of forgotten coefficients determines an abelian supported section. -/
def supportedSectionsOfForgetful (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : FiniteSupport.Admissible f V) :
    pointedSectionsSupportedIn f ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) A ⟶
      AddCommGrpCat.toPointed.obj (FiniteSupport.sections f G A) where
  toFun s := ⟨s.1, sorry⟩
  map_point := sorry

/-- Coefficient forgetting maps the abelian admissible diagram to the pointed diagram. -/
def forgetfulAdmissibleDiagram (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    FiniteSupport.diagram f G V ⋙ AddCommGrpCat.toPointed ⟶
      pointedAdmissibleDiagram f ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) V where
  app A := forgetfulSupportedSections f G A
  naturality := sorry

/-- Coefficient forgetting identifies the pointed admissible diagram with the underlying abelian diagram. -/
def forgetfulAdmissibleDiagramInv (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    pointedAdmissibleDiagram f ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) V ⟶
      FiniteSupport.diagram f G V ⋙ AddCommGrpCat.toPointed where
  app A := supportedSectionsOfForgetful f G A
  naturality := sorry

/-- The comparison on compact-support presheaves is induced by supported sections and coproducts. -/
def forgetfulLowerShriekPresheafComparison
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (pointedLowerShriekPresheaf f).obj
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) ⟶
      (lowerShriekPresheaf f).obj G ⋙ AddCommGrpCat.toPointed where
  app V :=
    colimMap (forgetfulAdmissibleDiagramInv f G V.unop) ≫
      colimit.post (FiniteSupport.diagram f G V.unop) AddCommGrpCat.toPointed
  naturality := sorry

/-- The lower comparison has direction `f_! F(G) ⟶ F(f_! G)`. -/
def forgetfulLowerShriekComparison :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed) ⋙ pointedLowerShriek f ⟶
      lowerShriek f ⋙ (sheafCompose Y.smallEtaleTopology AddCommGrpCat.toPointed) where
  app G :=
    (presheafToSheaf Y.smallEtaleTopology Pointed.{u}).map
        (forgetfulLowerShriekPresheafComparison f G) ≫
      (sheafComposeNatTrans (Y.smallEtaleTopology) AddCommGrpCat.toPointed
          (sheafificationAdjunction _ AddCommGrpCat.{u})
          (sheafificationAdjunction _ Pointed.{u})).app
        ((lowerShriekPresheaf f).obj G)
  naturality := sorry

/-- The fibrewise stalk map of the lower coefficient comparison. -/
def forgetfulLowerShriekComparisonStalk
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y) :
    (pointedStalkCoproduct f z).obj
        ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) ⟶
      AddCommGrpCat.toPointed.obj ((abelianStalkCoproduct f z).obj G) :=
  Limits.Sigma.map (fun x : Fiber f z ↦
      (CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso
        (toSmallEtalePoint x.point) AddCommGrpCat.toPointed).hom.app G) ≫
    Limits.sigmaComparison AddCommGrpCat.toPointed (fun x : Fiber f z ↦
      (toSmallEtalePoint x.point).sheafFiber.obj G)

/-- The fibrewise stalk map is the canonical coproduct comparison after coefficient stalk maps. -/
theorem forgetfulLowerShriekComparisonStalk_eq
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y) :
    forgetfulLowerShriekComparisonStalk f G z =
      Limits.Sigma.map (fun x : Fiber f z ↦
        (CategoryTheory.GrothendieckTopology.Point.sheafFiberCompIso
          (toSmallEtalePoint x.point) AddCommGrpCat.toPointed).hom.app G) ≫
        Limits.sigmaComparison AddCommGrpCat.toPointed (fun x : Fiber f z ↦
          (toSmallEtalePoint x.point).sheafFiber.obj G) := rfl

/-- Sheafification carries the sectionwise comparison to the lower comparison. -/
theorem forgetfulLowerShriekComparison_spec
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (sheafificationAdjunction Y.smallEtaleTopology Pointed.{u}).unit.app
        ((pointedLowerShriekPresheaf f).obj
          ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G)) ≫
      (sheafToPresheaf Y.smallEtaleTopology Pointed.{u}).map
        ((forgetfulLowerShriekComparison f).app G) =
      forgetfulLowerShriekPresheafComparison f G ≫
        Functor.whiskerRight
          ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).unit.app
            ((lowerShriekPresheaf f).obj G)) AddCommGrpCat.toPointed := sorry

/-- The actual lower comparison satisfies the coherent stalk comparison square. -/
theorem forgetfulLowerShriekComparison_stalk
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (z : GeometricPoint Y) :
    ∃ eP : pointedLowerShriek f ⋙ (toSmallEtalePoint z).sheafFiber ≅ pointedStalkCoproduct f z,
    ∃ eA : lowerShriek f ⋙ (toSmallEtalePoint z).sheafFiber ≅ abelianStalkCoproduct f z,
      (toSmallEtalePoint z).sheafFiber.map ((forgetfulLowerShriekComparison f).app G) ≫
          ((toSmallEtalePoint z).sheafFiberCompIso AddCommGrpCat.toPointed).hom.app
            ((lowerShriek f).obj G) ≫
          AddCommGrpCat.toPointed.map (eA.hom.app G) =
        eP.hom.app ((sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).obj G) ≫
          forgetfulLowerShriekComparisonStalk f G z := sorry

/-- The upper coefficient comparison is the mate of the lower comparison. -/
def forgetfulUpperShriekComparison
    {abelianUpper : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper)
    (h : (pointedLowerShriek f).IsLeftAdjoint) :
    abelianUpper ⋙ (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed) ⟶
      (sheafCompose Y.smallEtaleTopology AddCommGrpCat.toPointed) ⋙ pointedUpperShriek f h :=
  mateEquiv adj (pointedLowerShriekAdjunction f h) (forgetfulLowerShriekComparison f)

/-- The upper comparison is characterized by the adjunction counits. -/
theorem forgetfulUpperShriekComparison_spec
    {abelianUpper : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper)
    (h : (pointedLowerShriek f).IsLeftAdjoint)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (pointedLowerShriek f).map ((forgetfulUpperShriekComparison f adj h).app G) ≫
        (pointedLowerShriekAdjunction f h).counit.app
          ((sheafCompose Y.smallEtaleTopology AddCommGrpCat.toPointed).obj G) =
      (forgetfulLowerShriekComparison f).app (abelianUpper.obj G) ≫
        (sheafCompose Y.smallEtaleTopology AddCommGrpCat.toPointed).map (adj.counit.app G) := sorry

/-- The comparison of the abelian and pointed fibrewise skyscraper products. -/
def forgetfulSkyscraperProductComparison (z : GeometricPoint Y) :
    abelianSkyscraperProduct f z ⋙
        (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed) ⟶
      AddCommGrpCat.toPointed ⋙ pointedSkyscraperProduct f z where
  app A := Pi.lift fun x : Fiber f z ↦
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).map (Pi.π _ x) ≫
      (CategoryTheory.GrothendieckTopology.Point.toPointedSkyscraperComparison
        X.smallEtaleTopology (toSmallEtalePoint x.point)).app A
  naturality := sorry

/-- Each product projection of the fibrewise comparison is the coefficient skyscraper map. -/
theorem forgetfulSkyscraperProductComparison_π (z : GeometricPoint Y)
    (A : AddCommGrpCat.{u}) (x : Fiber f z) :
    (forgetfulSkyscraperProductComparison f z).app A ≫ Pi.π _ x =
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).map (Pi.π _ x) ≫
        (CategoryTheory.GrothendieckTopology.Point.toPointedSkyscraperComparison
          X.smallEtaleTopology (toSmallEtalePoint x.point)).app A := by
  exact Limits.Pi.lift_π _ _

/-- The upper comparison respects coherent abelian and pointed skyscraper-product descriptions. -/
theorem forgetfulUpperShriekComparison_skyscraper
    {abelianUpper : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper)
    (h : (pointedLowerShriek f).IsLeftAdjoint) (z : GeometricPoint Y) :
    ∃ eA : (toSmallEtalePoint z).skyscraperSheafFunctor ⋙ abelianUpper ≅
        abelianSkyscraperProduct f z,
    ∃ eP : (toSmallEtalePoint z).skyscraperSheafFunctor ⋙ pointedUpperShriek f h ≅
        pointedSkyscraperProduct f z,
      ∀ A : AddCommGrpCat.{u},
        (forgetfulUpperShriekComparison f adj h).app
            ((toSmallEtalePoint z).skyscraperSheafFunctor.obj A) ≫
          (pointedUpperShriek f h).map
            ((CategoryTheory.GrothendieckTopology.Point.toPointedSkyscraperComparison
              Y.smallEtaleTopology (toSmallEtalePoint z)).app A) ≫
          (eP.hom.app (AddCommGrpCat.toPointed.obj A)) =
        (sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed).map (eA.hom.app A) ≫
          (forgetfulSkyscraperProductComparison f z).app A := sorry

/-- The upper coefficient comparison is invertible. -/
theorem forgetfulUpperShriekComparison_isIso
    {abelianUpper : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek f ⊣ abelianUpper)
    (h : (pointedLowerShriek f).IsLeftAdjoint) :
    IsIso (forgetfulUpperShriekComparison f adj h) := sorry

end AlgebraicGeometry.Scheme.Etale

end
