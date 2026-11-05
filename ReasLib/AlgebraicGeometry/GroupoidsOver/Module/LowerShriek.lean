/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Pullback.Universe
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

/-!
# Module lower shriek on categories fibred in groupoids

Module inverse image on associated sites has a left adjoint constructed from free
presentations and a canonical comparison with lower shriek on abelian sheaves. For faithful morphisms with source
equalizers, lower shriek is exact and inverse image preserves injective modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor Limits FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/-- The module inverse image `f^* : Mod(Y_τ, O_Y) ⥤ Mod(X_τ, O_X)` along a
1-morphism of categories fibred in groupoids, obtained by restricting scalars
along `f⁻¹ O_Y ≅ O_X`. -/
abbrev associatedModuleInverseImage :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf X τ) :=
  moduleInverseImage (toCartesianBasedFunctor f).toFunctor (associatedStructureSheaf Y τ) ⋙
    SheafOfModules.restrictScalars
      (associatedStructureSheafInverseImageIso f τ).inv

/-- The module lower shriek `f_! : Mod(X_τ, O_X) ⥤ Mod(Y_τ, O_Y)`.
Restrict scalars to the inverse-image ring, apply the free-presentation
left adjoint on module presheaves, and sheafify. Source objects, arrows,
and coefficients fit in the section universe `u + 1`. -/
abbrev associatedModuleLowerShriek :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) := by
  let F := (toCartesianBasedFunctor f).toFunctor
  let R := associatedStructureSheaf Y τ
  letI : (PresheafOfModules.pushforward.{u + 1} (F := F)
      (𝟙 (F.op ⋙ R.obj))).IsRightAdjoint := inferInstance
  exact SheafOfModules.restrictScalars (associatedStructureSheafInverseImageIso f τ).hom ⋙
    (SheafOfModules.forget (inverseImageRingSheaf F R) ⋙
      PresheafOfModules.pullback.{u + 1} (𝟙 (F.op ⋙ R.obj)) ⋙
      PresheafOfModules.sheafification (𝟙 R.obj))

/-- The adjunction `f_! ⊣ f^*` of associated `τ`-module sheaves. -/
def associatedModuleLowerShriek_adjunction :
    associatedModuleLowerShriek f τ ⊣ associatedModuleInverseImage f τ := by
  let F := (toCartesianBasedFunctor f).toFunctor
  let R := associatedStructureSheaf Y τ
  letI : (PresheafOfModules.pushforward.{u + 1} (F := F)
      (𝟙 (F.op ⋙ R.obj))).IsRightAdjoint := inferInstance
  let adj := SheafOfModules.PullbackConstruction.adjunction.{u + 1}
    (F := F) (J := X.associatedTopology τ) (K := Y.associatedTopology τ)
    (𝟙 (inverseImageRingSheaf (J := X.associatedTopology τ) F R))
  let adj' : SheafOfModules.restrictScalars.{u + 1}
      (associatedStructureSheafInverseImageIso f τ).hom ⊣
      SheafOfModules.restrictScalars.{u + 1}
        (associatedStructureSheafInverseImageIso f τ).inv :=
    (SheafOfModules.Restriction.equivalenceOfIso
      (associatedStructureSheafInverseImageIso f τ).symm).toAdjunction
  exact adj'.comp adj

/-- The displayed lower shriek witnesses that associated module inverse image
is a right adjoint in the section universe `u + 1`. -/
instance associatedModuleInverseImage_isRightAdjoint :
    (associatedModuleInverseImage f τ).IsRightAdjoint :=
  (associatedModuleLowerShriek_adjunction f τ).isRightAdjoint

/-- The Hom equivalence induced by the associated `τ`-module lower-shriek
adjunction. -/
def associatedModuleLowerShriek_homEquiv
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    (G : SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) :
    ((associatedModuleLowerShriek f τ).obj F ⟶ G) ≃
      (F ⟶ (associatedModuleInverseImage f τ).obj G) :=
  (associatedModuleLowerShriek_adjunction f τ).homEquiv F G

section Comparison

variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
variable [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]

/-- Forgetting module structure identifies `associatedModuleInverseImage` with
abelian inverse image. -/
def associatedModuleInverseImage_underlyingIso :
    associatedModuleInverseImage f τ ⋙
        SheafOfModules.toSheaf (associatedStructureSheaf X τ) ≅
      SheafOfModules.toSheaf (associatedStructureSheaf Y τ) ⋙
        (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ) :=
  isoWhiskerLeft
      (moduleInverseImage (toCartesianBasedFunctor f).toFunctor
        (associatedStructureSheaf Y τ))
      (SheafOfModules.restrictScalarsCompToSheaf
        (associatedStructureSheafInverseImageIso f τ).inv) ≪≫
    moduleInverseImage.underlyingIso (toCartesianBasedFunctor f).toFunctor
      (associatedStructureSheaf Y τ)

/-- The canonical comparison from abelian `f_!` after forgetting to forgetting
after module `f_!`. -/
def associatedModuleLowerShriek_underlyingComparison :
    SheafOfModules.toSheaf (associatedStructureSheaf X τ) ⋙
        (toCartesianBasedFunctor f).toFunctor.sheafPullback AddCommGrpCat.{u + 1}
          (X.associatedTopology τ) (Y.associatedTopology τ) ⟶
      associatedModuleLowerShriek f τ ⋙
        SheafOfModules.toSheaf (associatedStructureSheaf Y τ) :=
  ((mateEquiv (associatedModuleLowerShriek_adjunction f τ)
        ((toCartesianBasedFunctor f).toFunctor.sheafAdjunctionContinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ)
          (Y.associatedTopology τ))).symm
      (associatedModuleInverseImage_underlyingIso f τ).hom).natTrans

end Comparison

/-- The canonical comparison between abelian and module lower shriek on associated
sites is invertible. -/
instance associatedModuleLowerShriek_underlyingComparison_isIso
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
    [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    IsIso (associatedModuleLowerShriek_underlyingComparison f τ) := sorry

/-- If a 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids over `(Sch/S)_fppf` is faithful and `X` has equalizers, then the
associated module lower shriek `f_!` is exact for every standard topology `τ`. -/
theorem associatedModuleLowerShriek_exact
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    exactFunctor
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
      (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ))
      (associatedModuleLowerShriek f τ) := sorry

/-- If a 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids over `(Sch/S)_fppf` is faithful and `X` has equalizers, then inverse
image of modules preserves injective objects for every standard topology `τ`. -/
instance associatedModuleInverseImage_preservesInjectiveObjects
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    (associatedModuleInverseImage f τ).PreservesInjectiveObjects := sorry

end AlgebraicGeometry.GroupoidsOver
