/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.HigherDirectImage.Comparison

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 96.21.2 (1): Abelian higher direct image is sheafification of
cohomology of the projection inverse image on the Yoneda fibre product. -/
@[stacks 075G] #check
  (AlgebraicGeometry.GroupoidsOver.sheafifyHigherDirectImagePresheafIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology),
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})] →
    [AlgebraicStack X] → [AlgebraicStack Y] →
    [∀ y : Y.total,
      HasSheafify (GroupoidsOver.associatedTopology
        (yonedaFibreProduct f (GroupoidsOver.fiberObj y)) τ) AddCommGrpCat.{u + 1}] →
    [∀ y : Y.total,
      HasExt.{u + 1} (Sheaf (GroupoidsOver.associatedTopology
        (yonedaFibreProduct f (GroupoidsOver.fiberObj y)) τ) AddCommGrpCat.{u + 1})] →
    (F : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) → (i : ℕ) →
      GroupoidsOver.sheafifyHigherDirectImagePresheaf f τ F i ≅
        GroupoidsOver.higherDirectImage f τ F i)

/- Lemma 96.21.2 (2): The underlying additive sheaf of module higher direct
image is sheafification of module-coefficient fibre-product cohomology. -/
@[stacks 075G] #check
  (AlgebraicGeometry.GroupoidsOver.sheafifyHigherDirectImageModulePresheafIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology),
    [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [HasInjectiveResolutions (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})] →
    [AlgebraicStack X] → [AlgebraicStack Y] →
    [∀ y : Y.total,
      HasSheafify (GroupoidsOver.associatedTopology
        (yonedaFibreProduct f (GroupoidsOver.fiberObj y)) τ) AddCommGrpCat.{u + 1}] →
    [∀ y : Y.total,
      HasExt.{u + 1} (Sheaf (GroupoidsOver.associatedTopology
        (yonedaFibreProduct f (GroupoidsOver.fiberObj y)) τ) AddCommGrpCat.{u + 1})] →
    (G : SheafOfModules.{u + 1} (GroupoidsOver.associatedStructureSheaf X τ)) →
    [HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}] →
    [∀ y : Y.total,
      ∀ P : (yonedaFibreProduct f (GroupoidsOver.fiberObj y)).totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (toCartesianBasedFunctor (yonedaFibreProduct.pr f
          (GroupoidsOver.fiberObj y))).toFunctor.op.HasLeftKanExtension P] →
    (i : ℕ) →
      GroupoidsOver.sheafifyHigherDirectImageModulePresheaf f τ G i ≅
        (SheafOfModules.toSheaf (GroupoidsOver.associatedStructureSheaf Y τ)).obj
          (GroupoidsOver.higherDirectImageModule f τ G i))
