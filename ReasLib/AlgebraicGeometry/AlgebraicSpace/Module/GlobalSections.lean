/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections

/-!
# Global sections of modules on algebraic spaces

Global sections are the additive group of morphisms from the structure module.
Module morphisms and pullbacks induce canonical maps on these groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The additive group of global sections of an `𝒪_X`-module, realized as
`Hom(𝒪_X, F)` in `X.Modules`. The Hom-type of sheaves of modules on the large
small-étale site lives in `Type (u + 1)`. -/
def globalSections {X : AlgebraicSpace S} (F : X.Modules) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (SheafOfModules.unit (structureSheaf X) ⟶ F)

/-- Evaluating `globalSections F` recovers the Hom-group `Hom(𝒪_X, F)`. -/
theorem globalSections_obj {X : AlgebraicSpace S} (F : X.Modules) :
    globalSections F = AddCommGrpCat.of (SheafOfModules.unit (structureSheaf X) ⟶ F) :=
  rfl

/-- The map on global sections induced by a morphism of `𝒪_X`-modules, given by
postcomposition on `Hom(𝒪_X, -)`. -/
def globalSectionsMap {X : AlgebraicSpace S} {F G : X.Modules} (φ : F ⟶ G) :
    globalSections F ⟶ globalSections G :=
  AddCommGrpCat.ofHom
    { toFun := fun ψ => ψ ≫ φ
      map_zero' := sorry
      map_add' := sorry }

/-- Postcomposition on `Hom(𝒪_X, -)` is the underlying function of `globalSectionsMap`. -/
theorem globalSectionsMap_eq {X : AlgebraicSpace S} {F G : X.Modules} (φ : F ⟶ G)
    (ψ : SheafOfModules.unit (structureSheaf X) ⟶ F) :
    (globalSectionsMap φ).hom ψ = ψ ≫ φ :=
  rfl

/-- The pullback map on global sections along `f : X ⟶ Y`. A section
`ψ : 𝒪_Y ⟶ F` is sent to `𝒪_X ⟶ f^* 𝒪_Y ⟶ f^* F`. -/
def globalSectionsPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules) :
    globalSections F ⟶ globalSections ((pullback f).obj F) :=
  AddCommGrpCat.ofHom
    { toFun := fun ψ ↦ structureModulePullbackInv f ≫ (pullback f).map ψ
      map_zero' := sorry
      map_add' := sorry }

/-- Pulling back a global section composes the structure-module comparison with its pullback. -/
theorem globalSectionsPullback_apply {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : Y.Modules)
    (ψ : SheafOfModules.unit (structureSheaf Y) ⟶ F) :
    (globalSectionsPullback f F).hom ψ =
      structureModulePullbackInv f ≫ (pullback f).map ψ :=
  rfl

/-- The map on global sections obtained by pulling back first along `g`, then
along `f`, and comparing the resulting module with pullback along `f ≫ g`. -/
def globalSectionsPullbackComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules) :
    globalSections ((pullback g).obj F) ⟶
      globalSections ((pullback (f ≫ g)).obj F) :=
  globalSectionsPullback f ((pullback g).obj F) ≫
    globalSectionsMap ((pullbackCompIso f g).hom.app F)

/-- Pulling back global sections through `g` and then `f` agrees with the
global-sections pullback map for `f ≫ g`. -/
theorem globalSectionsPullback_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Modules) :
    globalSectionsPullback g F ≫ globalSectionsPullbackComp f g F =
      globalSectionsPullback (f ≫ g) F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
