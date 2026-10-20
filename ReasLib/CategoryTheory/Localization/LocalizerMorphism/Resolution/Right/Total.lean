/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Total Category of Right Resolutions

The category of right resolutions of varying objects is the full subcategory of the comma
category `(𝟭 C₂ ↓ Φ.functor)` cut out by the target morphism property.  This presentation uses
Mathlib's canonical comma and full-subcategory owners, so ordinary category structure and its
projection functors require no duplicate dependent implementation.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.RightResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- The category of right resolutions of all objects in the target category. -/
@[stacks 0GSL "total category of right resolutions"]
abbrev Total (Φ : LocalizerMorphism W₁ W₂) :=
  (W₂.commaObj (𝟭 C₂) Φ.functor).FullSubcategory

namespace Total

variable {Φ : LocalizerMorphism W₁ W₂}

/-- The underlying comma-category object of a total right resolution. -/
abbrev comma (R : Total Φ) : Comma (𝟭 C₂) Φ.functor := R.obj

/-- The target object resolved by a total right resolution. -/
abbrev base (R : Total Φ) : C₂ := R.comma.left

/-- The resolving model in the source category. -/
abbrev model (R : Total Φ) : C₁ := R.comma.right

/-- The comparison from the base object to the image of the resolving model. -/
abbrev comparison (R : Total Φ) : R.base ⟶ Φ.functor.obj R.model := R.comma.hom

/-- The comparison of a total right resolution belongs to the target localization system. -/
theorem comparison_mem (R : Total Φ) : W₂ R.comparison := sorry

/-- The canonical inclusion into the ambient comma category. -/
@[stacks 0GSL "inclusion of the total right-resolution category"]
abbrev ι (Φ : LocalizerMorphism W₁ W₂) :
    Total Φ ⥤ Comma (𝟭 C₂) Φ.functor :=
  (W₂.commaObj (𝟭 C₂) Φ.functor).ι

/-- The projection sending a total right resolution to its resolved object. -/
@[stacks 0GSL "base projection of total right resolutions"]
abbrev baseFunctor (Φ : LocalizerMorphism W₁ W₂) : Total Φ ⥤ C₂ :=
  ι Φ ⋙ Comma.fst (𝟭 C₂) Φ.functor

/-- The projection sending a total right resolution to its resolving model. -/
@[stacks 0GSL "model projection of total right resolutions"]
abbrev modelFunctor (Φ : LocalizerMorphism W₁ W₂) : Total Φ ⥤ C₁ :=
  ι Φ ⋙ Comma.snd (𝟭 C₂) Φ.functor

/-- The base projection evaluates to the resolved object. -/
@[simp]
theorem baseFunctor_obj (R : Total Φ) : (baseFunctor Φ).obj R = R.base := sorry

/-- The model projection evaluates to the resolving model. -/
@[simp]
theorem modelFunctor_obj (R : Total Φ) : (modelFunctor Φ).obj R = R.model := sorry

/-- The base morphism underlying a morphism of total right resolutions. -/
abbrev baseHom {R S : Total Φ} (f : R ⟶ S) : R.base ⟶ S.base := f.hom.left

/-- The model morphism underlying a morphism of total right resolutions. -/
abbrev modelHom {R S : Total Φ} (f : R ⟶ S) : R.model ⟶ S.model := f.hom.right

/-- A total right-resolution morphism satisfies the comparison square in owner orientation. -/
@[reassoc]
theorem naturality {R S : Total Φ} (f : R ⟶ S) :
    R.comparison ≫ Φ.functor.map (modelHom f) = baseHom f ≫ S.comparison := sorry

/-- Construct a morphism of total right resolutions from its two components and comparison
square. -/
def homMk {R S : Total Φ} (baseHom : R.base ⟶ S.base)
    (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ Φ.functor.map modelHom = baseHom ≫ S.comparison) :
    R ⟶ S :=
  ObjectProperty.homMk
    { left := baseHom
      right := modelHom
      w := naturality.symm }

/-- The base component of a constructed total right-resolution morphism. -/
@[simp]
theorem homMk_baseHom {R S : Total Φ} (baseHom : R.base ⟶ S.base)
    (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ Φ.functor.map modelHom = baseHom ≫ S.comparison) :
    Total.baseHom (homMk baseHom modelHom naturality) = baseHom := sorry

/-- The model component of a constructed total right-resolution morphism. -/
@[simp]
theorem homMk_modelHom {R S : Total Φ} (baseHom : R.base ⟶ S.base)
    (modelHom : R.model ⟶ S.model)
    (naturality : R.comparison ≫ Φ.functor.map modelHom = baseHom ≫ S.comparison) :
    Total.modelHom (homMk baseHom modelHom naturality) = modelHom := sorry

/-- Morphisms of total right resolutions are determined by their base and model components. -/
@[ext]
theorem hom_ext {R S : Total Φ} {f g : R ⟶ S}
    (hbase : baseHom f = baseHom g) (hmodel : modelHom f = modelHom g) : f = g := sorry

/-- The identity total morphism has identity base component. -/
@[simp]
theorem id_baseHom (R : Total Φ) : baseHom (𝟙 R) = 𝟙 R.base := sorry

/-- The identity total morphism has identity model component. -/
@[simp]
theorem id_modelHom (R : Total Φ) : modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Composition of total morphisms composes their base components. -/
@[simp]
theorem comp_baseHom {R S T : Total Φ} (f : R ⟶ S) (g : S ⟶ T) :
    baseHom (f ≫ g) = baseHom f ≫ baseHom g := sorry

/-- Composition of total morphisms composes their model components. -/
@[simp]
theorem comp_modelHom {R S T : Total Φ} (f : R ⟶ S) (g : S ⟶ T) :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The base projection sends a total morphism to its base component. -/
@[simp]
theorem baseFunctor_map {R S : Total Φ} (f : R ⟶ S) :
    (baseFunctor Φ).map f = baseHom f := sorry

/-- The model projection sends a total morphism to its model component. -/
@[simp]
theorem modelFunctor_map {R S : Total Φ} (f : R ⟶ S) :
    (modelFunctor Φ).map f = modelHom f := sorry

/-- Naturality of the comparison family on total right resolutions. -/
theorem comparison_naturality {R S : Total Φ} (f : R ⟶ S) :
    (baseFunctor Φ).map f ≫ S.comparison =
      R.comparison ≫ (modelFunctor Φ ⋙ Φ.functor).map f := sorry

/-- The comparison maps of all total right resolutions form a natural transformation. -/
@[stacks 0GSL "comparison family on total right resolutions"]
def comparisonNatTrans (Φ : LocalizerMorphism W₁ W₂) :
    baseFunctor Φ ⟶ modelFunctor Φ ⋙ Φ.functor where
  app R := R.comparison
  naturality := fun _ _ f => comparison_naturality f

/-- Evaluating the total comparison family gives the stored comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : Total Φ) :
    (comparisonNatTrans Φ).app R = R.comparison := sorry

/-- Regard a right resolution of one object as an object of the total category. -/
@[stacks 0GSL "right resolution as a total resolution"]
def ofResolution {X : C₂} (R : Φ.RightResolution X) : Total Φ :=
  ⟨⟨X, R.model, R.comparison⟩, R.comparison_mem⟩

/-- Recover the fiberwise right resolution represented by a total object. -/
@[stacks 0GSL "fiberwise right resolution of a total resolution"]
def toResolution (R : Total Φ) : Φ.RightResolution R.base where
  X₁ := R.model
  w := R.comparison
  hw := R.comparison_mem

/-- The base of a right resolution viewed in the total category is its resolved object. -/
@[simp]
theorem ofResolution_base {X : C₂} (R : Φ.RightResolution X) :
    (ofResolution R).base = X := sorry

/-- The model of a right resolution viewed in the total category is unchanged. -/
@[simp]
theorem ofResolution_model {X : C₂} (R : Φ.RightResolution X) :
    (ofResolution R).model = R.model := sorry

/-- The comparison of a right resolution viewed in the total category is unchanged. -/
@[simp]
theorem ofResolution_comparison {X : C₂} (R : Φ.RightResolution X) :
    (ofResolution R).comparison = R.comparison := sorry

/-- Recovering a fiberwise resolution preserves the model. -/
@[simp]
theorem toResolution_model (R : Total Φ) : R.toResolution.model = R.model := sorry

/-- Recovering a fiberwise resolution preserves the comparison. -/
@[simp]
theorem toResolution_comparison (R : Total Φ) :
    R.toResolution.comparison = R.comparison := sorry

/-- Passing a fiberwise right resolution through the total category recovers it. -/
@[simp]
theorem toResolution_ofResolution {X : C₂} (R : Φ.RightResolution X) :
    (ofResolution R).toResolution = R := sorry

/-- Passing a total right resolution through its represented fiberwise resolution recovers the
total object. -/
@[simp]
theorem ofResolution_toResolution (R : Total Φ) :
    ofResolution R.toResolution = R := sorry

end Total

end CategoryTheory.LocalizerMorphism.RightResolution
