/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Total Category of Left Resolutions

The category of left resolutions of varying objects is the full subcategory of the comma
category `(Φ.functor ↓ 𝟭 C₂)` cut out by the target morphism property.  This presentation uses
Mathlib's canonical comma and full-subcategory owners, so ordinary category structure and its
projection functors require no duplicate dependent implementation.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.LeftResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- The category of left resolutions of all objects in the target category. -/
@[stacks 0GSL "total category of left resolutions"]
abbrev Total (Φ : LocalizerMorphism W₁ W₂) :=
  (W₂.commaObj Φ.functor (𝟭 C₂)).FullSubcategory

namespace Total

variable {Φ : LocalizerMorphism W₁ W₂}

/-- The underlying comma-category object of a total left resolution. -/
abbrev comma (R : Total Φ) : Comma Φ.functor (𝟭 C₂) := R.obj

/-- The target object resolved by a total left resolution. -/
abbrev base (R : Total Φ) : C₂ := R.comma.right

/-- The resolving model in the source category. -/
abbrev model (R : Total Φ) : C₁ := R.comma.left

/-- The comparison from the image of the resolving model to the base object. -/
abbrev comparison (R : Total Φ) : Φ.functor.obj R.model ⟶ R.base := R.comma.hom

/-- The comparison of a total left resolution belongs to the target localization system. -/
theorem comparison_mem (R : Total Φ) : W₂ R.comparison := sorry

/-- The canonical inclusion into the ambient comma category. -/
@[stacks 0GSL "inclusion of the total left-resolution category"]
abbrev ι (Φ : LocalizerMorphism W₁ W₂) :
    Total Φ ⥤ Comma Φ.functor (𝟭 C₂) :=
  (W₂.commaObj Φ.functor (𝟭 C₂)).ι

/-- The projection sending a total left resolution to its resolved object. -/
@[stacks 0GSL "base projection of total left resolutions"]
abbrev baseFunctor (Φ : LocalizerMorphism W₁ W₂) : Total Φ ⥤ C₂ :=
  ι Φ ⋙ Comma.snd Φ.functor (𝟭 C₂)

/-- The projection sending a total left resolution to its resolving model. -/
@[stacks 0GSL "model projection of total left resolutions"]
abbrev modelFunctor (Φ : LocalizerMorphism W₁ W₂) : Total Φ ⥤ C₁ :=
  ι Φ ⋙ Comma.fst Φ.functor (𝟭 C₂)

/-- The base projection evaluates to the resolved object. -/
@[simp]
theorem baseFunctor_obj (R : Total Φ) : (baseFunctor Φ).obj R = R.base := sorry

/-- The model projection evaluates to the resolving model. -/
@[simp]
theorem modelFunctor_obj (R : Total Φ) : (modelFunctor Φ).obj R = R.model := sorry

/-- The base morphism underlying a morphism of total left resolutions. -/
abbrev baseHom {R S : Total Φ} (f : R ⟶ S) : R.base ⟶ S.base := f.hom.right

/-- The model morphism underlying a morphism of total left resolutions. -/
abbrev modelHom {R S : Total Φ} (f : R ⟶ S) : R.model ⟶ S.model := f.hom.left

/-- A total left-resolution morphism satisfies the comparison square in owner orientation. -/
@[reassoc]
theorem naturality {R S : Total Φ} (f : R ⟶ S) :
    Φ.functor.map (modelHom f) ≫ S.comparison = R.comparison ≫ baseHom f := sorry

/-- Construct a morphism of total left resolutions from its two components and comparison
square. -/
def homMk {R S : Total Φ} (baseHom : R.base ⟶ S.base)
    (modelHom : R.model ⟶ S.model)
    (naturality : Φ.functor.map modelHom ≫ S.comparison = R.comparison ≫ baseHom) :
    R ⟶ S :=
  ObjectProperty.homMk
    { left := modelHom
      right := baseHom
      w := naturality }

/-- The base component of a constructed total left-resolution morphism. -/
@[simp]
theorem homMk_baseHom {R S : Total Φ} (baseHom : R.base ⟶ S.base)
    (modelHom : R.model ⟶ S.model)
    (naturality : Φ.functor.map modelHom ≫ S.comparison = R.comparison ≫ baseHom) :
    Total.baseHom (homMk baseHom modelHom naturality) = baseHom := sorry

/-- The model component of a constructed total left-resolution morphism. -/
@[simp]
theorem homMk_modelHom {R S : Total Φ} (baseHom : R.base ⟶ S.base)
    (modelHom : R.model ⟶ S.model)
    (naturality : Φ.functor.map modelHom ≫ S.comparison = R.comparison ≫ baseHom) :
    Total.modelHom (homMk baseHom modelHom naturality) = modelHom := sorry

/-- Morphisms of total left resolutions are determined by their base and model components. -/
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

/-- Naturality of the comparison family on total left resolutions. -/
theorem comparison_naturality {R S : Total Φ} (f : R ⟶ S) :
    (modelFunctor Φ ⋙ Φ.functor).map f ≫ S.comparison =
      R.comparison ≫ (baseFunctor Φ).map f := sorry

/-- The comparison maps of all total left resolutions form a natural transformation. -/
@[stacks 0GSL "comparison family on total left resolutions"]
def comparisonNatTrans (Φ : LocalizerMorphism W₁ W₂) :
    modelFunctor Φ ⋙ Φ.functor ⟶ baseFunctor Φ where
  app R := R.comparison
  naturality := fun _ _ f => comparison_naturality f

/-- Evaluating the total comparison family gives the stored comparison. -/
@[simp]
theorem comparisonNatTrans_app (R : Total Φ) :
    (comparisonNatTrans Φ).app R = R.comparison := sorry

/-- Regard a left resolution of one object as an object of the total category. -/
@[stacks 0GSL "left resolution as a total resolution"]
def ofResolution {X : C₂} (R : Φ.LeftResolution X) : Total Φ :=
  ⟨⟨R.model, X, R.comparison⟩, R.comparison_mem⟩

/-- Recover the fiberwise left resolution represented by a total object. -/
@[stacks 0GSL "fiberwise left resolution of a total resolution"]
def toResolution (R : Total Φ) : Φ.LeftResolution R.base where
  X₁ := R.model
  w := R.comparison
  hw := R.comparison_mem

/-- The base of a left resolution viewed in the total category is its resolved object. -/
@[simp]
theorem ofResolution_base {X : C₂} (R : Φ.LeftResolution X) :
    (ofResolution R).base = X := sorry

/-- The model of a left resolution viewed in the total category is unchanged. -/
@[simp]
theorem ofResolution_model {X : C₂} (R : Φ.LeftResolution X) :
    (ofResolution R).model = R.model := sorry

/-- The comparison of a left resolution viewed in the total category is unchanged. -/
@[simp]
theorem ofResolution_comparison {X : C₂} (R : Φ.LeftResolution X) :
    (ofResolution R).comparison = R.comparison := sorry

/-- Recovering a fiberwise resolution preserves the model. -/
@[simp]
theorem toResolution_model (R : Total Φ) : R.toResolution.model = R.model := sorry

/-- Recovering a fiberwise resolution preserves the comparison. -/
@[simp]
theorem toResolution_comparison (R : Total Φ) :
    R.toResolution.comparison = R.comparison := sorry

/-- Passing a fiberwise left resolution through the total category recovers it. -/
@[simp]
theorem toResolution_ofResolution {X : C₂} (R : Φ.LeftResolution X) :
    (ofResolution R).toResolution = R := sorry

/-- Passing a total left resolution through its represented fiberwise resolution recovers the
total object. -/
@[simp]
theorem ofResolution_toResolution (R : Total Φ) :
    ofResolution R.toResolution = R := sorry

end Total

end CategoryTheory.LocalizerMorphism.LeftResolution
