/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Map
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps and the Total Category of Right Resolutions

This leaf identifies dependent maps of right resolutions with ordinary morphisms in the total
comma-category model.  It is the boundary at which downstream code can stop carrying explicit
reindexing of base morphisms and use ordinary category composition instead.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.RightResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂}

namespace Map

variable {X Y Z : C₂} {f : X ⟶ Y} {g : Y ⟶ Z}
  {R : Φ.RightResolution X} {S : Φ.RightResolution Y} {T : Φ.RightResolution Z}

/-- Regard a dependent right-resolution map as a morphism in the total category. -/
@[stacks 0GSL "right-resolution map as a total morphism"]
def toTotalHom (m : Map f R S) : Total.ofResolution R ⟶ Total.ofResolution S :=
  Total.homMk f m.modelHom m.comparison_naturality

/-- The base component of the associated total morphism is the map being resolved. -/
@[simp]
theorem toTotalHom_baseHom (m : Map f R S) :
    Total.baseHom m.toTotalHom = f := sorry

/-- The model component of the associated total morphism is unchanged. -/
@[simp]
theorem toTotalHom_modelHom (m : Map f R S) :
    Total.modelHom m.toTotalHom = m.modelHom := sorry

/-- The identity dependent map becomes the identity total morphism. -/
@[simp]
theorem toTotalHom_id (R : Φ.RightResolution X) :
    (Map.id R).toTotalHom = 𝟙 (Total.ofResolution R) := sorry

/-- Composition of dependent maps becomes ordinary composition in the total category. -/
@[simp]
theorem toTotalHom_comp (m : Map f R S) (n : Map g S T) :
    (Map.comp m n).toTotalHom = m.toTotalHom ≫ n.toTotalHom := sorry

/-- Reindexing a dependent map does not change its associated total morphism. -/
@[simp]
theorem toTotalHom_reindex {f' : X ⟶ Y} (h : f = f') (m : Map f R S) :
    (Map.reindex h m).toTotalHom = m.toTotalHom := sorry

end Map

namespace Total

/-- Extract the dependent map represented by a total right-resolution morphism. -/
@[stacks 0GSL "dependent map underlying a total right-resolution morphism"]
def toMap {R S : Total Φ} (f : R ⟶ S) :
    Map (baseHom f) R.toResolution S.toResolution where
  modelHom := modelHom f
  comparison_naturality := naturality f

/-- Extracting a dependent map preserves the model component. -/
@[simp]
theorem toMap_modelHom {R S : Total Φ} (f : R ⟶ S) :
    (toMap f).modelHom = modelHom f := sorry

/-- Extracting a dependent map preserves the image of the model component. -/
@[simp]
theorem toMap_hom {R S : Total Φ} (f : R ⟶ S) :
    (toMap f).hom = Φ.functor.map (modelHom f) := sorry

/-- Construct a total morphism from a dependent map between the represented fiberwise
resolutions. -/
@[stacks 0GSL "total morphism from a dependent right-resolution map"]
def ofMap {R S : Total Φ} {f : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution) : R ⟶ S :=
  homMk f m.modelHom m.comparison_naturality

/-- The base component of a total morphism constructed from a dependent map. -/
@[simp]
theorem ofMap_baseHom {R S : Total Φ} {f : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution) : baseHom (ofMap m) = f := sorry

/-- The model component of a total morphism constructed from a dependent map. -/
@[simp]
theorem ofMap_modelHom {R S : Total Φ} {f : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution) :
    modelHom (ofMap m) = m.modelHom := sorry

/-- Converting a total morphism to a dependent map and back recovers it. -/
@[simp]
theorem ofMap_toMap {R S : Total Φ} (f : R ⟶ S) : ofMap (toMap f) = f := sorry

/-- Converting a dependent map to a total morphism and back recovers it after reindexing along
the computed base component. -/
@[simp]
theorem toMap_ofMap {R S : Total Φ} {f : R.base ⟶ S.base}
    (m : Map f R.toResolution S.toResolution) :
    Map.reindex (ofMap_baseHom m) (toMap (ofMap m)) = m := sorry

/-- The dependent map of an identity total morphism is the identity after canonical
reindexing. -/
@[simp]
theorem toMap_id (R : Total Φ) :
    Map.reindex (id_baseHom R) (toMap (𝟙 R)) = Map.id R.toResolution := sorry

/-- The dependent map of a composite is the composite of the dependent maps after canonical
reindexing. -/
@[simp]
theorem toMap_comp {R S T : Total Φ} (f : R ⟶ S) (g : S ⟶ T) :
    Map.reindex (comp_baseHom f g) (toMap (f ≫ g)) =
      Map.comp (toMap f) (toMap g) := sorry

end Total

end CategoryTheory.LocalizerMorphism.RightResolution
