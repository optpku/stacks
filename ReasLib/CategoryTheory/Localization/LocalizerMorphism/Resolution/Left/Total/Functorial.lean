/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Functorial
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Total.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial Left Resolutions in the Total Category

A functorial family of left resolutions is canonically a functor to the total resolution
category.  This packaging absorbs the dependent reindexing in `FunctorialAlong.map_id` and
`FunctorialAlong.map_comp` into ordinary functor laws.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LocalizerMorphism.LeftResolution.FunctorialAlong

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂}
  {D : Type u₃} [Category.{v₃} D] {F : D ⥤ C₂}

/-- The total resolution selected by functorial data at an indexing object. -/
def totalObj (R : FunctorialAlong Φ F) (X : D) : Total Φ :=
  Total.ofResolution (R.resolution X)

/-- The total morphism selected by functorial data at an indexing morphism. -/
def totalMap (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    R.totalObj X ⟶ R.totalObj Y :=
  (R.map f).toTotalHom

/-- The selected total morphism preserves identities. -/
theorem totalMap_id (R : FunctorialAlong Φ F) (X : D) :
    R.totalMap (𝟙 X) = 𝟙 (R.totalObj X) := sorry

/-- The selected total morphism preserves composition. -/
theorem totalMap_comp (R : FunctorialAlong Φ F)
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R.totalMap (f ≫ g) = R.totalMap f ≫ R.totalMap g := sorry

/-- A functorial family of left resolutions, assembled as a functor to the total category. -/
@[stacks 0GSL "functor to the total category of left resolutions"]
def total (R : FunctorialAlong Φ F) : D ⥤ Total Φ where
  obj X := R.totalObj X
  map f := R.totalMap f
  map_id := R.totalMap_id
  map_comp := R.totalMap_comp

namespace total

/-- The base of a selected total object is the corresponding value of the input functor. -/
@[simp]
theorem obj_base (R : FunctorialAlong Φ F) (X : D) :
    (R.total.obj X).base = F.obj X := sorry

/-- The model of a selected total object is the corresponding value of the model functor. -/
@[simp]
theorem obj_model (R : FunctorialAlong Φ F) (X : D) :
    (R.total.obj X).model = R.model.obj X := sorry

/-- The comparison of a selected total object is the corresponding component of the functorial
comparison. -/
@[simp]
theorem obj_comparison (R : FunctorialAlong Φ F) (X : D) :
    (R.total.obj X).comparison = R.comparison.app X := sorry

/-- The base component of a selected total morphism is the map of the input functor. -/
@[simp]
theorem map_baseHom (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    Total.baseHom (R.total.map f) = F.map f := sorry

/-- The model component of a selected total morphism is the map of the model functor. -/
@[simp]
theorem map_modelHom (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    Total.modelHom (R.total.map f) = R.model.map f := sorry

/-- Projecting a functorial total left resolution to its base recovers the input functor. -/
theorem comp_base (R : FunctorialAlong Φ F) :
    R.total ⋙ Total.baseFunctor Φ = F := sorry

/-- Projecting a functorial total left resolution to its models recovers the model functor. -/
theorem comp_model (R : FunctorialAlong Φ F) :
    R.total ⋙ Total.modelFunctor Φ = R.model := sorry

end total

end CategoryTheory.LocalizerMorphism.LeftResolution.FunctorialAlong
