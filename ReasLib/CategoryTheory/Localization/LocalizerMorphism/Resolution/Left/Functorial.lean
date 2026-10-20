module

public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial Left Resolutions Along a Functor

Rather than requiring chosen resolutions for every object of a target category, this file
packages a coherent choice only along a specified functor.  Its action on morphisms is exposed as
a map of left resolutions over the corresponding target morphism.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.LocalizerMorphism.LeftResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- A functorial choice of left resolutions along `F`. -/
@[stacks 0GSL "functorial left resolutions along a functor"]
structure FunctorialAlong (Φ : LocalizerMorphism W₁ W₂)
    {D : Type u₃} [Category.{v₃} D] (F : D ⥤ C₂) where
  /-- The functor of resolving models. -/
  model : D ⥤ C₁
  /-- The natural family of comparisons from the images of the resolving models. -/
  comparison : model ⋙ Φ.functor ⟶ F
  /-- Every comparison belongs to the target localization system. -/
  comparison_mem (X : D) : W₂ (comparison.app X)

namespace FunctorialAlong

variable {Φ : LocalizerMorphism W₁ W₂}
  {D : Type u₃} [Category.{v₃} D] {F : D ⥤ C₂}

/-- The left resolution selected at an object of the indexing category. -/
@[stacks 0GSL "left resolution selected by functorial data"]
def resolution (R : FunctorialAlong Φ F) (X : D) : Φ.LeftResolution (F.obj X) where
  X₁ := R.model.obj X
  w := R.comparison.app X
  hw := R.comparison_mem X

/-- The selected resolution has the model supplied by the model functor. -/
@[simp]
theorem resolution_model (R : FunctorialAlong Φ F) (X : D) :
    (R.resolution X).model = R.model.obj X := sorry

/-- The selected resolution has the corresponding component of the comparison. -/
@[simp]
theorem resolution_comparison (R : FunctorialAlong Φ F) (X : D) :
    (R.resolution X).comparison = R.comparison.app X := sorry

/-- Naturality of the comparison gives the comparison square for a morphism of selected left
resolutions. -/
theorem map_naturality (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    Φ.functor.map (R.model.map f) ≫ (R.resolution Y).comparison =
      (R.resolution X).comparison ≫ F.map f := sorry

/-- A morphism in the indexing category induces a map of the selected left resolutions. -/
@[stacks 0GSL "map of functorially selected left resolutions"]
def map (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    Map (F.map f) (R.resolution X) (R.resolution Y) where
  modelHom := R.model.map f
  comparison_naturality := R.map_naturality f

/-- The induced resolution map uses the map supplied by the model functor. -/
@[simp]
theorem map_modelHom (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    (R.map f).modelHom = R.model.map f := sorry

/-- The target-model morphism of the induced resolution map is the image of the model-functor
map. -/
@[simp]
theorem map_hom (R : FunctorialAlong Φ F) {X Y : D} (f : X ⟶ Y) :
    (R.map f).hom = Φ.functor.map (R.model.map f) := sorry

/-- The whiskered comparison of a precomposed functorial left resolution remains in the target
localization system. -/
theorem precomp_comparison_mem (R : FunctorialAlong Φ F)
    {E : Type u₄} [Category.{v₄} E] (G : E ⥤ D) (X : E) :
    W₂ ((Functor.whiskerLeft G R.comparison).app X) := sorry

/-- Precompose functorial left-resolution data with a functor of indexing categories. -/
@[stacks 0GSL "precomposition of functorial left resolutions"]
def precomp (R : FunctorialAlong Φ F)
    {E : Type u₄} [Category.{v₄} E] (G : E ⥤ D) :
    FunctorialAlong Φ (G ⋙ F) where
  model := G ⋙ R.model
  comparison := Functor.whiskerLeft G R.comparison
  comparison_mem := R.precomp_comparison_mem G

/-- Precomposition uses the composite resolving-model functor. -/
@[simp]
theorem precomp_model (R : FunctorialAlong Φ F)
    {E : Type u₄} [Category.{v₄} E] (G : E ⥤ D) :
    (R.precomp G).model = G ⋙ R.model := sorry

/-- Precomposition uses the left-whiskered comparison. -/
@[simp]
theorem precomp_comparison (R : FunctorialAlong Φ F)
    {E : Type u₄} [Category.{v₄} E] (G : E ⥤ D) :
    (R.precomp G).comparison = Functor.whiskerLeft G R.comparison := sorry

/-- The resolution selected after precomposition is the resolution selected at the image
object. -/
@[simp]
theorem precomp_resolution (R : FunctorialAlong Φ F)
    {E : Type u₄} [Category.{v₄} E] (G : E ⥤ D) (X : E) :
    (R.precomp G).resolution X = R.resolution (G.obj X) := sorry

/-- The resolution map selected after precomposition is the map selected on the image
morphism. -/
@[simp]
theorem precomp_map (R : FunctorialAlong Φ F)
    {E : Type u₄} [Category.{v₄} E] (G : E ⥤ D)
    {X Y : E} (f : X ⟶ Y) :
    (R.precomp G).map f = R.map (G.map f) := sorry

/-- The selected map of an identity agrees with the identity resolution map after reindexing. -/
@[simp]
theorem map_id (R : FunctorialAlong Φ F) (X : D) :
    Map.reindex (F.map_id X) (R.map (𝟙 X)) = Map.id (R.resolution X) := sorry

/-- The selected map of a composite agrees with the composite of the selected maps after
reindexing. -/
@[simp]
theorem map_comp (R : FunctorialAlong Φ F) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R.map (f ≫ g) =
      Map.reindex (F.map_comp f g).symm (Map.comp (R.map f) (R.map g)) := sorry

end FunctorialAlong

/-- A functorial choice of left resolutions for all objects of the target category. -/
@[stacks 0GSL "functorial left resolutions"]
abbrev Functorial (Φ : LocalizerMorphism W₁ W₂) :=
  FunctorialAlong Φ (Functor.id C₂)

end CategoryTheory.LocalizerMorphism.LeftResolution
