/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Left
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Left Resolutions by Objects Satisfying a Property

This file specializes Mathlib's left-resolution objects to a full subcategory cut out by an
arbitrary object property.  It exposes the ambient model, comparison, morphism, and naturality
API while retaining Mathlib's resolution category.
-/

@[expose] public section

open CategoryTheory.Localization CategoryTheory.MorphismProperty

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D]

/-- A left resolution of `X` by an object satisfying `P`, with comparison in `S`. -/
@[stacks 0GSL "left resolution by a full subcategory"]
abbrev LeftResolution (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :=
  (fullSubcategoryLocalizerMorphism P S).LeftResolution X

/-- Every object has a left resolution by an object satisfying `P`, with comparison in `S`. -/
abbrev HasLeftResolutions (P : ObjectProperty D) (S : MorphismProperty D) :=
  (fullSubcategoryLocalizerMorphism P S).HasLeftResolutions

namespace LeftResolution

variable {P : ObjectProperty D} {S : MorphismProperty D} {X : D}

/-- Construct a left resolution from an explicit model and comparison. -/
def mk (Y : P.FullSubcategory) (f : Y.obj ⟶ X) (hf : S f) :
    LeftResolution P S X where
  X₁ := Y
  w := f
  hw := hf

/-- The bundled model satisfying `P`. -/
abbrev model (R : LeftResolution P S X) : P.FullSubcategory :=
  LocalizerMorphism.LeftResolution.model R

/-- The ambient object underlying the model. -/
abbrev object (R : LeftResolution P S X) : D :=
  R.model.obj

/-- The comparison from the model to the original object. -/
abbrev comparison (R : LeftResolution P S X) : R.object ⟶ X :=
  LocalizerMorphism.LeftResolution.comparison R

/-- The morphism between the bundled models underlying a morphism of left resolutions. -/
abbrev modelHom {R R' : LeftResolution P S X} (f : R ⟶ R') : R.model ⟶ R'.model :=
  LocalizerMorphism.LeftResolution.modelHom f

/-- The ambient morphism underlying a morphism of left resolutions. -/
abbrev hom {R R' : LeftResolution P S X} (f : R ⟶ R') : R.object ⟶ R'.object :=
  LocalizerMorphism.LeftResolution.hom f

/-- The model of a left resolution satisfies the chosen object property. -/
theorem model_mem (R : LeftResolution P S X) : P R.object := sorry

/-- The comparison of a left resolution belongs to the chosen morphism property. -/
theorem comparison_mem (R : LeftResolution P S X) : S R.comparison := sorry

/-- The identity morphism of left resolutions induces the identity between bundled models. -/
@[simp]
theorem id_modelHom (R : LeftResolution P S X) :
    modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Composition of left-resolution morphisms induces composition between bundled models. -/
@[simp]
theorem comp_modelHom {R R' R'' : LeftResolution P S X} (f : R ⟶ R') (g : R' ⟶ R'') :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity morphism of left resolutions induces the ambient identity. -/
@[simp]
theorem id_hom (R : LeftResolution P S X) :
    hom (𝟙 R) = 𝟙 R.object := sorry

/-- Composition of left-resolution morphisms induces composition of ambient morphisms. -/
@[simp]
theorem comp_hom {R R' R'' : LeftResolution P S X} (f : R ⟶ R') (g : R' ⟶ R'') :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of left resolutions commutes with the comparisons in the ambient category. -/
@[reassoc]
theorem comparison_naturality {R R' : LeftResolution P S X} (f : R ⟶ R') :
    hom f ≫ R'.comparison = R.comparison := sorry

/-- The functor selecting the bundled model of each left resolution. -/
@[stacks 0GSL "left-resolution model functor"]
abbrev modelFunctor (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :
    LeftResolution P S X ⥤ P.FullSubcategory :=
  LocalizerMorphism.LeftResolution.modelFunctor (fullSubcategoryLocalizerMorphism P S) X

/-- The model functor returns the bundled model of a left resolution. -/
@[simp]
theorem modelFunctor_obj (R : LeftResolution P S X) :
    (modelFunctor P S X).obj R = R.model := sorry

/-- The model functor maps a resolution morphism to its bundled model morphism. -/
@[simp]
theorem modelFunctor_map {R R' : LeftResolution P S X} (f : R ⟶ R') :
    (modelFunctor P S X).map f = modelHom f := sorry

/-- The functor selecting the ambient object underlying each left-resolution model. -/
@[stacks 0GSL "left-resolution ambient model functor"]
abbrev objectFunctor (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :
    LeftResolution P S X ⥤ D :=
  LocalizerMorphism.LeftResolution.objectFunctor (fullSubcategoryLocalizerMorphism P S) X

/-- The ambient model functor returns the object underlying a left-resolution model. -/
@[simp]
theorem objectFunctor_obj (R : LeftResolution P S X) :
    (objectFunctor P S X).obj R = R.object := sorry

/-- The ambient model functor maps a resolution morphism to its ambient morphism. -/
@[simp]
theorem objectFunctor_map {R R' : LeftResolution P S X} (f : R ⟶ R') :
    (objectFunctor P S X).map f = hom f := sorry

/-- Naturality of the left-resolution comparisons in functorial form. -/
theorem comparisonNatTrans_naturality {R R' : LeftResolution P S X} (f : R ⟶ R') :
    (objectFunctor P S X).map f ≫ R'.comparison =
      R.comparison ≫ ((Functor.const (LeftResolution P S X)).obj X).map f := sorry

/-- The comparisons from left-resolution models to `X` form a natural transformation. -/
@[stacks 0GSL "natural family of left-resolution comparisons"]
abbrev comparisonNatTrans (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :
    objectFunctor P S X ⟶ (Functor.const (LeftResolution P S X)).obj X :=
  LocalizerMorphism.LeftResolution.comparisonNatTrans (fullSubcategoryLocalizerMorphism P S) X

/-- Evaluating the natural comparison at a left resolution gives its comparison morphism. -/
@[simp]
theorem comparisonNatTrans_app (R : LeftResolution P S X) :
    (comparisonNatTrans P S X).app R = R.comparison := sorry

/-- Left resolutions are nonempty exactly when an explicit model and comparison exist. -/
theorem nonempty_iff :
    Nonempty (LeftResolution P S X) ↔
      ∃ (Y : P.FullSubcategory) (f : Y.obj ⟶ X), S f := sorry

/-- The model selected by `mk` is the supplied object. -/
@[simp]
theorem mk_model (Y : P.FullSubcategory) (f : Y.obj ⟶ X) (hf : S f) :
    (mk Y f hf).model = Y := sorry

/-- The comparison selected by `mk` is the supplied morphism. -/
@[simp]
theorem mk_comparison (Y : P.FullSubcategory) (f : Y.obj ⟶ X) (hf : S f) :
    (mk Y f hf).comparison = f := sorry

end LeftResolution

end CategoryTheory.ObjectProperty


