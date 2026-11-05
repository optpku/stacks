module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Resolution.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right Resolutions by Objects Satisfying a Property

This file specializes Mathlib's right-resolution objects to a full subcategory cut out by an
arbitrary object property.  It exposes the ambient model, comparison, morphism, and naturality
API while retaining Mathlib's resolution category.
-/

@[expose] public section

open CategoryTheory.Localization CategoryTheory.MorphismProperty

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D]

/-- A right resolution of `X` by an object satisfying `P`, with comparison in `S`. -/
@[stacks 0GSL "right resolution by a full subcategory"]
abbrev RightResolution (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :=
  (fullSubcategoryLocalizerMorphism P S).RightResolution X

/-- Every object has a right resolution by an object satisfying `P`, with comparison in `S`. -/
abbrev HasRightResolutions (P : ObjectProperty D) (S : MorphismProperty D) :=
  (fullSubcategoryLocalizerMorphism P S).HasRightResolutions

namespace RightResolution

variable {P : ObjectProperty D} {S : MorphismProperty D} {X : D}

/-- Construct a right resolution from an explicit model and comparison. -/
def mk (Y : P.FullSubcategory) (f : X ⟶ Y.obj) (hf : S f) :
    RightResolution P S X where
  X₁ := Y
  w := f
  hw := hf

/-- The bundled model satisfying `P`. -/
abbrev model (R : RightResolution P S X) : P.FullSubcategory :=
  LocalizerMorphism.RightResolution.model R

/-- The ambient object underlying the model. -/
abbrev object (R : RightResolution P S X) : D :=
  R.model.obj

/-- The comparison from the original object to the model. -/
abbrev comparison (R : RightResolution P S X) : X ⟶ R.object :=
  LocalizerMorphism.RightResolution.comparison R

/-- The morphism between the bundled models underlying a morphism of right resolutions. -/
abbrev modelHom {R R' : RightResolution P S X} (f : R ⟶ R') : R.model ⟶ R'.model :=
  LocalizerMorphism.RightResolution.modelHom f

/-- The ambient morphism underlying a morphism of right resolutions. -/
abbrev hom {R R' : RightResolution P S X} (f : R ⟶ R') : R.object ⟶ R'.object :=
  LocalizerMorphism.RightResolution.hom f

/-- The model of a right resolution satisfies the chosen object property. -/
theorem model_mem (R : RightResolution P S X) : P R.object := sorry

/-- The comparison of a right resolution belongs to the chosen morphism property. -/
theorem comparison_mem (R : RightResolution P S X) : S R.comparison := sorry

/-- The identity morphism of right resolutions induces the identity between bundled models. -/
@[simp]
theorem id_modelHom (R : RightResolution P S X) :
    modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Composition of right-resolution morphisms induces composition between bundled models. -/
@[simp]
theorem comp_modelHom {R R' R'' : RightResolution P S X} (f : R ⟶ R') (g : R' ⟶ R'') :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The identity morphism of right resolutions induces the ambient identity. -/
@[simp]
theorem id_hom (R : RightResolution P S X) :
    hom (𝟙 R) = 𝟙 R.object := sorry

/-- Composition of right-resolution morphisms induces composition of ambient morphisms. -/
@[simp]
theorem comp_hom {R R' R'' : RightResolution P S X} (f : R ⟶ R') (g : R' ⟶ R'') :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of right resolutions commutes with the comparisons in the ambient category. -/
@[reassoc]
theorem comparison_naturality {R R' : RightResolution P S X} (f : R ⟶ R') :
    R.comparison ≫ hom f = R'.comparison := sorry

/-- The functor selecting the bundled model of each right resolution. -/
@[stacks 0GSL "right-resolution model functor"]
abbrev modelFunctor (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :
    RightResolution P S X ⥤ P.FullSubcategory :=
  LocalizerMorphism.RightResolution.modelFunctor (fullSubcategoryLocalizerMorphism P S) X

/-- The model functor returns the bundled model of a right resolution. -/
@[simp]
theorem modelFunctor_obj (R : RightResolution P S X) :
    (modelFunctor P S X).obj R = R.model := sorry

/-- The model functor maps a resolution morphism to its bundled model morphism. -/
@[simp]
theorem modelFunctor_map {R R' : RightResolution P S X} (f : R ⟶ R') :
    (modelFunctor P S X).map f = modelHom f := sorry

/-- The functor selecting the ambient object underlying each right-resolution model. -/
@[stacks 0GSL "right-resolution ambient model functor"]
abbrev objectFunctor (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :
    RightResolution P S X ⥤ D :=
  LocalizerMorphism.RightResolution.objectFunctor (fullSubcategoryLocalizerMorphism P S) X

/-- The ambient model functor returns the object underlying a right-resolution model. -/
@[simp]
theorem objectFunctor_obj (R : RightResolution P S X) :
    (objectFunctor P S X).obj R = R.object := sorry

/-- The ambient model functor maps a resolution morphism to its ambient morphism. -/
@[simp]
theorem objectFunctor_map {R R' : RightResolution P S X} (f : R ⟶ R') :
    (objectFunctor P S X).map f = hom f := sorry

/-- Naturality of the right-resolution comparisons in functorial form. -/
theorem comparisonNatTrans_naturality {R R' : RightResolution P S X} (f : R ⟶ R') :
    ((Functor.const (RightResolution P S X)).obj X).map f ≫ R'.comparison =
      R.comparison ≫ (objectFunctor P S X).map f := sorry

/-- The comparisons from `X` to its right-resolution models form a natural transformation. -/
@[stacks 0GSL "natural family of right-resolution comparisons"]
abbrev comparisonNatTrans (P : ObjectProperty D) (S : MorphismProperty D) (X : D) :
    (Functor.const (RightResolution P S X)).obj X ⟶ objectFunctor P S X :=
  LocalizerMorphism.RightResolution.comparisonNatTrans (fullSubcategoryLocalizerMorphism P S) X

/-- Evaluating the natural comparison at a right resolution gives its comparison morphism. -/
@[simp]
theorem comparisonNatTrans_app (R : RightResolution P S X) :
    (comparisonNatTrans P S X).app R = R.comparison := sorry

/-- Right resolutions are nonempty exactly when an explicit model and comparison exist. -/
theorem nonempty_iff :
    Nonempty (RightResolution P S X) ↔
      ∃ (Y : P.FullSubcategory) (f : X ⟶ Y.obj), S f := sorry

/-- The model selected by `mk` is the supplied object. -/
@[simp]
theorem mk_model (Y : P.FullSubcategory) (f : X ⟶ Y.obj) (hf : S f) :
    (mk Y f hf).model = Y := sorry

/-- The comparison selected by `mk` is the supplied morphism. -/
@[simp]
theorem mk_comparison (Y : P.FullSubcategory) (f : X ⟶ Y.obj) (hf : S f) :
    (mk Y f hf).comparison = f := sorry

end RightResolution

end CategoryTheory.ObjectProperty


