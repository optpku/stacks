/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial API for Left Resolutions

This file exposes the data carried by Mathlib's category of left resolutions of a localizer
morphism.  In particular, the resolving objects and their images in the target category vary
functorially, and the comparison maps form a natural transformation.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism.LeftResolution

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {Φ : LocalizerMorphism W₁ W₂} {X₂ : C₂}

/-- The resolving object in the source category of a localizer morphism. -/
abbrev model (R : Φ.LeftResolution X₂) : C₁ :=
  R.X₁

/-- The comparison from the image of a resolving model to the target object. -/
abbrev comparison (R : Φ.LeftResolution X₂) : Φ.functor.obj R.model ⟶ X₂ :=
  R.w

/-- The morphism of resolving models underlying a morphism of left resolutions. -/
abbrev modelHom {R R' : Φ.LeftResolution X₂} (f : R ⟶ R') : R.model ⟶ R'.model :=
  f.f

/-- The image in the target category of a morphism of resolving models. -/
abbrev hom {R R' : Φ.LeftResolution X₂} (f : R ⟶ R') :
    Φ.functor.obj R.model ⟶ Φ.functor.obj R'.model :=
  Φ.functor.map (modelHom f)

/-- The comparison of a left resolution belongs to the target localization system. -/
theorem comparison_mem (R : Φ.LeftResolution X₂) : W₂ R.comparison := sorry

/-- The model morphism underlying the identity of a left resolution is an identity. -/
@[simp]
theorem id_modelHom (R : Φ.LeftResolution X₂) :
    modelHom (𝟙 R) = 𝟙 R.model := sorry

/-- Model morphisms preserve composition of left-resolution morphisms. -/
@[simp]
theorem comp_modelHom {R R' R'' : Φ.LeftResolution X₂} (f : R ⟶ R') (g : R' ⟶ R'') :
    modelHom (f ≫ g) = modelHom f ≫ modelHom g := sorry

/-- The target morphism underlying the identity of a left resolution is an identity. -/
@[simp]
theorem id_hom (R : Φ.LeftResolution X₂) :
    hom (𝟙 R) = 𝟙 (Φ.functor.obj R.model) := sorry

/-- Target morphisms preserve composition of left-resolution morphisms. -/
@[simp]
theorem comp_hom {R R' R'' : Φ.LeftResolution X₂} (f : R ⟶ R') (g : R' ⟶ R'') :
    hom (f ≫ g) = hom f ≫ hom g := sorry

/-- A morphism of left resolutions commutes with the comparison maps. -/
@[reassoc]
theorem comparison_naturality {R R' : Φ.LeftResolution X₂} (f : R ⟶ R') :
    hom f ≫ R'.comparison = R.comparison := sorry

/-- The functor selecting the source-category model of each left resolution. -/
@[stacks 0GSL "left-resolution model functor for a localizer morphism"]
def modelFunctor (Φ : LocalizerMorphism W₁ W₂) (X₂ : C₂) :
    Φ.LeftResolution X₂ ⥤ C₁ where
  obj R := R.model
  map f := modelHom f
  map_id := id_modelHom
  map_comp := comp_modelHom

/-- The model functor returns the resolving model. -/
@[simp]
theorem modelFunctor_obj (R : Φ.LeftResolution X₂) :
    (modelFunctor Φ X₂).obj R = R.model := sorry

/-- The model functor returns the underlying model morphism. -/
@[simp]
theorem modelFunctor_map {R R' : Φ.LeftResolution X₂} (f : R ⟶ R') :
    (modelFunctor Φ X₂).map f = modelHom f := sorry

/-- The functor selecting the image of each resolving model in the target category. -/
@[stacks 0GSL "left-resolution target-model functor for a localizer morphism"]
abbrev objectFunctor (Φ : LocalizerMorphism W₁ W₂) (X₂ : C₂) :
    Φ.LeftResolution X₂ ⥤ C₂ :=
  modelFunctor Φ X₂ ⋙ Φ.functor

/-- The target-model functor returns the image of the resolving model. -/
@[simp]
theorem objectFunctor_obj (R : Φ.LeftResolution X₂) :
    (objectFunctor Φ X₂).obj R = Φ.functor.obj R.model := sorry

/-- The target-model functor returns the image of the underlying model morphism. -/
@[simp]
theorem objectFunctor_map {R R' : Φ.LeftResolution X₂} (f : R ⟶ R') :
    (objectFunctor Φ X₂).map f = hom f := sorry

/-- Naturality of left-resolution comparisons in functorial form. -/
theorem comparisonNatTrans_naturality {R R' : Φ.LeftResolution X₂} (f : R ⟶ R') :
    (objectFunctor Φ X₂).map f ≫ R'.comparison =
      R.comparison ≫ ((Functor.const (Φ.LeftResolution X₂)).obj X₂).map f := sorry

/-- The comparisons from left-resolution models to an object form a natural transformation. -/
@[stacks 0GSL "natural family of left-resolution comparisons for a localizer morphism"]
def comparisonNatTrans (Φ : LocalizerMorphism W₁ W₂) (X₂ : C₂) :
    objectFunctor Φ X₂ ⟶ (Functor.const (Φ.LeftResolution X₂)).obj X₂ :=
  { app := comparison
    naturality := fun _ _ f => comparisonNatTrans_naturality f }

/-- Evaluating the natural comparison at a resolution returns its comparison map. -/
@[simp]
theorem comparisonNatTrans_app (R : Φ.LeftResolution X₂) :
    (comparisonNatTrans Φ X₂).app R = R.comparison := sorry

/-- Left resolutions are nonempty exactly when an explicit model and comparison exist. -/
theorem nonempty_iff :
    Nonempty (Φ.LeftResolution X₂) ↔
      ∃ (Y : C₁) (f : Φ.functor.obj Y ⟶ X₂), W₂ f := sorry

end CategoryTheory.LocalizerMorphism.LeftResolution


