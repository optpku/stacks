/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor

/-!
# Augmentation transformations for Cartan--Eilenberg totals

The augmentation of a Cartan--Eilenberg resolution is natural on the category of bundled
resolutions, both before and after applying an additive functor.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

namespace Total

/-- The Cartan--Eilenberg augmentation as a morphism of bounded-below complexes. -/
@[stacks 015J "bounded-below Cartan-Eilenberg total augmentation"]
noncomputable def augmentationApp (X : Bundled A) :
    X.base ⟶ CartanEilenbergResolution.Total.toPlus X.resolution :=
  ⟨CartanEilenbergResolution.Total.augmentation X.resolution⟩

/-- Forgetting bounded-below structure from the augmentation component recovers the raw
Cartan--Eilenberg augmentation. -/
@[simp, stacks 015J "bounded-below Cartan-Eilenberg total augmentation"]
theorem augmentationApp_hom (X : Bundled A) :
    (augmentationApp X).hom =
      CartanEilenbergResolution.Total.augmentation X.resolution := sorry

/-- Naturality of the bounded-below Cartan--Eilenberg augmentation. -/
@[reassoc, stacks 015J "naturality of the bounded-below Cartan-Eilenberg total augmentation"]
theorem augmentation_naturality {X Y : Bundled A} (f : X ⟶ Y) :
    (source A).map f ≫ augmentationApp Y =
      augmentationApp X ≫ totalPlus.map f := sorry

/-- The bounded-below Cartan--Eilenberg augmentation as a natural transformation. -/
@[stacks 015J "bounded-below Cartan-Eilenberg total augmentation"]
noncomputable def augmentation : source A ⟶ totalPlus where
  app := augmentationApp
  naturality _ _ f := augmentation_naturality f

/-- A component of the bounded-below augmentation transformation is the canonical
Cartan--Eilenberg augmentation. -/
@[simp, stacks 015J "bounded-below Cartan-Eilenberg total augmentation"]
theorem augmentation_app (X : Bundled A) :
    augmentation.app X = augmentationApp X := sorry

/-- Forget bounded-below structure on source complexes. -/
noncomputable abbrev sourceComplex : Bundled A ⥤ CochainComplex A ℤ :=
  source A ⋙ CochainComplex.Plus.ι A

/-- The raw augmentation source-complex functor returns the stored source complex. -/
@[simp, stacks 015J "object computation for the raw augmentation source functor"]
theorem sourceComplex_obj (X : Bundled A) :
    sourceComplex.obj X = X.base.obj := sorry

/-- The raw augmentation source-complex functor returns the underlying source map. -/
@[simp, stacks 015J "map computation for the raw augmentation source functor"]
theorem sourceComplex_map {X Y : Bundled A} (f : X ⟶ Y) :
    sourceComplex.map f = f.base.hom := sorry

/-- Naturality of the raw Cartan--Eilenberg total augmentation. -/
@[reassoc, stacks 015J "naturality of the Cartan-Eilenberg total augmentation"]
theorem underlyingAugmentation_naturality {X Y : Bundled A} (f : X ⟶ Y) :
    sourceComplex.map f ≫
        CartanEilenbergResolution.Total.augmentation Y.resolution =
      CartanEilenbergResolution.Total.augmentation X.resolution ≫
        (CochainComplex.CartanEilenbergResolution.Bundled.total :
          Bundled A ⥤ CochainComplex A ℤ).map f := sorry

/-- The raw Cartan--Eilenberg total augmentation as a natural transformation. -/
@[stacks 015J "Cartan-Eilenberg total augmentation"]
noncomputable def underlyingAugmentation :
    sourceComplex ⟶
      (CochainComplex.CartanEilenbergResolution.Bundled.total :
        Bundled A ⥤ CochainComplex A ℤ) where
  app X := CartanEilenbergResolution.Total.augmentation X.resolution
  naturality _ _ f := underlyingAugmentation_naturality f

/-- A component of the raw total augmentation is the canonical pointwise augmentation. -/
@[simp, stacks 015J "Cartan-Eilenberg total augmentation"]
theorem underlyingAugmentation_app (X : Bundled A) :
    underlyingAugmentation.app X =
      CartanEilenbergResolution.Total.augmentation X.resolution := sorry

end Total

namespace MappedTotal

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Apply an additive functor termwise to the source complexes of bundled resolutions. -/
noncomputable abbrev sourceComplex (F : A ⥤ B) [F.Additive] :
    Bundled A ⥤ CochainComplex B ℤ :=
  source A ⋙ CochainComplex.Plus.ι A ⋙ F.mapHomologicalComplex (up ℤ)

/-- The mapped augmentation source-complex functor returns the termwise image of the source. -/
@[simp, stacks 015J "object computation for the mapped augmentation source functor"]
theorem sourceComplex_obj (F : A ⥤ B) [F.Additive] (X : Bundled A) :
    (sourceComplex F).obj X =
      (F.mapHomologicalComplex (up ℤ)).obj X.base.obj := sorry

/-- The mapped augmentation source-complex functor returns the termwise image of the source map. -/
@[simp, stacks 015J "map computation for the mapped augmentation source functor"]
theorem sourceComplex_map (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (sourceComplex F).map f =
      (F.mapHomologicalComplex (up ℤ)).map f.base.hom := sorry

/-- Naturality of the mapped Cartan--Eilenberg augmentation. -/
@[reassoc, stacks 015J "naturality of the mapped Cartan-Eilenberg total augmentation"]
theorem augmentation_naturality (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (sourceComplex F).map f ≫
        CartanEilenbergResolution.MappedTotal.augmentation Y.resolution F =
      CartanEilenbergResolution.MappedTotal.augmentation X.resolution F ≫
        (mappedTotal F).map f := sorry

/-- The mapped Cartan--Eilenberg augmentation as a natural transformation. -/
@[stacks 015J "mapped Cartan-Eilenberg total augmentation"]
noncomputable def augmentation (F : A ⥤ B) [F.Additive] :
    sourceComplex F ⟶ mappedTotal F where
  app X := CartanEilenbergResolution.MappedTotal.augmentation X.resolution F
  naturality _ _ f := augmentation_naturality F f

/-- A component of the mapped augmentation transformation is the canonical pointwise
augmentation. -/
@[simp, stacks 015J "mapped Cartan-Eilenberg total augmentation"]
theorem augmentation_app (F : A ⥤ B) [F.Additive] (X : Bundled A) :
    (augmentation F).app X =
      CartanEilenbergResolution.MappedTotal.augmentation X.resolution F := sorry

end MappedTotal

end CochainComplex.CartanEilenbergResolution.Bundled
