module

public import ReasLib.CategoryTheory.Filtration.Object

/-!
# Morphisms of Filtered Objects

A morphism of filtered objects is a morphism in the ambient category that preserves each
filtration stage. We define the `stageMap` (the induced map on stages) and prove naturality
with respect to the consecutive inclusions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

/-- A morphism of filtered objects: an ambient morphism that factors through each target stage. -/
@[ext]
structure Hom (X Y : FilteredObject C) where
  /-- The underlying morphism in the ambient category. -/
  hom : X.obj ⟶ Y.obj
  /-- Each source stage maps into the corresponding target stage. -/
  preserves (i : ℤ) : (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ hom)

namespace Hom

variable {X Y Z : FilteredObject C}

/-- The induced morphism on the `p`-th filtration stages. -/
noncomputable abbrev stageMap (f : Hom X Y) (p : ℤ) : X.stage p ⟶ Y.stage p :=
  (Y.filtration.stage p).factorThru
    ((X.filtration.stage p).arrow ≫ f.hom) (f.preserves p)

/-- The stage map is the restriction of the ambient morphism to filtration stages. -/
@[simp]
theorem stageMap_arrow (f : Hom X Y) (p : ℤ) :
    f.stageMap p ≫ (Y.filtration.stage p).arrow = (X.filtration.stage p).arrow ≫ f.hom :=
  Subobject.factorThru_arrow _ _ (f.preserves p)

/-- The stage maps commute with consecutive inclusions. -/
theorem succInclusion_naturality (f : Hom X Y) (p : ℤ) :
    X.filtration.succInclusion p ≫ f.stageMap p =
      f.stageMap (p + 1) ≫ Y.filtration.succInclusion p := by
  apply (cancel_mono (Y.filtration.stage p).arrow).1
  simp only [Category.assoc, stageMap_arrow, DecreasingFiltration.succInclusion_arrow]
  simp only [← Category.assoc, DecreasingFiltration.succInclusion_arrow]

/-- The identity morphism of a filtered object. -/
def id (X : FilteredObject C) : Hom X X where
  hom := 𝟙 X.obj
  preserves i := by simpa using (X.filtration.stage i).factors_self

/-- Composition of filtration-preserving morphisms. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  hom := f.hom ≫ g.hom
  preserves i := by
    simpa [stageMap, Category.assoc] using
      Subobject.factors_comp_arrow
        (f.stageMap i ≫ g.stageMap i : (X.filtration.stage i : C) ⟶ Z.filtration.stage i)

end Hom

/-- Identity is a left unit. -/
theorem id_comp_eq {X Y : FilteredObject C} (f : Hom X Y) :
    Hom.comp (Hom.id X) f = f := by ext; simp [Hom.comp, Hom.id]

/-- Identity is a right unit. -/
theorem comp_id_eq {X Y : FilteredObject C} (f : Hom X Y) :
    Hom.comp f (Hom.id Y) = f := by ext; simp [Hom.comp, Hom.id]

/-- Composition is associative. -/
theorem assoc_eq {W X Y Z : FilteredObject C} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  ext; simp [Hom.comp, Category.assoc]

section Functoriality

variable {X Y Z : FilteredObject C}

/-- The stage map of the identity is the identity. -/
@[simp]
theorem Hom.stageMap_id (X : FilteredObject C) (p : ℤ) :
    (Hom.id X).stageMap p = 𝟙 (X.stage p) := by
  apply (cancel_mono (X.filtration.stage p).arrow).1
  simp [Hom.id]

/-- The stage map of a composite is the composite of stage maps. -/
@[simp]
theorem Hom.stageMap_comp (f : Hom X Y) (g : Hom Y Z) (p : ℤ) :
    (Hom.comp f g).stageMap p = f.stageMap p ≫ g.stageMap p := by
  apply (cancel_mono (Z.filtration.stage p).arrow).1
  simp [Hom.comp, Category.assoc]

end Functoriality

end FilteredObject

end CategoryTheory
