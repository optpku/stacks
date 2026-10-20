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

/-- An ambient morphism between explicit filtration data that preserves every stage. -/
@[ext]
structure Hom.Data (X Y : FilteredObject.Data C) where
  /-- The underlying morphism in the ambient category. -/
  hom : X.obj ⟶ Y.obj
  /-- Each source stage maps into the corresponding target stage. -/
  preserves (i : ℤ) : (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ hom)

/-- The category-facing type of filtration-preserving morphisms. -/
def Hom (X Y : FilteredObject C) := Hom.Data X.toData Y.toData

namespace Hom.Data

variable {X Y Z : FilteredObject.Data C}

/-- Restrict an explicit filtration-preserving morphism to a filtration stage. -/
noncomputable abbrev stageMap (f : Hom.Data X Y) (p : ℤ) : X.stage p ⟶ Y.stage p :=
  (Y.filtration.stage p).factorThru
    ((X.filtration.stage p).arrow ≫ f.hom) (f.preserves p)

/-- Composing the restricted morphism with the stage arrow gives the ambient morphism. -/
@[simp] theorem stageMap_arrow (f : Hom.Data X Y) (p : ℤ) :
    f.stageMap p ≫ (Y.filtration.stage p).arrow = (X.filtration.stage p).arrow ≫ f.hom :=
  Subobject.factorThru_arrow _ _ (f.preserves p)

/-- The explicit identity morphism preserves every filtration stage. -/
def id (X : FilteredObject.Data C) : Hom.Data X X where
  hom := 𝟙 X.obj
  preserves i := by simpa using (X.filtration.stage i).factors_self

/-- Compose two explicit filtration-preserving morphisms. -/
def comp (f : Hom.Data X Y) (g : Hom.Data Y Z) : Hom.Data X Z where
  hom := f.hom ≫ g.hom
  preserves i := by
    simpa [stageMap, Category.assoc] using
      Subobject.factors_comp_arrow
        (f.stageMap i ≫ g.stageMap i : (X.filtration.stage i : C) ⟶ Z.filtration.stage i)

/-- The ambient morphism of the explicit identity is the identity. -/
@[simp] theorem id_hom (X : FilteredObject.Data C) : (id X).hom = 𝟙 X.obj := rfl

/-- The ambient morphism of explicit composition is the composite of ambient morphisms. -/
@[simp] theorem comp_hom (f : Hom.Data X Y) (g : Hom.Data Y Z) :
    (comp f g).hom = f.hom ≫ g.hom := rfl

end Hom.Data

namespace Hom

variable {X Y Z : FilteredObject C}

/-- View explicit filtration-preserving morphism data as a categorical morphism. -/
def fromData (f : Data X.toData Y.toData) : Hom X Y := f

/-- Recover the explicit filtration-preserving data of a categorical morphism. -/
def toData (f : Hom X Y) : Data X.toData Y.toData := f

/-- Recovering the data of a morphism's categorical view returns that data. -/
@[simp] theorem toData_fromData (f : Data X.toData Y.toData) :
    (fromData f).toData = f := rfl

/-- The categorical view of a morphism's explicit data is the original morphism. -/
@[simp] theorem fromData_toData (f : Hom X Y) : fromData f.toData = f := rfl

/-- The ambient morphism underlying a filtration-preserving morphism. -/
abbrev hom (f : Hom X Y) : X.obj ⟶ Y.obj := f.toData.hom

/-- Passing to the categorical view preserves the ambient morphism. -/
@[simp] theorem fromData_hom (f : Data X.toData Y.toData) :
    (fromData f).hom = f.hom := rfl

/-- Each filtration stage maps into the corresponding target stage. -/
theorem preserves (f : Hom X Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ f.hom) :=
  f.toData.preserves i

/-- Construct a categorical morphism from an ambient morphism preserving each stage. -/
def mk (hom : X.obj ⟶ Y.obj)
    (preserves : ∀ i : ℤ,
      (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ hom)) : Hom X Y :=
  fromData ⟨hom, preserves⟩

/-- Filtration-preserving morphisms are equal if their ambient morphisms are equal. -/
@[ext] theorem ext {f g : Hom X Y} (h : f.hom = g.hom) : f = g := Data.ext h

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
def id (X : FilteredObject C) : Hom X X := fromData (Data.id X.toData)

/-- Composition of filtration-preserving morphisms. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  fromData (Data.comp f.toData g.toData)

/-- The ambient morphism of a filtered identity is the ambient identity. -/
@[simp] theorem id_hom (X : FilteredObject C) : (id X).hom = 𝟙 X.obj := rfl

/-- The ambient morphism of filtered composition is ambient composition. -/
@[simp] theorem comp_hom (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).hom = f.hom ≫ g.hom := rfl

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
