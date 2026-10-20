/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport

/-!
# Functors of displayed categories

This file owns maps of displayed categories over a functor of base categories.  The induced
functor on total categories is kept separate from the displayed data, so downstream constructions
can use either the dependent map or its ordinary total-category realization.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u' v'' u'' v''' u'''

set_option linter.checkUnivs false in
/-- A functor between displayed categories lying over a functor of base categories. -/
@[stacks 015N "functor between displayed categories"]
structure DisplayedFunctor
    {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (D : DisplayedCategory C) (E : DisplayedCategory C') (F : C ⥤ C') where
  /-- The map on displayed objects over each base object. -/
  obj : {X : C} → D.obj X → E.obj (F.obj X)
  /-- The map on displayed morphisms over a base morphism. -/
  map : {X Y : C} → {f : X ⟶ Y} → {x : D.obj X} → {y : D.obj Y} →
    D.Hom f x y → E.Hom (F.map f) (obj x) (obj y)
  /-- Compatibility with displayed identities, transported along the base functor law. -/
  map_id : ∀ {X : C} (x : D.obj X),
    DisplayedCategory.Hom.cast E (F.map_id X) (map (D.id x)) = E.id (obj x)
  /-- Compatibility with displayed composition, transported along the base functor law. -/
  map_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : D.obj X} {y : D.obj Y} {z : D.obj Z}
    (φ : D.Hom f x y) (ψ : D.Hom g y z),
    DisplayedCategory.Hom.cast E (F.map_comp f g) (map (D.comp φ ψ)) =
      E.comp (map φ) (map ψ)

namespace DisplayedFunctor

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'} {F : C ⥤ C'}

/-- Reindex displayed-functor data along an equality of the underlying base functors.

This is the canonical dependent equality operation for clients which obtain two definitionally
different presentations of the same base functor.  It changes no displayed data beyond the
necessary `Eq.rec` transport. -/
def reindex {F G : C ⥤ C'} (h : F = G)
    (Φ : DisplayedFunctor D E F) : DisplayedFunctor D E G := h ▸ Φ

/-- Reindexing a displayed functor along reflexivity leaves it unchanged. -/
@[simp]
theorem reindex_rfl {F : C ⥤ C'} (Φ : DisplayedFunctor D E F) :
    reindex rfl Φ = Φ := sorry

/-- Successive displayed-functor reindexings combine by equality transitivity. -/
@[simp]
theorem reindex_trans {F G H : C ⥤ C'} (h : F = G) (k : G = H)
    (Φ : DisplayedFunctor D E F) :
    reindex k (reindex h Φ) = reindex (h.trans k) Φ := sorry

/-- The displayed-object map of a reindexed displayed functor is canonical object transport. -/
@[simp]
theorem reindex_obj {F G : C ⥤ C'} (h : F = G)
    (Φ : DisplayedFunctor D E F) {X : C} (x : D.obj X) :
    (reindex h Φ).obj x =
      DisplayedCategory.Obj.cast E
        (congrArg (fun K : C ⥤ C' => K.obj X) h) (Φ.obj x) := sorry

/-- The displayed-morphism map of a reindexed displayed functor is the canonical dependent
transport of the original map. -/
@[simp]
theorem reindex_map {F G : C ⥤ C'} (h : F = G)
    (Φ : DisplayedFunctor D E F) {X Y : C} {f : X ⟶ Y}
    {x : D.obj X} {y : D.obj Y} (φ : D.Hom f x y) :
    HEq ((reindex h Φ).map φ) (Φ.map φ) := sorry

/-- Displayed functors over a fixed base functor are determined by their object and morphism
maps.  Heterogeneous equality is the natural comparison for morphism maps whose endpoints are
only propositionally equal. -/
@[ext]
theorem ext {Φ Ψ : DisplayedFunctor D E F}
    (h_obj : ∀ {X : C} (x : D.obj X), Φ.obj x = Ψ.obj x)
    (h_map : ∀ {X Y : C} {f : X ⟶ Y} {x : D.obj X} {y : D.obj Y}
      (φ : D.Hom f x y), HEq (Φ.map φ) (Ψ.map φ)) :
    Φ = Ψ := sorry

/-- The identity displayed functor over the identity base functor. -/
def id (D : DisplayedCategory C) : DisplayedFunctor D D (𝟭 C) where
  obj x := x
  map φ := φ
  map_id := sorry
  map_comp := sorry

/-- Composition of displayed functors over composition of base functors. -/
def comp {C'' : Type u''} [Category.{v''} C'']
    {E' : DisplayedCategory C''} {G : C' ⥤ C''}
    (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor E E' G) :
    DisplayedFunctor D E' (F ⋙ G) where
  obj x := Ψ.obj (Φ.obj x)
  map φ := Ψ.map (Φ.map φ)
  map_id := sorry
  map_comp := sorry

/-- The total-category functor induced by a displayed functor. -/
@[stacks 015N "total functor induced by a displayed functor"]
def total (Φ : DisplayedFunctor D E F) :
    DisplayedCategory.Total D ⥤ DisplayedCategory.Total E where
  obj X := ⟨F.obj X.base, Φ.obj X.obj⟩
  map f := ⟨F.map f.base, Φ.map f.displayed⟩
  map_id := sorry
  map_comp := sorry

/-- The base object of the total image is computed by the base functor. -/
@[simp]
theorem total_obj_base (Φ : DisplayedFunctor D E F)
    (X : DisplayedCategory.Total D) :
    ((total Φ).obj X).base = F.obj X.base := sorry

/-- The displayed object of the total image is computed by the displayed object map. -/
@[simp]
theorem total_obj_obj (Φ : DisplayedFunctor D E F)
    (X : DisplayedCategory.Total D) :
    ((total Φ).obj X).obj = Φ.obj X.obj := sorry

/-- The base morphism of a total image is computed by the base functor. -/
@[simp]
theorem total_map_base (Φ : DisplayedFunctor D E F)
    {X Y : DisplayedCategory.Total D} (f : X ⟶ Y) :
    ((total Φ).map f).base = F.map f.base := sorry

/-- The displayed morphism of a total image is computed by the displayed map. -/
@[simp]
theorem total_map_displayed (Φ : DisplayedFunctor D E F)
    {X Y : DisplayedCategory.Total D} (f : X ⟶ Y) :
    ((total Φ).map f).displayed = Φ.map f.displayed := sorry

/-- Totalization sends base-arrow reindexing to reindexing along the image base-arrow equality. -/
@[simp, stacks 015N "totalized displayed-functor transport"]
theorem total_map_reindex (Φ : DisplayedFunctor D E F)
    {X Y : DisplayedCategory.Total D} {f : X ⟶ Y}
    {g : X.base ⟶ Y.base} (h : f.base = g) :
    (total Φ).map
        (DisplayedCategory.Total.Hom.reindex (D := D) (f := f) h) =
      DisplayedCategory.Total.Hom.reindex
        (D := E) (f := (total Φ).map f)
        (congrArg (fun k : X.base ⟶ Y.base => F.map k) h) := sorry

/-- Totalization forgets the proof-level presentation of a reindexed base functor. -/
@[simp]
theorem total_reindex {F G : C ⥤ C'} (h : F = G)
    (Φ : DisplayedFunctor D E F) :
    total (reindex h Φ) = total Φ := sorry

/-- A totalized displayed-functor map is canonically a hom-lift of its base image.

This instance lets based and fibered downstream constructions use `total Φ` without rebuilding a
projection equality for every morphism. -/
@[stacks 015N "hom-lift for a totalized displayed-functor map"]
instance total_map_isHomLift (Φ : DisplayedFunctor D E F)
    {X Y : DisplayedCategory.Total D} (f : X ⟶ Y) :
    (DisplayedCategory.Total.forget E).IsHomLift
      (F.map f.base) ((total Φ).map f) := sorry

/-- The total functor commutes with the projections to the base categories. -/
theorem total_forget (Φ : DisplayedFunctor D E F) :
    total Φ ⋙ DisplayedCategory.Total.forget E =
      DisplayedCategory.Total.forget D ⋙ F := sorry

/-- The same-base projection formula for a displayed functor over an identity base functor. -/
theorem total_forget_id {E : DisplayedCategory C}
    (Φ : DisplayedFunctor D E (𝟭 C)) :
    total Φ ⋙ DisplayedCategory.Total.forget E = DisplayedCategory.Total.forget D := sorry

/-- Totalization preserves identity displayed functors. -/
@[simp]
theorem total_id (D : DisplayedCategory C) :
    total (id D) = 𝟭 (DisplayedCategory.Total D) := sorry

/-- Totalization preserves composition of displayed functors. -/
@[simp]
theorem total_comp {C'' : Type u''} [Category.{v''} C'']
    {E' : DisplayedCategory C''} {G : C' ⥤ C''}
    (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor E E' G) :
    total (comp Φ Ψ) = total Φ ⋙ total Ψ := sorry

/- The ordinary functor category identifies these composites only propositionally.  Keeping the
unit laws in reindexed form gives dependent clients the same rewrite surface as ordinary
category composition. -/

/-- The identity displayed functor is a left unit up to the canonical base-functor transport. -/
@[simp]
theorem id_comp {F : C ⥤ C'} (Φ : DisplayedFunctor D E F) :
    reindex (Functor.id_comp F) (comp (id D) Φ) = Φ := sorry

/-- The identity displayed functor is a right unit up to the canonical base-functor transport. -/
@[simp]
theorem comp_id {F : C ⥤ C'} (Φ : DisplayedFunctor D E F) :
    reindex (Functor.comp_id F) (comp Φ (id E)) = Φ := sorry

/-- Displayed-functor composition is associative up to the canonical base-functor transport. -/
@[simp]
theorem assoc {C'' : Type u''} [Category.{v''} C'']
    {C''' : Type u'''} [Category.{v'''} C''']
    {E' : DisplayedCategory C''} {E'' : DisplayedCategory C'''}
    {F : C ⥤ C'} {G : C' ⥤ C''} {H : C'' ⥤ C'''}
    (Φ : DisplayedFunctor D E F) (Ψ : DisplayedFunctor E E' G)
    (Ω : DisplayedFunctor E' E'' H) :
    reindex (Functor.assoc F G H) (comp (comp Φ Ψ) Ω) =
      comp Φ (comp Ψ Ω) := sorry

end DisplayedFunctor

end CategoryTheory
