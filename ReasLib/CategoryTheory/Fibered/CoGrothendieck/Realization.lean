/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.GroupoidValued
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Map2

/-!
# Strict co-Grothendieck realization

The pseudofunctor from groupoid-valued pseudofunctors to categories fibred in
groupoids over a fixed base.
-/

@[expose] public section

universe w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

section Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The `1`-cell action on the groupoid-valued source bicategory. -/
private def mapOwner
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    toFibered F.toPseudofunctor ⟶ toFibered G.toPseudofunctor :=
  mapOver α.hom

/-- The `2`-cell action on the groupoid-valued source bicategory. -/
private def map₂Owner
    {F G : Pseudofunctor.GroupoidValued 𝒞} {α β : F ⟶ G} (Γ : α ⟶ β) :
    mapOwner α ⟶ mapOwner β :=
  map₂Over Γ.hom

end Implementation

/-- The identity law needed to assemble the co-Grothendieck realization hom functor. -/
private theorem realizationHomFunctor_map_id
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    Implementation.map₂Owner (𝟙 α) = 𝟙 (Implementation.mapOwner α) := sorry

/-- The composition law needed to assemble the co-Grothendieck realization hom functor. -/
private theorem realizationHomFunctor_map_comp
    {F G : Pseudofunctor.GroupoidValued 𝒞}
    {α β γ : F ⟶ G} (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    Implementation.map₂Owner (Γ ≫ Δ) =
      Implementation.map₂Owner Γ ≫ Implementation.map₂Owner Δ := sorry

/-- The functor on a fixed hom-category induced by co-Grothendieck realization.

It exposes the strong-transformation and modification actions before they are packaged into the
global strict pseudofunctor. -/
def realizationHomFunctor (F G : Pseudofunctor.GroupoidValued 𝒞) :
    (F ⟶ G) ⥤
      (toFibered F.toPseudofunctor ⟶ toFibered G.toPseudofunctor) where
  obj α := Implementation.mapOwner α
  map Γ := Implementation.map₂Owner Γ
  map_id α := realizationHomFunctor_map_id α
  map_comp Γ Δ := realizationHomFunctor_map_comp Γ Δ

namespace Implementation

/-- The owner object action preserves identity `1`-morphisms strictly. -/
private theorem mapOwner_id (F : Pseudofunctor.GroupoidValued 𝒞) :
    mapOwner (𝟙 F) = 𝟙 (toFibered F.toPseudofunctor) := sorry

/-- The owner `1`-cell action preserves horizontal composition strictly. -/
private theorem mapOwner_comp
    {F G H : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) (β : G ⟶ H) :
    mapOwner (α ≫ β) = mapOwner α ≫ mapOwner β := sorry

/-- The equality transporting a left-unitor source under the owner action. -/
private theorem mapOwner_id_comp
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    mapOwner (𝟙 F ≫ α) =
      𝟙 (toFibered F.toPseudofunctor) ≫ mapOwner α := sorry

/-- The equality transporting a right-unitor source under the owner action. -/
private theorem mapOwner_comp_id
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    mapOwner (α ≫ 𝟙 G) =
      mapOwner α ≫ 𝟙 (toFibered G.toPseudofunctor) := sorry

/-- The equality transporting the source of an associator under the owner action. -/
private theorem mapOwner_assoc_left
    {F G H I : Pseudofunctor.GroupoidValued 𝒞}
    (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) :
    mapOwner ((α ≫ β) ≫ γ) =
      (mapOwner α ≫ mapOwner β) ≫ mapOwner γ := sorry

/-- The equality transporting the target of an associator under the owner action. -/
private theorem mapOwner_assoc_right
    {F G H I : Pseudofunctor.GroupoidValued 𝒞}
    (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) :
    mapOwner α ≫ (mapOwner β ≫ mapOwner γ) =
      mapOwner (α ≫ (β ≫ γ)) := sorry

/-- Compatibility of the co-Grothendieck `2`-cell action with left whiskering. -/
private theorem map₂Owner_whisker_left
    {F G H : Pseudofunctor.GroupoidValued 𝒞}
    (α : F ⟶ G) {β γ : G ⟶ H} (Γ : β ⟶ γ) :
    map₂Owner (α ◁ Γ) =
      eqToHom (mapOwner_comp α β) ≫
        mapOwner α ◁ map₂Owner Γ ≫
          eqToHom (mapOwner_comp α γ).symm := sorry

/-- Compatibility of the co-Grothendieck `2`-cell action with right whiskering. -/
private theorem map₂Owner_whisker_right
    {F G H : Pseudofunctor.GroupoidValued 𝒞}
    {α β : F ⟶ G} (Γ : α ⟶ β) (γ : G ⟶ H) :
    map₂Owner (Γ ▷ γ) =
      eqToHom (mapOwner_comp α γ) ≫
        map₂Owner Γ ▷ mapOwner γ ≫
          eqToHom (mapOwner_comp β γ).symm := sorry

/-- Left-unitor coherence for the strict co-Grothendieck owner action. -/
private theorem map₂Owner_left_unitor
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    map₂Owner (λ_ α).hom =
      eqToHom (mapOwner_id_comp α) ≫
        (λ_ (mapOwner α)).hom := sorry

/-- Right-unitor coherence for the strict co-Grothendieck owner action. -/
private theorem map₂Owner_right_unitor
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    map₂Owner (ρ_ α).hom =
      eqToHom (mapOwner_comp_id α) ≫
        (ρ_ (mapOwner α)).hom := sorry

/-- Associator coherence for the strict co-Grothendieck owner action. -/
private theorem map₂Owner_associator
    {F G H I : Pseudofunctor.GroupoidValued 𝒞}
    (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) :
    map₂Owner (α_ α β γ).hom =
      eqToHom (mapOwner_assoc_left α β γ) ≫
        (α_ (mapOwner α) (mapOwner β) (mapOwner γ)).hom ≫
          eqToHom (mapOwner_assoc_right α β γ) := sorry

/-- The explicit prelax data of the co-Grothendieck realization. -/
private def realizationPrelax :
    PrelaxFunctor (Pseudofunctor.GroupoidValued 𝒞)
      (FiberedCategoryOver.Groupoids 𝒞) :=
  PrelaxFunctor.mkOfHomFunctors
    (fun F ↦ toFibered F.toPseudofunctor) realizationHomFunctor

/-- The strict-pseudofunctor core of the co-Grothendieck realization. -/
private def realizationCore :
    StrictPseudofunctorCore (Pseudofunctor.GroupoidValued 𝒞)
      (FiberedCategoryOver.Groupoids 𝒞) where
  __ := realizationPrelax
  map_id := mapOwner_id
  map_comp := mapOwner_comp
  map₂_whisker_left := map₂Owner_whisker_left
  map₂_whisker_right := map₂Owner_whisker_right
  map₂_left_unitor := map₂Owner_left_unitor
  map₂_right_unitor := map₂Owner_right_unitor
  map₂_associator := map₂Owner_associator

end Implementation

variable (𝒞) in
/-- The strict co-Grothendieck realization of groupoid-valued pseudofunctors as categories fibred
in groupoids over `𝒞`. Its unity and composition comparisons are equality isomorphisms induced by
the strict `CoGrothendieck.map_id_eq` and `CoGrothendieck.map_comp_eq` formulas. -/
def realization :
    StrictPseudofunctor (Pseudofunctor.GroupoidValued 𝒞)
      (FiberedCategoryOver.Groupoids 𝒞) :=
  StrictPseudofunctor.mk' Implementation.realizationCore

end Implementation

/-- The object action of the co-Grothendieck realization is the canonical bundled category fibred
in groupoids associated to the underlying groupoid-valued pseudofunctor. -/
@[simp]
theorem realization.obj (F : Pseudofunctor.GroupoidValued 𝒞) :
    (realization 𝒞).obj F = toFibered F.toPseudofunctor := sorry

/-- The `1`-cell action of the co-Grothendieck realization is the canonical map over the fixed
base induced by the underlying strong transformation. -/
@[simp]
theorem realization.map
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    (realization 𝒞).map α = mapOver α.hom := sorry

/-- The `2`-cell action of the co-Grothendieck realization is the canonical vertical map over the
fixed base induced by the underlying modification. -/
@[simp]
theorem realization.map₂
    {F G : Pseudofunctor.GroupoidValued 𝒞} {α β : F ⟶ G} (Γ : α ⟶ β) :
    (realization 𝒞).map₂ Γ = map₂Over Γ.hom := sorry

/-- The local functor of co-Grothendieck realization is the explicit hom-category action. -/
@[simp]
theorem realization.mapFunctor
    (F G : Pseudofunctor.GroupoidValued 𝒞) :
    (realization 𝒞).mapFunctor F G = realizationHomFunctor F G := sorry

/-- The hom-category action of co-Grothendieck realization sends a strong transformation to its
canonical map over the fixed base. -/
@[simp]
theorem realizationHomFunctor.obj
    {F G : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) :
    (realizationHomFunctor F G).obj α = mapOver α.hom := sorry

/-- The hom-category action of co-Grothendieck realization sends a modification to its canonical
vertical map over the fixed base. -/
@[simp]
theorem realizationHomFunctor.map
    {F G : Pseudofunctor.GroupoidValued 𝒞}
    {α β : F ⟶ G} (Γ : α ⟶ β) :
    (realizationHomFunctor F G).map Γ = map₂Over Γ.hom := sorry

/-- Co-Grothendieck realization preserves identity `1`-morphisms on the nose. -/
@[simp]
theorem realization.map.id (F : Pseudofunctor.GroupoidValued 𝒞) :
    (realization 𝒞).map (𝟙 F) = 𝟙 ((realization 𝒞).obj F) := sorry

/-- Co-Grothendieck realization preserves horizontal composition on the nose. -/
@[simp]
theorem realization.map.comp
    {F G H : Pseudofunctor.GroupoidValued 𝒞} (α : F ⟶ G) (β : G ⟶ H) :
    (realization 𝒞).map (α ≫ β) =
      (realization 𝒞).map α ≫ (realization 𝒞).map β := sorry

end CategoryTheory.Pseudofunctor.CoGrothendieck
