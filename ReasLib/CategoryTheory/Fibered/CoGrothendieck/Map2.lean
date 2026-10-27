/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Basic

/-!
# Modification action for co-Grothendieck maps

The explicit vertical `2`-cell induced by a modification of pseudofunctors.
-/

@[expose] public section

universe w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

/-- A modification between strong transformations acts on a co-Grothendieck object within its
fixed base fiber. The first factor is the modification component; the second is the canonical
`G.mapId` comparison required by the co-Grothendieck representation of an arrow over an identity.
No witness is chosen. `Opposite.op` is qualified to disambiguate it from `Pseudofunctor.op`. -/
def map₂App
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G}
    (Γ : α ⟶ β)
    (a : ∫ᶜ F) :
    (map α).obj a ⟶ (map β).obj a where
  base := 𝟙 a.base
  fiber :=
    (Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber ≫
      (G.mapId ⟨Opposite.op a.base⟩).inv.toNatTrans.app
        ((β.app ⟨Opposite.op a.base⟩).toFunctor.obj a.fiber)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The components `map₂App Γ` are natural in co-Grothendieck objects.

Proof strategy: extensionality first makes the base equation trivial. In the fiber, expand
`CoGrothendieck.map`, use the modification naturality equation for `Γ`, then the naturality of
`G.mapId` and the strong-naturality comparisons of `α` and `β`. -/
@[reassoc]
theorem map₂App.naturality
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β)
    {a b : ∫ᶜ F} (f : a ⟶ b) :
    (map α).map f ≫ map₂App Γ b =
      map₂App Γ a ≫ (map β).map f := by
  have hΓ := congrArg (fun η ↦ η.toNatTrans.app b.fiber)
    (Γ.as.naturality f.base.op.toLoc)
  dsimp at hΓ
  apply Hom.ext _ _ (by
    change f.base ≫ 𝟙 b.base = 𝟙 a.base ≫ f.base
    rw [Category.comp_id, Category.id_comp])
  dsimp only [map, map₂App, categoryStruct]
  simp only [categoryStruct_comp_fiber]
  simp only [op_id, Quiver.Hom.id_toLoc,
    G.mapComp_id_left_inv_app, G.mapComp_id_right_inv_app,
    Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso,
    eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app,
    Category.assoc, Functor.map_comp]
  simp only [← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Cat.Hom.id_toFunctor, Functor.id_obj, eqToHom_trans, eqToHom_refl,
    Category.comp_id, Category.id_comp]
  rw [← (Cat.Hom.toNatIso (G.mapId ⟨Opposite.op a.base⟩)).inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [Cat.Hom.id_map, Category.assoc]
  simp only [← Cat.Hom.toNatIso_hom] at hΓ
  rw [← reassoc_of% hΓ,
    (Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.naturality_assoc f.fiber]

/-- Each explicit `map₂App Γ a` lies over the identity of the unchanged base. -/
theorem map₂App.isHomLift
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β)
    (a : ∫ᶜ F) :
    Functor.IsHomLift (forget G) (𝟙 ((forget F).obj a))
      (map₂App Γ a) :=
  Functor.IsHomLift.map (map₂App Γ a)

section Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- A modification induces the corresponding natural transformation between co-Grothendieck
map functors. Its component data are explicit in `map₂App`; only their named naturality theorem
is used to assemble the transformation. -/
private def map₂NatTrans
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}} {α β : F ⟶ G}
    (Γ : α ⟶ β) : map α ⟶ map β where
  app a := map₂App Γ a
  naturality {_ _} f := map₂App.naturality Γ f

/-- The natural transformation induced by a modification, bundled as a vertical `2`-cell between
the corresponding based co-Grothendieck maps. -/
private def map₂Based
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}} {α β : F ⟶ G}
    (Γ : α ⟶ β) : mapBased α ⟶ mapBased β where
  toNatTrans := map₂NatTrans Γ
  isHomLift' a := map₂App.isHomLift Γ a

end Implementation

/-- A modification of arbitrary `Cat`-valued pseudofunctors induces the canonical vertical
`2`-cell between their based co-Grothendieck maps. This is the choice-free ambient action; the
groupoid-fibred specialization is `map₂Over`. -/
def map₂Based
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}} {α β : F ⟶ G}
    (Γ : α ⟶ β) : mapBased α ⟶ mapBased β :=
  Implementation.map₂Based Γ

private theorem basedFunctor_ext
    {X Y : BasedCategory.{v₂, w} 𝒞} {A B : X ⥤ᵇ Y}
    (h : A.toFunctor = B.toFunctor) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- The based co-Grothendieck action preserves identity strong transformations strictly. -/
@[simp]
theorem mapBased.id
    (F : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}) :
    mapBased (𝟙 F) = 𝟙 (BasedCategory.ofFunctor (forget F)) := by
  apply basedFunctor_ext
  exact map_id_eq F

/-- The based co-Grothendieck action preserves horizontal composition strictly. -/
@[simp]
theorem mapBased.comp
    {F G H : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    (α : F ⟶ G) (β : G ⟶ H) :
    mapBased (α ≫ β) = (mapBased α).comp (mapBased β) := by
  apply basedFunctor_ext
  exact map_comp_eq α β

/-- The based co-Grothendieck action preserves identity modifications. -/
@[simp]
theorem map₂Based.id
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    (α : F ⟶ G) :
    map₂Based (𝟙 α) = 𝟙 (mapBased α) := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  change (ι G a.base).map (𝟙 ((α.app ⟨Opposite.op a.base⟩).toFunctor.obj a.fiber)) =
    𝟙 ((map α).obj a)
  exact (ι G a.base).map_id _

/-- The based co-Grothendieck action preserves vertical composition of modifications. -/
@[simp]
theorem map₂Based.comp
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β γ : F ⟶ G} (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    map₂Based (Γ ≫ Δ) = map₂Based Γ ≫ map₂Based Δ := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  change (ι G a.base).map
      ((Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber ≫
        (Δ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber) =
    (ι G a.base).map ((Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber) ≫
      (ι G a.base).map ((Δ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber)
  exact (ι G a.base).map_comp _ _

/-- The functor on a fixed hom-category induced by the based co-Grothendieck action.

It packages the strong-transformation and modification actions before any pointwise groupoid
condition is imposed. -/
def mapBasedHomFunctor
    (F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}) :
    (F ⟶ G) ⥤
      (BasedCategory.ofFunctor (forget F) ⟶ BasedCategory.ofFunctor (forget G)) where
  obj α := mapBased α
  map Γ := map₂Based Γ
  map_id α := map₂Based.id α
  map_comp Γ Δ := map₂Based.comp Γ Δ

/-- The object action of the based co-Grothendieck hom-category functor is the canonical based
map induced by a strong transformation. -/
@[simp]
theorem mapBasedHomFunctor.obj
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}} (α : F ⟶ G) :
    (mapBasedHomFunctor F G).obj α = mapBased α := rfl

/-- The morphism action of the based co-Grothendieck hom-category functor is the canonical
vertical `2`-cell induced by a modification. -/
@[simp]
theorem mapBasedHomFunctor.map
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) :
    (mapBasedHomFunctor F G).map Γ = map₂Based Γ := rfl

/-- A modification of pointwise groupoidal pseudofunctors induces the canonical owner-level
`2`-cell between their co-Grothendieck `1`-morphisms. -/
def map₂Over
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    {α β : F ⟶ G} (Γ : α ⟶ β) :
    mapOver α ⟶ mapOver β :=
  Bicategory.InducedBicategory.mkHom₂ (map₂Based Γ)

/-- The co-Grothendieck action on modifications preserves identity modifications. -/
@[simp]
theorem map₂Over.id
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    (α : F ⟶ G) :
    map₂Over (𝟙 α) = 𝟙 (mapOver α) := by
  apply Bicategory.InducedBicategory.hom₂_ext
  exact map₂Based.id α

/-- The co-Grothendieck action on modifications preserves vertical composition. -/
@[simp]
theorem map₂Over.comp
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    {α β γ : F ⟶ G} (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    map₂Over (Γ ≫ Δ) = map₂Over Γ ≫ map₂Over Δ := by
  apply Bicategory.InducedBicategory.hom₂_ext
  exact map₂Based.comp Γ Δ

end Implementation

end CategoryTheory.Pseudofunctor.CoGrothendieck
