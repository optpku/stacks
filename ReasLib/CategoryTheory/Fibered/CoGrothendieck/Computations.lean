/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Map2

/-!
# Pointwise computations for co-Grothendieck action

Formulas for the vertical `2`-cell induced by a modification, first at the general based
co-Grothendieck layer and then at the pointwise-groupoidal bundled layer.
-/

@[expose] public section

universe w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

/-- The base component of the explicit co-Grothendieck arrow induced by a modification is the
identity. -/
@[simp]
theorem map₂App.base
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    (map₂App Γ a).base = 𝟙 a.base := sorry

/-- The fiber component of the explicit co-Grothendieck arrow induced by a modification is the
modification component followed by the target identity comparison. -/
@[simp]
theorem map₂App.fiber
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    (map₂App Γ a).fiber =
      (Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber ≫
        (G.mapId ⟨Opposite.op a.base⟩).inv.toNatTrans.app
          ((β.app ⟨Opposite.op a.base⟩).toFunctor.obj a.fiber) := sorry

/-- The component of the bundled based co-Grothendieck `2`-cell is the explicit arrow
`map₂App Γ a`. -/
@[simp]
theorem map₂Based.app
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    (map₂Based Γ).toNatTrans.app a = map₂App Γ a := sorry

/-- The base component of the based co-Grothendieck `2`-cell induced by a modification is the
identity. -/
@[simp]
theorem map₂Based.app.base
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    ((map₂Based Γ).toNatTrans.app a).base = 𝟙 a.base := sorry

/-- The fiber component of the based co-Grothendieck `2`-cell induced by a modification is the
modification component followed by the target identity comparison. -/
@[simp]
theorem map₂Based.app.fiber
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    ((map₂Based Γ).toNatTrans.app a).fiber =
      (Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber ≫
        (G.mapId ⟨Opposite.op a.base⟩).inv.toNatTrans.app
          ((β.app ⟨Opposite.op a.base⟩).toFunctor.obj a.fiber) := sorry

/-- The components induced by a modification are natural in co-Grothendieck arrows at the
based-category layer. -/
@[reassoc]
theorem map₂Based.naturality
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β)
    {a b : ∫ᶜ F} (f : a ⟶ b) :
    (mapBased α).toFunctor.map f ≫ (map₂Based Γ).toNatTrans.app b =
      (map₂Based Γ).toNatTrans.app a ≫ (mapBased β).toFunctor.map f := sorry

/-- Every component of the based co-Grothendieck `2`-cell induced by a modification lies over
the identity of its source base object. -/
theorem map₂Based.app.isHomLift
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    Functor.IsHomLift (forget G) (𝟙 ((forget F).obj a))
      ((map₂Based Γ).toNatTrans.app a) := sorry

/-- The component of a map of the based co-Grothendieck hom-category functor is the component
of the canonical vertical `2`-cell. -/
@[simp]
theorem mapBasedHomFunctor.map.app
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    ((mapBasedHomFunctor F G).map Γ).toNatTrans.app a =
      (map₂Based Γ).toNatTrans.app a := sorry

/-- The base component of the co-Grothendieck `2`-cell induced by a modification is the
identity. -/
@[simp]
theorem map₂Over.app.base
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    ((map₂Over Γ).hom.toNatTrans.app a).base = 𝟙 a.base := sorry

/-- The fiber component of the co-Grothendieck `2`-cell induced by a modification is the
modification component followed by the target identity comparison. -/
@[simp]
theorem map₂Over.app.fiber
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    ((map₂Over Γ).hom.toNatTrans.app a).fiber =
      (Γ.as.app ⟨Opposite.op a.base⟩).toNatTrans.app a.fiber ≫
        (G.mapId ⟨Opposite.op a.base⟩).inv.toNatTrans.app
          ((β.app ⟨Opposite.op a.base⟩).toFunctor.obj a.fiber) := sorry

/-- The components induced by a modification are natural in co-Grothendieck arrows. -/
@[reassoc]
theorem map₂Over.naturality
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    {α β : F ⟶ G} (Γ : α ⟶ β)
    {a b : ∫ᶜ F} (f : a ⟶ b) :
    (FiberedCategoryOver.Groupoids.toFunctor (mapOver α)).map f ≫
        (map₂Over Γ).hom.toNatTrans.app b =
      (map₂Over Γ).hom.toNatTrans.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctor (mapOver β)).map f := sorry

/-- Every component of the co-Grothendieck `2`-cell induced by a modification lies over the
identity of its source base object. -/
theorem map₂Over.app.isHomLift
    {F G : LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat.{v₂, w}}
    [∀ U, IsGroupoid (F.obj U)] [∀ U, IsGroupoid (G.obj U)]
    {α β : F ⟶ G} (Γ : α ⟶ β) (a : ∫ᶜ F) :
    Functor.IsHomLift (forget G) (𝟙 ((forget F).obj a))
      ((map₂Over Γ).hom.toNatTrans.app a) := sorry

end CategoryTheory.Pseudofunctor.CoGrothendieck
