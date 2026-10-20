/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Basic

/-!
# Indexed-functor composition and modifications
-/

@[expose] public section

universe uC vC uD vD uE vE uI vI uJ vJ uF vF uG vG uH vH uM vM uN vN

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace IndexedFunctor

variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- Naturality data for the composite of two indexed functors.  The associators make this
definition independent of the parenthesization chosen for ordinary functor composition. -/
noncomputable def compNaturality
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    {U V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor ⋙
        (H.app V ⋙ K.app (u.obj V)) ≅
      (H.app U ⋙ K.app (u.obj U)) ⋙
        (L.map ((u ⋙ v).map f).op.toLoc).toFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (H.naturality f) (K.app (u.obj V)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (H.app U) (K.naturality (u.map f)) ≪≫
    (Functor.associator _ _ _).symm

/-- Identity coherence for the composite of two indexed functors. -/
theorem comp_naturality_id
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    (U : C) (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (H.app U ⋙ K.app (u.obj U)).map
          ((F.mapIdOp U).inv.toNatTrans.app x) ≫
        (compNaturality H K (𝟙 U)).hom.app x =
      (L.mapIdOp' ((u ⋙ v).obj U) ((u ⋙ v).map (𝟙 U))
        ((u ⋙ v).map_id U)).inv.toNatTrans.app
          ((H.app U ⋙ K.app (u.obj U)).obj x) := sorry

/-- Composition coherence for the composite of two indexed functors. -/
theorem comp_naturality_comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (compNaturality H K (g ≫ f)).hom.app x ≫
        (L.mapCompOp' ((u ⋙ v).map f) ((u ⋙ v).map g)
          ((u ⋙ v).map (g ≫ f))
          ((u ⋙ v).map_comp g f).symm).hom.toNatTrans.app
            ((H.app U ⋙ K.app (u.obj U)).obj x) =
      (H.app W ⋙ K.app (u.obj W)).map
          ((F.mapCompOp f g).hom.toNatTrans.app x) ≫
        (compNaturality H K g).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (L.map ((u ⋙ v).map g).op.toLoc).toFunctor.map
          ((compNaturality H K f).hom.app x) := sorry

/-- Composition of universe-polymorphic indexed functors. -/
noncomputable def comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L) :
    IndexedFunctor (u ⋙ v) F L where
  app U := H.app U ⋙ K.app (u.obj U)
  naturality f := compNaturality H K f
  naturality_id U x := comp_naturality_id H K U x
  naturality_comp f g x := comp_naturality_comp H K f g x

/-- Components of a composite indexed functor are composites of the component functors. -/
@[simp]
theorem comp_app
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L) (U : C) :
    (H.comp K).app U = H.app U ⋙ K.app (u.obj U) := sorry

/-- Naturality of a composite indexed functor is the canonical composite comparison. -/
@[simp]
theorem comp_naturality
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    {U V : C} (f : V ⟶ U) :
    (H.comp K).naturality f = compNaturality H K f := sorry

/-- Transport of restricted morphisms through a composite indexed functor is successive
transport through its two factors. -/
theorem comp_mapHom
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    (H.comp K).mapHom f₁ f₂ φ =
      K.mapHom (u.map f₁) (u.map f₂) (H.mapHom f₁ f₂ φ) := sorry

/-- A modification between two indexed functors with the same base, source, and target consists
of component natural transformations compatible with the indexed naturality isomorphisms. -/
@[ext]
structure Hom (H K : IndexedFunctor u F G) where
  /-- The natural transformation between the component functors over a base object. -/
  app (U : C) : H.app U ⟶ K.app U
  /-- Compatibility of the component transformations with reindexing. -/
  naturality {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (H.naturality f).hom.app x ≫
        (G.map (u.map f).op.toLoc).toFunctor.map ((app U).app x) =
      (app V).app ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (K.naturality f).hom.app x

/-- Naturality of the identity modification of an indexed functor. -/
theorem homId_naturality
    (H : IndexedFunctor u F G)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (H.naturality f).hom.app x ≫
        (G.map (u.map f).op.toLoc).toFunctor.map
          ((NatTrans.id (H.app U)).app x) =
      (NatTrans.id (H.app V)).app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (H.naturality f).hom.app x := sorry

/-- The identity modification of an indexed functor. -/
def homId (H : IndexedFunctor u F G) : Hom H H where
  app U := NatTrans.id (H.app U)
  naturality f x := homId_naturality H f x

/-- Naturality of the vertical composite of two indexed-functor modifications. -/
theorem homComp_naturality
    {H K L : IndexedFunctor u F G}
    (α : Hom H K) (β : Hom K L)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (H.naturality f).hom.app x ≫
        (G.map (u.map f).op.toLoc).toFunctor.map
          ((α.app U ≫ β.app U).app x) =
      (α.app V ≫ β.app V).app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (L.naturality f).hom.app x := sorry

/-- Vertical composition of indexed-functor modifications. -/
def homComp
    {H K L : IndexedFunctor u F G}
    (α : Hom H K) (β : Hom K L) :
    Hom H L where
  app U := α.app U ≫ β.app U
  naturality f x := homComp_naturality α β f x

/-- Left identity law for indexed-functor modifications. -/
theorem hom_id_comp
    {H K : IndexedFunctor u F G} (α : Hom H K) :
    homComp (homId H) α = α := sorry

/-- Right identity law for indexed-functor modifications. -/
theorem hom_comp_id
    {H K : IndexedFunctor u F G} (α : Hom H K) :
    homComp α (homId K) = α := sorry

/-- Associativity of vertical composition of indexed-functor modifications. -/
theorem hom_assoc
    {H K L M : IndexedFunctor u F G}
    (α : Hom H K) (β : Hom K L) (γ : Hom L M) :
    homComp (homComp α β) γ =
      homComp α (homComp β γ) := sorry

/-- Indexed functors with fixed base, source, and target form a category under modifications. -/
instance : Category (IndexedFunctor u F G) where
  Hom := Hom
  id := homId
  comp := homComp
  id_comp := hom_id_comp
  comp_id := hom_comp_id
  assoc := hom_assoc

/-- Components of the identity indexed-functor modification are identity natural
transformations. -/
@[simp]
theorem hom_id_app
    (H : IndexedFunctor u F G) (U : C) :
    ((𝟙 H : H ⟶ H).app U) = NatTrans.id (H.app U) := sorry

/-- Components of a composite indexed-functor modification are composites of component natural
transformations. -/
@[simp]
theorem hom_comp_app
    {H K L : IndexedFunctor u F G}
    (α : H ⟶ K) (β : K ⟶ L) (U : C) :
    (α ≫ β).app U = α.app U ≫ β.app U := sorry


end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
