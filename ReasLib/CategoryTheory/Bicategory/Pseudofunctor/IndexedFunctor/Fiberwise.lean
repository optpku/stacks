/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition.Basic

/-!
# Fiberwise properties of indexed functors
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

/-- An indexed functor is fiberwise fully faithful when every component functor is full and
faithful.  This is the minimal property needed to identify hom-sets after reindexing; essential
surjectivity is deliberately not part of this layer. -/
class FiberwiseFullyFaithful (H : IndexedFunctor u F G) : Prop where
  /-- Every fiber component is full. -/
  full (U : C) : (H.app U).Full
  /-- Every fiber component is faithful. -/
  faithful (U : C) : (H.app U).Faithful

attribute [instance] FiberwiseFullyFaithful.full FiberwiseFullyFaithful.faithful

/-- Fiberwise full-faithfulness can be supplied as ordinary fully-faithful structures on all
components.  This constructor is useful when a previous API packages full faithfulness as
`Nonempty Functor.FullyFaithful` rather than as two typeclass assumptions. -/
theorem FiberwiseFullyFaithful.ofFullyFaithful
    (H : IndexedFunctor u F G)
    (h : ∀ U : C, Nonempty (H.app U).FullyFaithful) :
    H.FiberwiseFullyFaithful := sorry

/-- An indexed functor is a fiberwise equivalence when every component functor is an
equivalence.  This property does not impose a same-universe presentation of all fibers. -/
class FiberwiseEquivalence (H : IndexedFunctor u F G) : Prop where
  /-- Every fiber component is an equivalence of categories. -/
  app_isEquivalence (U : C) : (H.app U).IsEquivalence

attribute [instance] FiberwiseEquivalence.app_isEquivalence

/-- Fiberwise equivalence can be supplied directly as equivalence instances for all component
functors. -/
theorem FiberwiseEquivalence.ofIsEquivalence
    (H : IndexedFunctor u F G)
    (h : ∀ U : C, (H.app U).IsEquivalence) :
    H.FiberwiseEquivalence := sorry

/-- The identity indexed functor is an equivalence on every fiber. -/
instance FiberwiseEquivalence.id
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}) :
    (id F).FiberwiseEquivalence := sorry

/-- Every fiberwise equivalence is fiberwise fully faithful. -/
instance FiberwiseEquivalence.fullyFaithful
    (H : IndexedFunctor u F G) [H.FiberwiseEquivalence] :
    H.FiberwiseFullyFaithful := sorry

/-- For a fiberwise-fully-faithful indexed functor, transport of a morphism between restricted
objects is an equivalence of hom-sets.  This packages the component hom equivalence together
with the two naturality isomorphisms, so applications need not reconstruct that conjugation. -/
noncomputable def mapHomEquiv (H : IndexedFunctor u F G)
    [H.FiberwiseFullyFaithful]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))} :
    ((F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) ≃
      ((G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x) ⟶
        (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj y)) :=
  (Functor.FullyFaithful.ofFullyFaithful (H.app V)).homEquiv.trans
    (Iso.homCongr ((H.naturality f₁).app x) ((H.naturality f₂).app y))

/-- The forward map of `mapHomEquiv` is `mapHom`. -/
@[simp]
theorem mapHomEquiv_apply (H : IndexedFunctor u F G)
    [H.FiberwiseFullyFaithful]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    H.mapHomEquiv f₁ f₂ φ = H.mapHom f₁ f₂ φ := sorry

/-- Applying the inverse hom transport after `mapHom` recovers the source morphism. -/
@[simp]
theorem mapHomEquiv_symm_apply_mapHom (H : IndexedFunctor u F G)
    [H.FiberwiseFullyFaithful]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    (H.mapHomEquiv f₁ f₂).symm (H.mapHom f₁ f₂ φ) = φ := sorry

/-- Mapping the inverse hom transport recovers the target morphism. -/
@[simp]
theorem mapHom_mapHomEquiv_symm_apply (H : IndexedFunctor u F G)
    [H.FiberwiseFullyFaithful]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (ψ :
      (G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x) ⟶
        (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj y)) :
    H.mapHom f₁ f₂ ((H.mapHomEquiv f₁ f₂).symm ψ) = ψ := sorry

/-- Inverse restricted-hom transport preserves identity morphisms. -/
@[simp]
theorem mapHomEquiv_symm_apply_id (H : IndexedFunctor u F G)
    [H.FiberwiseFullyFaithful]
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (H.mapHomEquiv f f).symm
        (𝟙 ((G.map (u.map f).op.toLoc).toFunctor.obj
          ((H.app U).obj x))) =
      𝟙 ((F.map f.op.toLoc).toFunctor.obj x) := sorry

/-- Inverse restricted-hom transport preserves composition.  This is the computation rule
needed when descent data or other structured families are reconstructed through a fiberwise
fully-faithful indexed functor. -/
theorem mapHomEquiv_symm_apply_comp (H : IndexedFunctor u F G)
    [H.FiberwiseFullyFaithful]
    {U₁ U₂ U₃ V : C}
    (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (f₃ : V ⟶ U₃)
    {x₁ : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {x₂ : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    {x₃ : F.obj (LocallyDiscrete.mk (Opposite.op U₃))}
    (φ :
      (G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x₁) ⟶
        (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj x₂))
    (ψ :
      (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj x₂) ⟶
        (G.map (u.map f₃).op.toLoc).toFunctor.obj ((H.app U₃).obj x₃)) :
    (H.mapHomEquiv f₁ f₃).symm (φ ≫ ψ) =
      (H.mapHomEquiv f₁ f₂).symm φ ≫
        (H.mapHomEquiv f₂ f₃).symm ψ := sorry

/-- A composite of fiberwise-fully-faithful indexed functors is again fiberwise fully
faithful. -/
instance FiberwiseFullyFaithful.comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    [H.FiberwiseFullyFaithful] [K.FiberwiseFullyFaithful] :
    (H.comp K).FiberwiseFullyFaithful := sorry

/-- A composite of fiberwise-equivalence indexed functors is again a fiberwise equivalence. -/
instance FiberwiseEquivalence.comp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    [H.FiberwiseEquivalence] [K.FiberwiseEquivalence] :
    (H.comp K).FiberwiseEquivalence := sorry

/-- Inverse restricted-hom transport through a composite indexed functor is successive inverse
transport through its second and first factors. -/
theorem comp_mapHomEquiv_symm_apply
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    [H.FiberwiseFullyFaithful] [K.FiberwiseFullyFaithful]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (ψ :
      (L.map ((u ⋙ v).map f₁).op.toLoc).toFunctor.obj
          (((H.comp K).app U₁).obj x) ⟶
        (L.map ((u ⋙ v).map f₂).op.toLoc).toFunctor.obj
          (((H.comp K).app U₂).obj y)) :
    ((H.comp K).mapHomEquiv f₁ f₂).symm ψ =
      (H.mapHomEquiv f₁ f₂).symm
        ((K.mapHomEquiv (u.map f₁) (u.map f₂)).symm ψ) := sorry

end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
