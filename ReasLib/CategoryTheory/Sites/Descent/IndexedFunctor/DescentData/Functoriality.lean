/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition.Basic
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Basic

import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of descent-data transport

This leaf records the action of identity-base indexed functors and their modifications on descent
data.  It packages that action as a functor from the category of indexed functors to a functor
category.
-/

@[expose] public section

universe t uC vC uF vF uG vG uL vL

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The identity indexed functor acts as the identity functor on descent data. -/
@[simp, stacks 026E "indexed-functor descent transport identity"]
theorem mapDescentData.id
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}) :
    (id F).mapDescentData f = 𝟭 (F.DescentData f) := sorry

/-- Transporting descent data through a composite indexed functor is successive transport
through its two factors. -/
@[simp, stacks 026E "indexed-functor descent transport composition"]
theorem mapDescentData.comp
    {L : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vL, uL}}
    (H : IndexedFunctor (𝟭 C) F G)
    (K : IndexedFunctor (𝟭 C) G L) :
    (H.comp K).mapDescentData f =
      H.mapDescentData f ⋙ K.mapDescentData f := sorry

/-- Component transformations of an indexed-functor modification respect the overlap maps of a
transported descent datum. -/
@[stacks 026E "indexed-functor modification descent compatibility"]
theorem mapDescentData.NatTrans.App.comm
    {H K : IndexedFunctor (𝟭 C) F G}
    (α : H ⟶ K) (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.map
          ((α.app (X i₁)).app (D.obj i₁)) ≫
        ((K.mapDescentData f).obj D).hom
          q f₁ f₂ hf₁ hf₂ =
      ((H.mapDescentData f).obj D).hom
          q f₁ f₂ hf₁ hf₂ ≫
        (G.map f₂.op.toLoc).toFunctor.map
          ((α.app (X i₂)).app (D.obj i₂)) := sorry

/-- The component at a descent datum of the natural transformation induced by an
indexed-functor modification. -/
@[stacks 026E "indexed-functor modification descent component"]
def mapDescentData.NatTrans.app
    {H K : IndexedFunctor (𝟭 C) F G}
    (α : H ⟶ K) (D : F.DescentData f) :
    (H.mapDescentData f).obj D ⟶
      (K.mapDescentData f).obj D where
  hom i := (α.app (X i)).app (D.obj i)
  comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
    mapDescentData.NatTrans.App.comm f α D q f₁ f₂ hf₁ hf₂

/-- Components induced by an indexed-functor modification are natural in the source descent
datum. -/
@[stacks 026E "indexed-functor modification descent naturality"]
theorem mapDescentData.NatTrans.naturality
    {H K : IndexedFunctor (𝟭 C) F G}
    (α : H ⟶ K) {D₁ D₂ : F.DescentData f}
    (φ : D₁ ⟶ D₂) :
    (H.mapDescentData f).map φ ≫
        mapDescentData.NatTrans.app f α D₂ =
      mapDescentData.NatTrans.app f α D₁ ≫
        (K.mapDescentData f).map φ := sorry

/-- A modification of identity-base indexed functors induces a natural transformation between
their functors on descent data. -/
@[stacks 026E "indexed-functor modification descent transformation"]
def mapDescentData.natTrans
    {H K : IndexedFunctor (𝟭 C) F G}
    (α : H ⟶ K) :
    H.mapDescentData f ⟶ K.mapDescentData f where
  app D := mapDescentData.NatTrans.app f α D
  naturality _ _ φ := mapDescentData.NatTrans.naturality f α φ

/-- Components of the natural transformation on descent data are the component transformations
of the indexed-functor modification. -/
@[simp, stacks 026E "indexed-functor modification descent component readout"]
theorem mapDescentData.NatTrans.app_hom
    {H K : IndexedFunctor (𝟭 C) F G}
    (α : H ⟶ K) (D : F.DescentData f) (i : ι) :
    ((mapDescentData.natTrans f α).app D).hom i =
      (α.app (X i)).app (D.obj i) := sorry

/-- The identity indexed-functor modification induces the identity natural transformation on
descent data. -/
@[simp, stacks 026E "indexed-functor modification descent identity"]
theorem mapDescentData.NatTrans.id
    (H : IndexedFunctor (𝟭 C) F G) :
    mapDescentData.natTrans f (𝟙 H) =
      𝟙 (H.mapDescentData f) := sorry

/-- Vertical composition of indexed-functor modifications is preserved by descent-data
transport. -/
@[simp, stacks 026E "indexed-functor modification descent composition"]
theorem mapDescentData.NatTrans.comp
    {H K L : IndexedFunctor (𝟭 C) F G}
    (α : H ⟶ K) (β : K ⟶ L) :
    mapDescentData.natTrans f (α ≫ β) =
      mapDescentData.natTrans f α ≫
        mapDescentData.natTrans f β := sorry

/-- For a fixed indexing family, descent-data transport is functorial in the identity-base
indexed functor. -/
@[stacks 026E "indexed-functor descent transport functoriality"]
def mapDescentData.functor :
    IndexedFunctor (𝟭 C) F G ⥤
      (F.DescentData f ⥤ G.DescentData f) where
  obj H := H.mapDescentData f
  map α := mapDescentData.natTrans f α
  map_id H := mapDescentData.NatTrans.id f H
  map_comp α β := mapDescentData.NatTrans.comp f α β

/-- The object action of `mapDescentData.functor` is `mapDescentData`. -/
@[simp, stacks 026E "indexed-functor descent transport functor object"]
theorem mapDescentData.Functor.obj
    (H : IndexedFunctor (𝟭 C) F G) :
    (mapDescentData.functor f).obj H = H.mapDescentData f := sorry

/-- The morphism action of `mapDescentData.functor` is `mapDescentData.natTrans`. -/
@[simp, stacks 026E "indexed-functor descent transport functor morphism"]
theorem mapDescentData.Functor.map
    {H K : IndexedFunctor (𝟭 C) F G} (α : H ⟶ K) :
    (mapDescentData.functor f).map α =
      mapDescentData.natTrans f α := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
