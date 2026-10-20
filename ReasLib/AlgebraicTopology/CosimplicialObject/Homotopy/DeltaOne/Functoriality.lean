/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Componentwise

/-!
# Functoriality of componentwise cosimplicial homotopies

This module provides composition in the source and target variables, conjugation by an
isomorphism, and degreewise application of a functor for product-free cosimplicial homotopies.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u v u' v' u'' v''

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {E : Type u''} [Category.{v''} E]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

namespace DeltaOneHomotopy

variable {T W : CosimplicialObject C}

/-- Precompose every component of a product-free homotopy by a morphism of cosimplicial objects. -/
@[stacks 0FKJ "precomposition of product-free cosimplicial homotopies"]
def precomp (H : DeltaOneHomotopy a b) (p : T ⟶ U) :
    DeltaOneHomotopy (p ≫ a) (p ≫ b) where
  hom i := p.app _ ≫ H.hom i
  zero_endpoint := sorry
  one_endpoint := sorry
  naturality := sorry

/-- Precomposition acts on each simplex-indexed component by precomposition. -/
@[simp, stacks 0FKJ "components of a precomposed product-free homotopy"]
theorem precomp.hom (H : DeltaOneHomotopy a b) (p : T ⟶ U)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (H.precomp p).hom i = p.app n ≫ H.hom i := sorry

/-- Postcompose every component of a product-free homotopy by a morphism of cosimplicial objects. -/
@[stacks 0FKJ "postcomposition of product-free cosimplicial homotopies"]
def postcomp (H : DeltaOneHomotopy a b) (p : V ⟶ W) :
    DeltaOneHomotopy (a ≫ p) (b ≫ p) where
  hom i := H.hom i ≫ p.app _
  zero_endpoint := sorry
  one_endpoint := sorry
  naturality := sorry

/-- Postcomposition acts on each simplex-indexed component by postcomposition. -/
@[simp, stacks 0FKJ "components of a postcomposed product-free homotopy"]
theorem postcomp.hom (H : DeltaOneHomotopy a b) (p : V ⟶ W)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (H.postcomp p).hom i = H.hom i ≫ p.app n := sorry

/-- Simultaneously precompose and postcompose a product-free homotopy. -/
@[stacks 0FKJ "two-sided composition of product-free cosimplicial homotopies"]
def precompPostcomp (H : DeltaOneHomotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    DeltaOneHomotopy (p ≫ a ≫ q) (p ≫ b ≫ q) :=
  (H.postcomp q).precomp p

/-- Two-sided composition acts on every component by the corresponding two-sided composite. -/
@[simp, stacks 0FKJ "components of a two-sided product-free homotopy composite"]
theorem precompPostcomp.hom (H : DeltaOneHomotopy a b) (p : T ⟶ U) (q : V ⟶ W)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (H.precompPostcomp p q).hom i = p.app n ≫ H.hom i ≫ q.app n := sorry

/-- Precomposition by an identity is the original homotopy after endpoint transport. -/
@[simp, stacks 0FKJ "identity precomposition of product-free homotopies"]
theorem precomp.id (H : DeltaOneHomotopy a b) :
    cast (Category.id_comp a) (Category.id_comp b) (H.precomp (𝟙 U)) = H := sorry

/-- Iterated precomposition agrees with precomposition by the composite after endpoint transport. -/
@[stacks 0FKJ "composition of product-free homotopy precomposition"]
theorem precomp.comp {S : CosimplicialObject C} (H : DeltaOneHomotopy a b)
    (q : T ⟶ U) (p : S ⟶ T) :
    cast (Category.assoc p q a) (Category.assoc p q b) (H.precomp (p ≫ q)) =
      (H.precomp q).precomp p := sorry

/-- Postcomposition by an identity is the original homotopy after endpoint transport. -/
@[simp, stacks 0FKJ "identity postcomposition of product-free homotopies"]
theorem postcomp.id (H : DeltaOneHomotopy a b) :
    cast (Category.comp_id a) (Category.comp_id b) (H.postcomp (𝟙 V)) = H := sorry

/-- Iterated postcomposition agrees with postcomposition by the composite after endpoint
transport. -/
@[stacks 0FKJ "composition of product-free homotopy postcomposition"]
theorem postcomp.comp {X : CosimplicialObject C} (H : DeltaOneHomotopy a b)
    (p : V ⟶ W) (q : W ⟶ X) :
    cast (Category.assoc a p q) (Category.assoc b p q) ((H.postcomp p).postcomp q) =
      H.postcomp (p ≫ q) := sorry

/-- Precomposition and postcomposition commute after the canonical endpoint transport. -/
@[stacks 0FKJ "commutation of product-free homotopy composition"]
theorem precomp_postcomp (H : DeltaOneHomotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    cast (Category.assoc p a q) (Category.assoc p b q) ((H.precomp p).postcomp q) =
      (H.postcomp q).precomp p := sorry

/-- Conjugate a product-free homotopy between endomorphisms along an isomorphism of
cosimplicial objects. -/
def conjugate {a b : U ⟶ U} (H : DeltaOneHomotopy a b) (e : T ≅ U) :
    DeltaOneHomotopy (e.hom ≫ a ≫ e.inv) (e.hom ≫ b ≫ e.inv) :=
  H.precompPostcomp e.hom e.inv

/-- Conjugation acts on a product-free homotopy by conjugating each component. -/
@[simp]
theorem conjugate.hom {a b : U ⟶ U} (H : DeltaOneHomotopy a b) (e : T ≅ U)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (conjugate H e).hom i = e.hom.app n ≫ H.hom i ≫ e.inv.app n := sorry

/-- Applying a functor to each component of a product-free homotopy. -/
@[stacks 0FKJ "functoriality of product-free cosimplicial homotopies"]
def whiskerRight (H : DeltaOneHomotopy a b) (F : C ⥤ D) :
    DeltaOneHomotopy (Functor.whiskerRight a F) (Functor.whiskerRight b F) where
  hom i := F.map (H.hom i)
  zero_endpoint := sorry
  one_endpoint := sorry
  naturality := sorry

/-- Whiskering a product-free homotopy applies the functor to each component. -/
@[simp, stacks 0FKJ "components of a whiskered product-free homotopy"]
theorem whiskerRight.hom (H : DeltaOneHomotopy a b) (F : C ⥤ D)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (H.whiskerRight F).hom i = F.map (H.hom i) := sorry

/-- Applying the identity functor fixes every component of a product-free homotopy. -/
@[simp, stacks 019Y "identity functor on product-free homotopy components"]
theorem whiskerRight.id_hom (H : DeltaOneHomotopy a b)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    (H.whiskerRight (𝟭 C)).hom i = H.hom i := sorry

/-- Successive functor applications agree componentwise with application of the composite. -/
@[stacks 019Y "composite functor on product-free homotopy components"]
theorem whiskerRight.comp_hom (H : DeltaOneHomotopy a b) (F : C ⥤ D) (G : D ⥤ E)
    {n : SimplexCategory} (i : (Δ[1] : SSet).obj (op n)) :
    ((H.whiskerRight F).whiskerRight G).hom i =
      (H.whiskerRight (F ⋙ G)).hom i := sorry

end DeltaOneHomotopy

end CategoryTheory.CosimplicialObject
