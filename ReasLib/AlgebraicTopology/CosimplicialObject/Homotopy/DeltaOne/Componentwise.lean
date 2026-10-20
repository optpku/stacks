/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Componentwise cosimplicial homotopies

This module defines the product-free, degreewise `Δ[1]`-indexed presentation of a homotopy
between morphisms of cosimplicial objects.  It depends only on the canonical endpoint simplices
of the simplicial interval and does not require cotensors or products in the target category.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

/-- A product-free cosimplicial homotopy from `a` to `b` is a natural family of maps indexed by
the simplices of `Δ[1]`, with the constant endpoints equal to `a` and `b`. -/
@[stacks 0FKJ]
structure DeltaOneHomotopy (a b : U ⟶ V) where
  /-- The degreewise component indexed by a simplex of `Δ[1]`. -/
  hom {n : SimplexCategory} (i : (Δ[1] : SSet.{0}).obj (op n)) : U.obj n ⟶ V.obj n
  /-- Evaluation at the constant `0` simplex recovers `a`. -/
  zero_endpoint (n : SimplexCategory) :
    hom (SSet.deltaOne.endpoint 0 (op n)) = a.app n
  /-- Evaluation at the constant `1` simplex recovers `b`. -/
  one_endpoint (n : SimplexCategory) :
    hom (SSet.deltaOne.endpoint 1 (op n)) = b.app n
  /-- The component family is natural with respect to simplex operators. -/
  naturality {n₁ n₂ : SimplexCategory} (σ : n₁ ⟶ n₂)
      (i : (Δ[1] : SSet).obj (op n₂)) :
    CommSq (U.map σ) (hom ((Δ[1] : SSet).map σ.op i)) (hom i) (V.map σ)

namespace DeltaOneHomotopy

/-- Extensionality for product-free `Δ[1]`-indexed cosimplicial homotopies. -/
@[ext, stacks 0FKJ "product-free cosimplicial homotopy extensionality"]
theorem ext {H K : DeltaOneHomotopy a b}
    (h : ∀ ⦃n : SimplexCategory⦄, (i : (Δ[1] : SSet.{0}).obj (op n)) →
      H.hom i = K.hom i) : H = K := sorry

/-- A product-free homotopy evaluates to its component at every simplex of `Δ[1]`. -/
@[stacks 0FKJ "evaluation of a product-free cosimplicial homotopy"]
instance : CoeFun (DeltaOneHomotopy a b) (fun _ ↦ ∀ ⦃n : SimplexCategory⦄,
    (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n)) where
  coe H := fun {_} i ↦ H.hom i

/-- The constant product-free `Δ[1]`-indexed homotopy on a cosimplicial morphism. -/
@[stacks 0FKJ "constant product-free cosimplicial homotopy"]
def refl (a : U ⟶ V) : DeltaOneHomotopy a a where
  hom {_} _ := a.app _
  zero_endpoint := sorry
  one_endpoint := sorry
  naturality := sorry

/-- Every component of the constant product-free homotopy is the original morphism component. -/
@[simp, stacks 0FKJ "constant product-free homotopy component"]
theorem refl.hom (a : U ⟶ V) {n : SimplexCategory}
    (i : (Δ[1] : SSet.{0}).obj (op n)) :
    (refl a).hom i = a.app n := sorry

/-- Transport the constant product-free homotopy along an equality of morphisms. -/
@[stacks 0FKJ "equality transport for product-free cosimplicial homotopy"]
def ofEq (h : a = b) : DeltaOneHomotopy a b :=
  h ▸ refl a

/-- Every component of an equality-transport product-free homotopy is the source component. -/
@[simp, stacks 0FKJ "equality-transport product-free homotopy component"]
theorem ofEq.hom (h : a = b) {n : SimplexCategory}
    (i : (Δ[1] : SSet.{0}).obj (op n)) :
    (ofEq h).hom i = a.app n := sorry

/-- Transport a product-free `Δ[1]`-indexed homotopy along endpoint equalities. -/
@[stacks 0FKJ "endpoint transport for product-free cosimplicial homotopies"]
def cast {a b a' b' : U ⟶ V}
    (ha : a = a') (hb : b = b') (H : DeltaOneHomotopy a b) :
    DeltaOneHomotopy a' b' :=
  ha ▸ hb ▸ H

/-- The simplex-indexed component is unchanged by endpoint transport. -/
@[simp, stacks 0FKJ "component formula for transported product-free homotopies"]
theorem cast.hom {a b a' b' : U ⟶ V}
    (ha : a = a') (hb : b = b') (H : DeltaOneHomotopy a b)
    {n : SimplexCategory} (i : (Δ[1] : SSet.{0}).obj (op n)) :
    (cast ha hb H).hom i = H.hom i := sorry

end DeltaOneHomotopy

end CategoryTheory.CosimplicialObject
