/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Cotensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of cotensor-valued cosimplicial homotopies

This file owns precomposition, postcomposition, and their combined action on homotopies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

section Homotopy

variable {U V : CosimplicialObject C}
variable [HasCotensor (Δ[1] : SSet.{0}) V]

namespace Homotopy

variable {a b : U ⟶ V} {T W : CosimplicialObject C}

namespace precomp

/-- The zero endpoint equation for a cotensor-valued homotopy after precomposition. -/
@[stacks 019W "precomposed cosimplicial homotopy zero endpoint"]
theorem zero_endpoint (H : Homotopy a b) (p : T ⟶ U) (n : SimplexCategory) :
    (p ≫ H.hom).app n ≫
        Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 0 (op n)) =
      (p ≫ a).app n := sorry

/-- The one endpoint equation for a cotensor-valued homotopy after precomposition. -/
@[stacks 019W "precomposed cosimplicial homotopy one endpoint"]
theorem one_endpoint (H : Homotopy a b) (p : T ⟶ U) (n : SimplexCategory) :
    (p ≫ H.hom).app n ≫
        Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 1 (op n)) =
      (p ≫ b).app n := sorry

end precomp

/-- Precompose a cotensor-valued cosimplicial homotopy. -/
@[stacks 019W "precomposition of cosimplicial homotopies"]
def precomp (H : Homotopy a b) (p : T ⟶ U) : Homotopy (p ≫ a) (p ≫ b) where
  hom := p ≫ H.hom
  zero_endpoint := precomp.zero_endpoint H p
  one_endpoint := precomp.one_endpoint H p

/-- Precomposition acts on the underlying cotensor-valued morphism by composition. -/
@[simp, stacks 019W "precomposition on cosimplicial homotopies"]
theorem precomp.hom (H : Homotopy a b) (p : T ⟶ U) :
    (H.precomp p).hom = p ≫ H.hom := sorry

namespace postcomp

/-- The zero endpoint equation for a cotensor-valued homotopy after postcomposition. -/
@[stacks 019W "postcomposed cosimplicial homotopy zero endpoint"]
theorem zero_endpoint [HasCotensor (Δ[1] : SSet.{0}) W]
    (H : Homotopy a b) (p : V ⟶ W) (n : SimplexCategory) :
    (H.hom ≫ cotensor.hom (Δ[1] : SSet.{0}) p).app n ≫
        Pi.π (fun _ ↦ W.obj n) (SSet.deltaOne.endpoint 0 (op n)) =
      (a ≫ p).app n := sorry

/-- The one endpoint equation for a cotensor-valued homotopy after postcomposition. -/
@[stacks 019W "postcomposed cosimplicial homotopy one endpoint"]
theorem one_endpoint [HasCotensor (Δ[1] : SSet.{0}) W]
    (H : Homotopy a b) (p : V ⟶ W) (n : SimplexCategory) :
    (H.hom ≫ cotensor.hom (Δ[1] : SSet.{0}) p).app n ≫
        Pi.π (fun _ ↦ W.obj n) (SSet.deltaOne.endpoint 1 (op n)) =
      (b ≫ p).app n := sorry

end postcomp

/-- Postcompose a cotensor-valued cosimplicial homotopy. -/
@[stacks 019W "postcomposition of cosimplicial homotopies"]
def postcomp [HasCotensor (Δ[1] : SSet.{0}) W]
    (H : Homotopy a b) (p : V ⟶ W) : Homotopy (a ≫ p) (b ≫ p) where
  hom := H.hom ≫ cotensor.hom (Δ[1] : SSet.{0}) p
  zero_endpoint := postcomp.zero_endpoint H p
  one_endpoint := postcomp.one_endpoint H p

/-- Postcomposition acts on the underlying cotensor-valued morphism through the cotensor map. -/
@[simp, stacks 019W "postcomposition on cosimplicial homotopies"]
theorem postcomp.hom [HasCotensor (Δ[1] : SSet.{0}) W]
    (H : Homotopy a b) (p : V ⟶ W) :
    (H.postcomp p).hom = H.hom ≫ cotensor.hom (Δ[1] : SSet.{0}) p := sorry

/-- Simultaneously precompose and postcompose a cotensor-valued cosimplicial homotopy. -/
@[stacks 019W "two-sided composition of cosimplicial homotopies"]
def precompPostcomp [HasCotensor (Δ[1] : SSet.{0}) W]
    (H : Homotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    Homotopy (p ≫ a ≫ q) (p ≫ b ≫ q) :=
  (H.postcomp q).precomp p

/-- The underlying morphism of a two-sidedly composed homotopy is the expected composite. -/
@[simp, stacks 019W "two-sided composition on cosimplicial homotopies"]
theorem precompPostcomp.hom [HasCotensor (Δ[1] : SSet.{0}) W]
    (H : Homotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    (H.precompPostcomp p q).hom =
      p ≫ H.hom ≫ cotensor.hom (Δ[1] : SSet.{0}) q := sorry

end Homotopy

end Homotopy

end CategoryTheory.CosimplicialObject
