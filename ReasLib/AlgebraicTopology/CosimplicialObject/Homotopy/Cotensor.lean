/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Cotensor.Object
public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019W

# Cotensor-valued cosimplicial homotopies

This file uses the canonical standard-simplex endpoints to define the cotensor-valued homotopy
structure, its evaluation API, and the canonical reflexive and equality-transport constructions.
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

/-- A cosimplicial homotopy from `a` to `b` is a morphism `U ⟶ cotensor Δ[1] V` whose
endpoint evaluations recover `a` and `b`. -/
@[stacks 019W]
structure Homotopy (a b : U ⟶ V) where
  /-- The underlying map to the standard `1`-simplex cotensor. -/
  hom : U ⟶ cotensor (Δ[1] : SSet.{0}) V
  /-- Evaluation at the constant `0` simplex recovers `a`. -/
  zero_endpoint (n : SimplexCategory) :
    hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 0 (op n)) = a.app n
  /-- Evaluation at the constant `1` simplex recovers `b`. -/
  one_endpoint (n : SimplexCategory) :
    hom.app n ≫ Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 1 (op n)) = b.app n

namespace Homotopy

/-- Two cotensor-valued homotopies with the same underlying morphism are equal. -/
@[ext, stacks 019W "cosimplicial homotopy extensionality"]
theorem ext {a b : U ⟶ V} {H K : Homotopy a b}
    (h : H.hom = K.hom) : H = K := sorry

/-- Evaluating a cosimplicial homotopy at a simplex of `Δ[1]` gives the corresponding
degreewise component map `U.obj n ⟶ V.obj n`. -/
@[stacks 019W "cosimplicial homotopy simplex evaluation"]
def app {a b : U ⟶ V} (H : Homotopy a b) {n : SimplexCategory}
    (α : (Δ[1] : SSet.{0}).obj (op n)) : U.obj n ⟶ V.obj n :=
  H.hom.app n ≫ Pi.π (fun _ ↦ V.obj n) α

/-- A cotensor-valued homotopy can be evaluated as a degreewise family of morphisms. -/
@[stacks 019W "cosimplicial homotopy evaluation function"]
instance {a b : U ⟶ V} :
    CoeFun (Homotopy a b) (fun _ ↦ ∀ ⦃n : SimplexCategory⦄,
      (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n)) where
  coe H := fun {_} α ↦ H.app α

namespace refl

/-- Naturality of the constant cotensor-valued morphism associated to a cosimplicial morphism. -/
@[stacks 019W "constant cosimplicial homotopy naturality"]
theorem naturality (a : U ⟶ V) {m n : SimplexCategory} (f : m ⟶ n) :
    U.map f ≫ Pi.lift (fun _ : (Δ[1] : SSet.{0}).obj (op n) ↦ a.app n) =
      Pi.lift (fun _ : (Δ[1] : SSet.{0}).obj (op m) ↦ a.app m) ≫
        (cotensor (Δ[1] : SSet.{0}) V).map f := sorry

/-- The zero endpoint of the constant cotensor-valued morphism is the original morphism. -/
@[stacks 019W "constant cosimplicial homotopy zero endpoint"]
theorem zero_endpoint (a : U ⟶ V) (n : SimplexCategory) :
    Pi.lift (fun _ : (Δ[1] : SSet.{0}).obj (op n) ↦ a.app n) ≫
      Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 0 (op n)) = a.app n := sorry

/-- The one endpoint of the constant cotensor-valued morphism is the original morphism. -/
@[stacks 019W "constant cosimplicial homotopy one endpoint"]
theorem one_endpoint (a : U ⟶ V) (n : SimplexCategory) :
    Pi.lift (fun _ : (Δ[1] : SSet.{0}).obj (op n) ↦ a.app n) ≫
      Pi.π (fun _ ↦ V.obj n) (SSet.deltaOne.endpoint 1 (op n)) = a.app n := sorry

end refl

/-- The constant cotensor-valued cosimplicial homotopy on a morphism. -/
@[stacks 019W "constant cotensor-valued cosimplicial homotopy"]
def refl (a : U ⟶ V) : Homotopy a a where
  hom :=
    { app n := Pi.lift (fun _ : (Δ[1] : SSet.{0}).obj (op n) ↦ a.app n)
      naturality _ _ f := refl.naturality a f }
  zero_endpoint := refl.zero_endpoint a
  one_endpoint := refl.one_endpoint a

/-- Every simplex evaluation of the constant homotopy is the original morphism component. -/
@[simp, stacks 019W "constant cosimplicial homotopy evaluation"]
theorem refl.app (a : U ⟶ V) {n : SimplexCategory}
    (i : (Δ[1] : SSet.{0}).obj (op n)) :
    (refl a).app i = a.app n := sorry

/-- Transport the constant cotensor-valued homotopy along an equality of morphisms. -/
@[stacks 019W "equality transport for cotensor-valued cosimplicial homotopy"]
def ofEq {a b : U ⟶ V} (h : a = b) : Homotopy a b :=
  h ▸ refl a

/-- Every simplex evaluation of an equality-transport homotopy is the source component. -/
@[simp, stacks 019W "equality-transport homotopy evaluation"]
theorem ofEq.app {a b : U ⟶ V} (h : a = b) {n : SimplexCategory}
    (i : (Δ[1] : SSet.{0}).obj (op n)) :
    (ofEq h).app i = a.app n := sorry

/-- Transport a cotensor-valued cosimplicial homotopy along endpoint equalities. -/
@[stacks 019W "endpoint transport for cosimplicial homotopies"]
def cast {a b a' b' : U ⟶ V}
    (ha : a = a') (hb : b = b') (H : Homotopy a b) : Homotopy a' b' :=
  ha ▸ hb ▸ H

/-- The simplex evaluation is unchanged by endpoint transport. -/
@[simp, stacks 019W "component formula for transported cosimplicial homotopies"]
theorem cast.app {a b a' b' : U ⟶ V}
    (ha : a = a') (hb : b = b') (H : Homotopy a b)
    {n : SimplexCategory} (i : (Δ[1] : SSet.{0}).obj (op n)) :
    (cast ha hb H).app i = H.app i := sorry

/-- A cosimplicial homotopy is determined by its degreewise evaluations at all simplices of
`Δ[1]`. -/
@[stacks 019W "cosimplicial homotopy evaluation extensionality"]
theorem ext_app {a b : U ⟶ V} {H K : Homotopy a b}
    (h : ∀ (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n)),
      H.app (n := n) α = K.app (n := n) α) :
    H = K := sorry

/-- Evaluation at the constant zero simplex recovers the source endpoint. -/
@[simp, stacks 019W "cosimplicial homotopy zero endpoint evaluation"]
theorem app.zero {a b : U ⟶ V} (H : Homotopy a b) (n : SimplexCategory) :
    H (SSet.deltaOne.endpoint 0 (op n)) = a.app n := sorry

/-- Evaluation at the constant one simplex recovers the target endpoint. -/
@[simp, stacks 019W "cosimplicial homotopy one endpoint evaluation"]
theorem app.one {a b : U ⟶ V} (H : Homotopy a b) (n : SimplexCategory) :
    H (SSet.deltaOne.endpoint 1 (op n)) = b.app n := sorry

/-- Naturality: evaluating at a simplex commutes with the cosimplicial structure. -/
@[stacks 019W "Equation 14.28.1.1"]
theorem naturality {a b : U ⟶ V} (H : Homotopy a b)
    {m n : SimplexCategory} (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)) :
    CommSq (U.map f) (H ((Δ[1] : SSet.{0}).map f.op α)) (H α) (V.map f) := sorry

end Homotopy

end Homotopy

end CategoryTheory.CosimplicialObject
