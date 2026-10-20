/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Swapping bicategorical cospan transformations

This file gives the neutral symmetry API for transformations and modifications between
walking-cospan diagrams. Swapping exchanges the two endpoint components and generating
comparisons while leaving the common-target component fixed.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- Swap the two endpoint components and generating comparisons of a bicategorical cospan
transformation, leaving its common-target component fixed. -/
@[stacks 0040 "swap of a bicategorical cospan transformation"]
def swap (ψ : CospanTransform f g f' g') :
    CospanTransform g f g' f' :=
  mk ψ.right ψ.left ψ.base ψ.rightIso ψ.leftIso

/-- The left component of a swapped cospan transformation is the original right component. -/
@[simp]
theorem swap.left (ψ : CospanTransform f g f' g') :
    (swap ψ).left = ψ.right := sorry

/-- The right component of a swapped cospan transformation is the original left component. -/
@[simp]
theorem swap.right (ψ : CospanTransform f g f' g') :
    (swap ψ).right = ψ.left := sorry

/-- Swapping a cospan transformation preserves its common-target component. -/
@[simp]
theorem swap.base (ψ : CospanTransform f g f' g') :
    (swap ψ).base = ψ.base := sorry

/-- The left generating comparison of a swapped transformation is the original right
generating comparison. -/
@[simp]
theorem swap.leftIso (ψ : CospanTransform f g f' g') :
    (swap ψ).leftIso = ψ.rightIso := sorry

/-- The right generating comparison of a swapped transformation is the original left
generating comparison. -/
@[simp]
theorem swap.rightIso (ψ : CospanTransform f g f' g') :
    (swap ψ).rightIso = ψ.leftIso := sorry

/-- Swapping a cospan transformation twice recovers the original transformation. -/
@[simp]
theorem swap.involution (ψ : CospanTransform f g f' g') :
    swap (swap ψ) = ψ := sorry

/-- Swapping preserves identity cospan transformations. -/
@[simp]
theorem swap.id (f : x ⟶ z) (g : y ⟶ z) :
    swap (CospanTransform.id f g) = CospanTransform.id g f := sorry

/-- Swapping preserves vertical composition of cospan transformations. -/
@[simp]
theorem swap.comp
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') :
    swap (CospanTransform.comp ψ φ) =
      CospanTransform.comp (swap ψ) (swap φ) := sorry

namespace Hom

variable {ψ φ : CospanTransform f g f' g'}

/-- Swap the endpoint components of a modification between cospan transformations, leaving
its common-target component fixed. -/
@[stacks 0040 "swap of a bicategorical cospan modification"]
def swap (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    Pseudofunctor.StrongTrans.Hom
      (CospanTransform.swap ψ) (CospanTransform.swap φ) :=
  Hom.mk
    (Hom.right Γ : ψ.right ⟶ φ.right)
    (Hom.left Γ : ψ.left ⟶ φ.left)
    (Hom.base Γ : ψ.base ⟶ φ.base)
    (Hom.right_naturality Γ) (Hom.left_naturality Γ)

/-- The left component of a swapped modification is the original right component. -/
@[simp]
theorem swap.left (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    Hom.left (Hom.swap Γ) = Hom.right Γ := sorry

/-- The right component of a swapped modification is the original left component. -/
@[simp]
theorem swap.right (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    Hom.right (Hom.swap Γ) = Hom.left Γ := sorry

/-- Swapping a modification preserves its common-target component. -/
@[simp]
theorem swap.base (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    Hom.base (Hom.swap Γ) = Hom.base Γ := sorry

/-- Swapping preserves identity cospan modifications. -/
@[simp]
theorem swap.id (ψ : CospanTransform f g f' g') :
    swap (Hom.id ψ) = Hom.id (CospanTransform.swap ψ) := sorry

/-- Swapping preserves vertical composition of cospan modifications. -/
@[simp]
theorem swap.comp
    {χ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) :
    swap (Hom.comp Γ Δ) = Hom.comp (swap Γ) (swap Δ) := sorry

/-- After the canonical endpoint transports, swapping a modification twice recovers the
original modification. -/
@[simp]
theorem swap.involution (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    eqToHom (CospanTransform.swap.involution ψ).symm ≫
        swap (swap Γ) ≫
      eqToHom (CospanTransform.swap.involution φ) = Γ := sorry

end Hom

/-- Swapping transformations and modifications defines a functor between the two cospan
hom-categories obtained by exchanging the endpoints. -/
@[stacks 0040 "swap functor on bicategorical cospan transformations"]
def swap.functor :
    CospanTransform f g f' g' ⥤ CospanTransform g f g' f' where
  obj ψ := swap ψ
  map Γ := Hom.swap Γ
  map_id ψ := Hom.swap.id ψ
  map_comp Γ Δ := Hom.swap.comp Γ Δ

/-- The object action of the cospan swap functor swaps a transformation. -/
@[simp]
theorem swap.functor.obj (ψ : CospanTransform f g f' g') :
    (swap.functor (f := f) (g := g) (f' := f') (g' := g')).obj ψ = swap ψ := sorry

/-- The morphism action of the cospan swap functor swaps a modification. -/
@[simp]
theorem swap.functor.map
    {ψ φ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (swap.functor (f := f) (g := g) (f' := f') (g' := g')).map Γ = Hom.swap Γ := sorry

/-- The composite of the two endpoint-swap functors is the identity functor. -/
@[simp]
theorem swap.functor.involution :
    swap.functor (f := f) (g := g) (f' := f') (g' := g') ⋙
        swap.functor (f := g) (g := f) (f' := g') (g' := f') =
      𝟭 (CospanTransform f g f' g') := sorry

/- Data and axiom audit:

`swap` and `Hom.swap` store the exchanged endpoint data directly through the canonical
generator-level constructors. `swap.functor` uses those data owners for its object and morphism
actions. Any `sorryAx` is confined to the inherited coherence fields and the theorem-level
functor laws; no component, `1`-morphism, `2`-morphism, or comparison isomorphism is chosen. -/

end CategoryTheory.Bicategory.CospanTransform
