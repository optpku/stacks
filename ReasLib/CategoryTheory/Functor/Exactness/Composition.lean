/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of Exact Functors

This leaf records closure of finite-limit and finite-colimit exactness under
functor composition, with separate left and right exact APIs.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

/-- The composite of two left exact functors is left exact. -/
@[stacks 015F "composition of left exact functors"]
theorem leftExactFunctor_comp
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {D : Type u₃} [Category.{v₃} D] {F : Functor A B} {G : Functor B D}
    (hF : leftExactFunctor A B F) (hG : leftExactFunctor B D G) :
    leftExactFunctor A D (F ⋙ G) := sorry

/-- The composite of two right exact functors is right exact. -/
@[stacks 015F "composition of right exact functors"]
theorem rightExactFunctor_comp
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {D : Type u₃} [Category.{v₃} D] {F : Functor A B} {G : Functor B D}
    (hF : rightExactFunctor A B F) (hG : rightExactFunctor B D G) :
    rightExactFunctor A D (F ⋙ G) := sorry

/-- The composite of two exact functors is exact. -/
@[stacks 015F "composition of exact functors"]
theorem exactFunctor_comp
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {D : Type u₃} [Category.{v₃} D] {F : Functor A B} {G : Functor B D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := sorry

namespace LeftExactFunctor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {D : Type u₃} [Category.{v₃} D]

/-- The bundled composite of two left exact functors. -/
@[stacks 015F "composition of bundled left exact functors"]
noncomputable abbrev comp (F : LeftExactFunctor A B) (G : LeftExactFunctor B D) :
    LeftExactFunctor A D :=
  ((LeftExactFunctor.whiskeringLeft A B D).obj F).obj G

end LeftExactFunctor

namespace RightExactFunctor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {D : Type u₃} [Category.{v₃} D]

/-- The bundled composite of two right exact functors. -/
@[stacks 015F "composition of bundled right exact functors"]
noncomputable abbrev comp (F : RightExactFunctor A B) (G : RightExactFunctor B D) :
    RightExactFunctor A D :=
  ((RightExactFunctor.whiskeringLeft A B D).obj F).obj G

end RightExactFunctor

namespace ExactFunctor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {D : Type u₃} [Category.{v₃} D]

/-- The bundled composite of two exact functors.  Bundling owns the canonical
finite-limit and finite-colimit instances, so downstream APIs do not need
local instances for the underlying composite. -/
@[stacks 015F "composition of bundled exact functors"]
noncomputable abbrev comp (F : ExactFunctor A B) (G : ExactFunctor B D) :
    ExactFunctor A D :=
  ((ExactFunctor.whiskeringLeft A B D).obj F).obj G

/-- The underlying functor of an exact bundled composite is ordinary functor composition. -/
@[simp]
theorem comp_obj (F : ExactFunctor A B) (G : ExactFunctor B D) :
    (F.comp G).obj = F.obj ⋙ G.obj := sorry

/-- Object computation for an exact bundled composite. -/
@[simp]
theorem comp_obj_obj (F : ExactFunctor A B) (G : ExactFunctor B D) (X : A) :
    (F.comp G).obj.obj X = G.obj.obj (F.obj.obj X) := sorry

/-- Morphism computation for an exact bundled composite. -/
@[simp]
theorem comp_obj_map (F : ExactFunctor A B) (G : ExactFunctor B D) {X Y : A} (f : X ⟶ Y) :
    (F.comp G).obj.map f = G.obj.map (F.obj.map f) := sorry

end ExactFunctor

end CategoryTheory
