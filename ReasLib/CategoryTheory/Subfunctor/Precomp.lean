/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Precomposition of subfunctors

A subfunctor of a type-valued functor restricts canonically along any functor into its source
category. This file owns that general construction and its objectwise API.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.Subfunctor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Precompose a subfunctor with a functor into the source category of its ambient functor. -/
@[stacks 01JK "subfunctor precomposition"]
def precomp {F : C ⥤ Type w} (H : Subfunctor F) (G : D ⥤ C) :
    Subfunctor (G ⋙ F) where
  obj X := H.obj (G.obj X)
  map f := H.map (G.map f)

/-- The objectwise subset of a precomposed subfunctor is the original subset at the image
object. -/
@[simp, stacks 01JK "precomposed subfunctor object"]
theorem precomp_obj {F : C ⥤ Type w} (H : Subfunctor F) (G : D ⥤ C) (X : D) :
    (H.precomp G).obj X = H.obj (G.obj X) := sorry

/-- Membership in a precomposed subfunctor is membership in the original subfunctor at the image
object. -/
@[simp, stacks 01JK "precomposed subfunctor membership"]
theorem mem_precomp_obj {F : C ⥤ Type w} (H : Subfunctor F) (G : D ⥤ C)
    {X : D} {x : F.obj (G.obj X)} :
    x ∈ (H.precomp G).obj X ↔ x ∈ H.obj (G.obj X) := sorry

/-- The associated functor of a precomposed subfunctor acts through the original associated
functor. -/
@[simp, stacks 01JK "precomposed subfunctor map"]
theorem precomp_map {F : C ⥤ Type w} (H : Subfunctor F) (G : D ⥤ C)
    {X Y : D} (f : X ⟶ Y) :
    (H.precomp G).toFunctor.map f = H.toFunctor.map (G.map f) := sorry

/-- Passing a precomposed subfunctor to its associated functor agrees with precomposition of the
associated functor. -/
@[stacks 01JK "precomposed associated functor"]
theorem precomp_toFunctor {F : C ⥤ Type w} (H : Subfunctor F) (G : D ⥤ C) :
    (H.precomp G).toFunctor = G ⋙ H.toFunctor := sorry

/-- The inclusion of a precomposed subfunctor is the whiskering of the original inclusion. -/
@[simp, stacks 01JK "precomposed subfunctor inclusion"]
theorem precomp_ι {F : C ⥤ Type w} (H : Subfunctor F) (G : D ⥤ C) :
    (H.precomp G).ι = Functor.whiskerLeft G H.ι := sorry

end CategoryTheory.Subfunctor
