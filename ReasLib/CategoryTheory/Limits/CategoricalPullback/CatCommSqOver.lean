/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Categorical pullback squares and their comparison functors

This module exposes the canonical square of an explicit categorical pullback as a bundled
`CatCommSqOver`, for APIs that take the square as data rather than through typeclass search.
It also gives an arbitrary categorical commutative square its canonical comparison functor to
the explicit categorical pullback, independently of any bicategorical universal property.
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoricalPullback
open scoped CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/-- The canonical categorical square on the two projections from `F ⊡ G`.

This is a genuine bundled-data bridge rather than a second pullback owner: mathlib's
`catCommSq F G` is a typeclass instance, while the universal-property and functoriality APIs used
by later items take an explicit `CatCommSqOver F G (F ⊡ G)` value. -/
@[stacks 003R "canonical categorical-pullback square"]
def catCommSqOver (F : A ⥤ C) (G : B ⥤ C) : CatCommSqOver F G (F ⊡ G) where
  fst := π₁ F G
  snd := π₂ F G
  iso := (catCommSq F G).iso

/-- The forward component of the canonical categorical-pullback square is the structural
isomorphism stored by the corresponding categorical-pullback object. -/
@[simp]
theorem catCommSq.iso.hom.app (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    (catCommSq F G).iso.hom.app x = x.iso.hom := sorry

/-- The inverse component of the canonical categorical-pullback square is the inverse of the
structural isomorphism stored by the corresponding categorical-pullback object. -/
@[simp]
theorem catCommSq.iso.inv.app (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    (catCommSq F G).iso.inv.app x = x.iso.inv := sorry

end CategoricalPullback

universe v₄ u₄

namespace CategoricalPullback.CatCommSqOver

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {X : Type u₄} [Category.{v₄} X]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- The canonical comparison from the apex of a categorical commutative square to the
explicit categorical pullback of its cospan.

This is a readable, square-oriented facade for mathlib's
`CatCommSqOver.toFunctorToCategoricalPullback`; it does not assume that the square has any
universal property. -/
abbrev comparison (P : CatCommSqOver F G X) : X ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G X).obj P

/-- The first projection of the comparison functor on objects. -/
@[simp]
theorem comparison.obj.fst (P : CatCommSqOver F G X) (x : X) :
    (P.comparison.obj x).fst = P.fst.obj x := sorry

/-- The second projection of the comparison functor on objects. -/
@[simp]
theorem comparison.obj.snd (P : CatCommSqOver F G X) (x : X) :
    (P.comparison.obj x).snd = P.snd.obj x := sorry

/-- The structural isomorphism carried by the comparison functor on objects. -/
@[simp]
theorem comparison.obj.iso (P : CatCommSqOver F G X) (x : X) :
    (P.comparison.obj x).iso = P.iso.app x := sorry

/-- The forward structural map carried by the comparison functor on objects. -/
@[simp]
theorem comparison.obj.iso.hom (P : CatCommSqOver F G X) (x : X) :
    (P.comparison.obj x).iso.hom = (P.iso.app x).hom := sorry

/-- The inverse structural map carried by the comparison functor on objects. -/
@[simp]
theorem comparison.obj.iso.inv (P : CatCommSqOver F G X) (x : X) :
    (P.comparison.obj x).iso.inv = (P.iso.app x).inv := sorry

/-- The first projection of the comparison functor on morphisms. -/
@[simp]
theorem comparison.map.fst (P : CatCommSqOver F G X) {x y : X} (f : x ⟶ y) :
    (P.comparison.map f).fst = P.fst.map f := sorry

/-- The second projection of the comparison functor on morphisms. -/
@[simp]
theorem comparison.map.snd (P : CatCommSqOver F G X) {x y : X} (f : x ⟶ y) :
    (P.comparison.map f).snd = P.snd.map f := sorry

end CategoricalPullback.CatCommSqOver

end CategoryTheory.Limits
