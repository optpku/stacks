/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.PseudoCone

/-!
# Categorical commutative squares in the pith of `Cat`

This module gives an ordinary categorical commutative square a direct pith-valued
pseudopullback-cone view. The composite representation through `toPseudoPullbackCone` remains
an implementation detail, while downstream statements can use the square's familiar fields.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe v u

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

open Bicategory

variable {X : Type u} [Category.{v} X]
variable {A : Type u} [Category.{v} A]
variable {B : Type u} [Category.{v} B]
variable {C : Type u} [Category.{v} C]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- A categorical commutative square, regarded directly as a pseudopullback cone in the pith
of `Cat`. It retains the categories and functors and keeps only natural isomorphisms as
`2`-morphisms. -/
def toPith (P : CatCommSqOver F G X) :=
  P.toPseudoPullbackCone.toPith

/-- The apex of the pith-valued cone associated to a categorical commutative square. -/
@[simp]
theorem toPith.pt (P : CatCommSqOver F G X) :
    P.toPith.pt = Pith.mk (Cat.of X) := sorry

/-- The left leg of the pith-valued cone associated to a categorical commutative square. -/
@[simp]
theorem toPith.fst (P : CatCommSqOver F G X) :
    P.toPith.fst = Core.mk P.fst.toCatHom := sorry

/-- The right leg of the pith-valued cone associated to a categorical commutative square. -/
@[simp]
theorem toPith.snd (P : CatCommSqOver F G X) :
    P.toPith.snd = Core.mk P.snd.toCatHom := sorry

/-- The comparison isomorphism of the pith-valued cone associated to a categorical
commutative square. -/
@[simp]
theorem toPith.iso (P : CatCommSqOver F G X) :
    P.toPith.iso = Core.isoMk (Cat.Hom.isoMk P.iso) := sorry

/- Data audit (mathlib 4.32): `toPith` composes the explicit `toPseudoPullbackCone` and
`PseudoPullbackCone.toPith` data owners. Its apex, legs, and comparison contain no additional
choice; proof debt is confined to the separate computation statements. -/

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
