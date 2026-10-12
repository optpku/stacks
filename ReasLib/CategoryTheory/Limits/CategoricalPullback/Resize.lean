/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.AsSmall
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit

/-!
# Universe resizing for categorical pullback squares

The bicategory `Cat` is universe-homogeneous: all category objects in one cospan must use the same
object and Hom universes. A general `CatCommSqOver` has no such restriction. This file gives the
canonical bridge by transporting all four categories to common `AsSmall` models.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe vA uA vB uB vC uC vX uX

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- A categorical commutative square transported to common small models of its four categories. -/
def resize (P : CatCommSqOver F G X) :
    CatCommSqOver
      (Functor.asSmall.{max vB uB vX uX} F)
      (Functor.asSmall.{max vA uA vX uX} G)
      (AsSmall.{max vA uA vB uB vC uC vX uX} X) where
  fst := Functor.asSmall.{max vB uB vC uC} P.fst
  snd := Functor.asSmall.{max vA uA vC uC} P.snd
  iso := Functor.asSmallMapIso.{max vA uA vB uB} P.iso

namespace Resized

/-- The universe-independent bilimit predicate for a categorical commutative square: resize the
square canonically and apply the ordinary `Cat`-bilimit predicate. -/
abbrev IsBilimit (P : CatCommSqOver F G X) : Prop :=
  P.resize.IsBilimit

/-- A general categorical commutative square is a resized bilimit exactly when its canonical
comparison with the explicit categorical pullback is an equivalence. -/
theorem isBilimit_iff_comparisonIsEquivalence (P : CatCommSqOver F G X) :
    Resized.IsBilimit P ↔ P.comparison.IsEquivalence := sorry

end Resized

namespace Resized

variable {A B C X : Type (max uA vA)} [Category.{vA} A] [Category.{vA} B]
variable [Category.{vA} C] [Category.{vA} X]
variable {F : A ⥤ C} {G : B ⥤ C}

/-- In the universe-homogeneous case, the resized bilimit predicate agrees with the ordinary
`Cat`-bilimit predicate. This is an interoperability theorem, not a typeclass instance: either
predicate may be chosen as the downstream owner without creating instance-search loops. -/
theorem isBilimit_iff (P : CatCommSqOver F G X) :
    Resized.IsBilimit P ↔ P.IsBilimit := sorry

end Resized

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/- Data audit (mathlib 4.32): `Functor.asSmall`, `Functor.asSmallMap`,
`Functor.asSmallMapIso`, and `CatCommSqOver.resize` report only `propext`,
`Classical.choice`, and `Quot.sound`; none depends on `sorryAx`. -/
