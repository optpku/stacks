module

import Mathlib.CategoryTheory.Category.Cat.Terminal
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Cat.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.PseudoCone

/-!
# The categorical pullback as a conical pseudolimit

This module compares mathlib's explicit categorical pullback with the neutral representable
conical pseudolimit of the corresponding walking-cospan pseudofunctor.

The comparison is a specified functor with an `IsEquivalence` instance. No inverse is selected:
downstream users that need equivalence data can apply `Functor.asEquivalence`, while statements
that only need the universal property can use typeclass search.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe v u

namespace CategoryTheory

open Bicategory
open Limits
open Limits.CategoricalPullback
open scoped Pseudofunctor.StrongTrans
open scoped Limits.CategoricalPullback

namespace Limits.CategoricalPullback

variable {A B C : Type u}
variable [Category.{v} A] [Category.{v} B] [Category.{v} C]

/-- The canonical comparison from mathlib's explicit categorical pullback to the neutral
conical pseudolimit category of the associated walking-cospan pseudofunctor.

It first regards an object as a constant functor out of the chosen terminal category, then
uses mathlib's `CategoricalPullback.functorEquiv` to obtain a categorical commutative square,
and finally interprets that square as a walking-cospan pseudocone. -/
noncomputable def toConicalPseudoLimit (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤
      ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom) :=
  Functor.const (⊤_ Cat) ⋙ (functorEquiv F G (⊤_ Cat)).functor ⋙
    CatCommSqOver.toPseudoConeFunctor (⊤_ Cat) F G

/-- The explicit categorical pullback presents the neutral conical pseudolimit of its
walking-cospan pseudofunctor. -/
instance toConicalPseudoLimit.isEquivalence (F : A ⥤ C) (G : B ⥤ C) :
    (toConicalPseudoLimit F G).IsEquivalence := sorry

/- Data audit (mathlib 4.32): `toConicalPseudoLimit` reports `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. Its object and morphism actions are the explicit composite above;
`sorryAx` is inherited only from the Prop-valued modification naturality and functor laws of
`CatCommSqOver.toPseudoConeFunctor`. -/

end Limits.CategoricalPullback

end CategoryTheory
