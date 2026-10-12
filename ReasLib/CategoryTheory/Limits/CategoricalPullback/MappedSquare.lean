/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Square

/-!
# Mapping squares to categorical pullback cones

A category-valued pseudofunctor sends an ordinary commutative square to a
categorical commutative square over the images of its lower edges.
-/

@[expose] public section

open CategoryTheory.Limits.CategoricalPullback

universe uC vC uF vF

namespace CategoryTheory.Pseudofunctor

/-- The categorical commutative square obtained by applying a category-valued
pseudofunctor to a commutative square in a locally discrete bicategory. -/
def mapCommSqOver {C : Type uC} [Category.{vC} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{vF, uF}) (sq : Square C) :
    CatCommSqOver (F.map sq.f₂₄.toLoc).toFunctor
      (F.map sq.f₃₄.toLoc).toFunctor (F.obj (LocallyDiscrete.mk sq.X₁)) where
  fst := (F.map sq.f₁₂.toLoc).toFunctor
  snd := (F.map sq.f₁₃.toLoc).toFunctor
  iso := Cat.Hom.toNatIso (F.isoMapOfCommSq sq.commSq.toLoc)

end CategoryTheory.Pseudofunctor
