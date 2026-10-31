/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.MapProperties

/-!
# Properties of common-base postcomposition

This leaf contains the typeclass consequences of `CategoricalPullback.postcompose`.  Keeping these
bridges separate from the ordinary construction lets consumers import only the data owners when
they do not need equivalence properties.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace postcompose

/-- Postcomposition of both cospan legs is faithful, independently of the common-base functor. -/
instance faithful (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (postcompose F G H).Faithful := sorry

/-- Postcomposition is full when the common-base functor is faithful. -/
instance full (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) [H.Faithful] :
    (postcompose F G H).Full := sorry

/-- Postcomposition is essentially surjective when the common-base functor is fully faithful. -/
instance essSurj (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) [H.Full] [H.Faithful] :
    (postcompose F G H).EssSurj := sorry

/-- Postcomposition is an equivalence when the common-base functor is fully faithful. -/
instance isEquivalence (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) [H.Full] [H.Faithful] :
    (postcompose F G H).IsEquivalence := sorry

end postcompose

end CategoryTheory.Limits.CategoricalPullback
