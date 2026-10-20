/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.Quotient
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Presentations of categories cofibered in groupoids

A presentation by a groupoid in functors is an equivalence from its quotient
to the given category cofibered in groupoids, over the common base category.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory BasedFunctor

universe u v w

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.GroupoidInFunctors

/-- A morphism from the quotient of `G` to a category cofibered in groupoids `F` is
a presentation if its associated based functor is an equivalence over the base. -/
abbrev IsPresentation (G : GroupoidInFunctors.{u, v, w} C)
    (F : CofiberedCategoryOver.Groupoids C)
    (φ : G.quotient ⟶ F) : Prop :=
  BasedFunctor.IsEquivalence (CofiberedCategoryOver.Groupoids.toBasedFunctor φ)

end CategoryTheory.GroupoidInFunctors
