/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Local
public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquality

/-!
# Local properties of local-equality quotient morphisms

This leaf contains site-local properties of the quotient morphism.  It is kept
separate from `CategoryOver.LocalEquality` so constructing the quotient only
depends on fibred-category and quotient-category infrastructure.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.LocalEquality.QuotientTotal

/-- The canonical morphism to the local-equality quotient is locally essentially surjective on
objects because the quotient does not introduce new total-category objects. -/
theorem toFiberedCategory.locallyEssentiallySurjective
    (J : GrothendieckTopology C) (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.Hom.LocallyEssentiallySurjective J
      (toFiberedCategory J X) := sorry

end FiberedCategoryOver.LocalEquality.QuotientTotal

end CategoryTheory
