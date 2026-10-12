/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction

/-!
# Fibred-inertia pseudofunctor projections

Owner-level compatibility of strict and ordinary fibred inertia with the canonical forgetful
pseudofunctor.  Local action formulas are owned by `map` and `map₂`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

/-- Forgetting fibred structure after applying strict fibred inertia agrees with first
forgetting to a based category and then applying based inertia. -/
@[simp, stacks 04Z4 "strict fibred-inertia forgetful pseudofunctor"]
theorem strictPseudofunctor.comp_toBased :
    (strictPseudofunctor C).comp
        (FiberedCategoryOver.toBased C :
          StrictPseudofunctor
            (FiberedCategoryOver.{u, v, max w vS, vS} C)
            (BasedCategory.{vS, max w vS} C)) =
      (FiberedCategoryOver.toBased C :
          StrictPseudofunctor
            (FiberedCategoryOver.{u, v, w, vS} C)
            (BasedCategory.{vS, w} C)).comp
        (BasedCategory.Inertia.strictPseudofunctor C) := sorry

/-- The ordinary fibred-inertia pseudofunctor sends an object to its absolute inertia. -/
@[simp, stacks 04Z4 "fibred-inertia pseudofunctor object computation"]
theorem pseudofunctor.obj
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    (pseudofunctor C).obj X = FiberedCategoryOver.inertia X := sorry

/-- Ordinary fibred inertia satisfies the same compatibility with forgetting to based
categories. -/
@[simp, stacks 04Z4 "fibred-inertia pseudofunctor forgetful comparison"]
theorem pseudofunctor.comp_toBased :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.toBased C :
          StrictPseudofunctor
            (FiberedCategoryOver.{u, v, max w vS, vS} C)
            (BasedCategory.{vS, max w vS} C)).toPseudofunctor) =
      ((FiberedCategoryOver.toBased C :
          StrictPseudofunctor
            (FiberedCategoryOver.{u, v, w, vS} C)
            (BasedCategory.{vS, w} C)).toPseudofunctor).comp
        (BasedCategory.Inertia.pseudofunctor C) := sorry

end FiberedCategoryOver.Inertia

end CategoryTheory
