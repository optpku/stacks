/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction

/-!
# Setoid-fibred inertia pseudofunctor projections

Owner-level compatibility of strict and ordinary setoid-fibred inertia with the canonical
forgetful pseudofunctor.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.FiberedCategoryOver.Setoids.Inertia

variable {C : Type u} [Category.{v} C]

/-- Forgetting strict setoid-fibred inertia to based categories recovers neutral based inertia
after forgetting the input. -/
@[simp]
theorem strictPseudofunctor.comp_toBased :
    (strictPseudofunctor C).comp
        (FiberedCategoryOver.Setoids.toBased C) =
      (FiberedCategoryOver.Setoids.toBased C).comp
        (BasedCategory.Inertia.strictPseudofunctor C) := sorry

/-- Strict setoid-fibred inertia is compatible with forgetting directly to general fibred
categories. -/
@[stacks 04Z4 "strict inertia projection to fibred categories", simp]
theorem strictPseudofunctor.comp_toFibered :
    (strictPseudofunctor C).comp
        (FiberedCategoryOver.Setoids.toFibered C) =
      (FiberedCategoryOver.Setoids.toFibered C).comp
        (FiberedCategoryOver.Inertia.strictPseudofunctor C) := sorry

/-- The ordinary setoid-fibred inertia pseudofunctor sends an object to its absolute inertia. -/
@[simp]
theorem pseudofunctor.obj
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    (pseudofunctor C).obj X =
      FiberedCategoryOver.Setoids.inertia X := sorry

/-- Forgetting ordinary setoid-fibred inertia to based categories recovers neutral based
inertia after forgetting the input. -/
@[simp]
theorem pseudofunctor.comp_toBased :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.Setoids.toBased C).toPseudofunctor) =
      ((FiberedCategoryOver.Setoids.toBased C).toPseudofunctor).comp
        (BasedCategory.Inertia.pseudofunctor C) := sorry

/-- Ordinary setoid-fibred inertia is compatible with forgetting directly to general fibred
categories. -/
@[stacks 04Z4 "inertia projection to fibred categories", simp]
theorem pseudofunctor.comp_toFibered :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.Setoids.toFibered C).toPseudofunctor) =
      ((FiberedCategoryOver.Setoids.toFibered C).toPseudofunctor).comp
        (FiberedCategoryOver.Inertia.pseudofunctor C) := sorry

end CategoryTheory.FiberedCategoryOver.Setoids.Inertia
