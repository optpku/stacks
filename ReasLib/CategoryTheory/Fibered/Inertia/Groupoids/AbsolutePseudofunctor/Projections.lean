module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction

/-!
# Groupoid-fibred inertia pseudofunctor projections

Owner-level compatibility of strict and ordinary groupoid-fibred inertia with the canonical
forgetful pseudofunctors.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Inertia

variable {C : Type u} [Category.{v} C]

/-- Forgetting strict groupoid-fibred inertia to based categories recovers neutral based
inertia after forgetting the input. -/
@[simp]
theorem strictPseudofunctor.comp_toBased :
    (strictPseudofunctor C).comp
        (FiberedCategoryOver.Groupoids.toBased C) =
      (FiberedCategoryOver.Groupoids.toBased C).comp
        (BasedCategory.Inertia.strictPseudofunctor C) := sorry

/-- Strict groupoid-fibred inertia is compatible with forgetting to general fibred
categories. -/
@[simp]
theorem strictPseudofunctor.comp_toFibered :
    (strictPseudofunctor C).comp
        (FiberedCategoryOver.Groupoids.toFibered C) =
      (FiberedCategoryOver.Groupoids.toFibered C).comp
        (FiberedCategoryOver.Inertia.strictPseudofunctor C) := sorry

/-- The ordinary groupoid-fibred inertia pseudofunctor sends an object to its absolute
inertia. -/
@[simp]
theorem pseudofunctor.obj
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    (pseudofunctor C).obj X =
      FiberedCategoryOver.Groupoids.inertia X := sorry

/-- Forgetting ordinary groupoid-fibred inertia to based categories recovers neutral based
inertia after forgetting the input. -/
@[simp]
theorem pseudofunctor.comp_toBased :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.Groupoids.toBased C).toPseudofunctor) =
      ((FiberedCategoryOver.Groupoids.toBased C).toPseudofunctor).comp
        (BasedCategory.Inertia.pseudofunctor C) := sorry

/-- Ordinary groupoid-fibred inertia is compatible with forgetting to general fibred
categories. -/
@[simp]
theorem pseudofunctor.comp_toFibered :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.Groupoids.toFibered C).toPseudofunctor) =
      ((FiberedCategoryOver.Groupoids.toFibered C).toPseudofunctor).comp
        (FiberedCategoryOver.Inertia.pseudofunctor C) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Inertia
