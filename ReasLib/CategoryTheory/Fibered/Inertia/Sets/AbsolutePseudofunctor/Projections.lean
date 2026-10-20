module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Projections
public import ReasLib.CategoryTheory.Fibered.Setoids.FromSets

/-!
# Set-fibred inertia pseudofunctor projections

Compatibility with forgetting to based categories and to the essentially discrete setoid owner.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]

/-- Forgetting strict set-fibred inertia to based categories recovers neutral based inertia. -/
@[simp]
theorem strictPseudofunctor.comp_toBased :
    (strictPseudofunctor C).comp (FiberedCategoryOver.Sets.toBased C) =
      (FiberedCategoryOver.Sets.toBased C).comp
        (BasedCategory.Inertia.strictPseudofunctor C) := sorry

/-- Forgetting strict set-fibred inertia to setoid fibres agrees with applying setoid-fibred
inertia after forgetting the input. -/
@[simp]
theorem strictPseudofunctor.comp_toSetoids :
    (strictPseudofunctor C).comp (FiberedCategoryOver.Sets.toSetoids C) =
      (FiberedCategoryOver.Sets.toSetoids C).comp
        (FiberedCategoryOver.Setoids.Inertia.strictPseudofunctor C) := sorry

/-- Forgetting ordinary set-fibred inertia to based categories recovers neutral based inertia. -/
@[simp]
theorem pseudofunctor.comp_toBased :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.Sets.toBased C).toPseudofunctor) =
      ((FiberedCategoryOver.Sets.toBased C).toPseudofunctor).comp
        (BasedCategory.Inertia.pseudofunctor C) := sorry

/-- Forgetting ordinary set-fibred inertia to setoid fibres agrees with applying setoid-fibred
inertia after forgetting the input. -/
@[simp]
theorem pseudofunctor.comp_toSetoids :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.Sets.toSetoids C).toPseudofunctor) =
      ((FiberedCategoryOver.Sets.toSetoids C).toPseudofunctor).comp
        (FiberedCategoryOver.Setoids.Inertia.pseudofunctor C) := sorry

end CategoryTheory.FiberedCategoryOver.Sets.Inertia
