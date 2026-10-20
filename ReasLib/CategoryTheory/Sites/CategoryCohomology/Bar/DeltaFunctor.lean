module

public import ReasLib.CategoryTheory.Sites.CategoryCohomology.Bar
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Effaceable
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.ExactComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# The category-cohomology bar delta functor

The exact bar complex defines a cohomological delta functor in the coefficient presheaf.  Positive
degrees are effaceable, so this delta functor has the universal property used to compare it with
ordinary right-derived limits.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.CategoryCohomology.Bar

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{max u v, w}]

/-- The cohomological delta functor attached to the exact category-cohomology bar complex. -/
@[stacks 08RZ "category-cohomology bar delta functor"]
noncomputable def deltaFunctor :
    CohomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w} :=
  CohomologicalDeltaFunctor.ExactComplex.functorBundled
    (complexExactFunctor (C := C))

/-- The degree branches of the bar delta functor are its bar-cohomology functors. -/
@[simp, stacks 08RZ "category-cohomology bar delta-functor degree"]
theorem deltaFunctor_obj (n : ℕ) :
    ((deltaFunctor (C := C)).F n).obj = cohomologyFunctor (C := C) n := sorry

/-- Objectwise evaluation of the bar delta functor is the cohomology of the explicit bar
complex. -/
@[simp, stacks 08RZ "category-cohomology bar delta-functor object"]
theorem deltaFunctor_obj_obj (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    ((deltaFunctor (C := C)).F n).obj.obj F = cohomology F n := sorry

/-- Every positive category-cohomology bar functor is effaceable. -/
@[stacks 08RZ "effaceability of positive category-cohomology bar functors"]
theorem cohomologyFunctor_isEffaceable (n : ℕ) (hn : 0 < n) :
    (cohomologyFunctor (C := C) n).IsEffaceable := sorry

/-- The category-cohomology bar delta functor is universal. -/
@[stacks 08RZ "universality of the category-cohomology bar delta functor"]
instance deltaFunctor.isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (deltaFunctor (C := C)) := sorry

end CategoryTheory.CategoryCohomology.Bar
