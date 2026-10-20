/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.CategoryTheory.Preadditive.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Category cohomology as a right-derived limit

For an additive presheaf on `C`, category cohomology is the ordinary right-derived functor of
`lim : (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat`.  The explicit composable-arrow model is kept in
`CategoryCohomology.Bar`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.CategoryCohomology

variable {C : Type u} [Category.{v} C]
variable [HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasInjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- Category cohomology is the right-derived functor of the limit of an additive presheaf. -/
@[stacks 08RZ "category cohomology as a right-derived limit"]
noncomputable abbrev cohomology (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    AddCommGrpCat.{w} :=
  ((lim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerived n).obj F

/-- The degree-`n` category-cohomology functor in the coefficient presheaf. -/
@[stacks 08RZ "derived category-cohomology coefficient functor"]
noncomputable abbrev cohomologyFunctor (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w} :=
  (lim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).rightDerived n

/-- Evaluation of the derived category-cohomology functor on a coefficient presheaf. -/
@[simp, stacks 08RZ "derived category-cohomology object formula"]
theorem cohomologyFunctor_obj (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (cohomologyFunctor (C := C) n).obj F = cohomology F n := sorry

/-- Derived category cohomology is additive in its coefficient presheaf. -/
@[stacks 08RZ "additivity of derived category cohomology"]
instance cohomologyFunctor.additive (n : ℕ) :
    (cohomologyFunctor (C := C) n).Additive := sorry

end CategoryTheory.CategoryCohomology
