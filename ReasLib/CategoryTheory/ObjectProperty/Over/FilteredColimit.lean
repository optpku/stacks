/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Over.Basic

/-!
# Filtered colimits from selected objects over a target

This leaf records the final-subcategory criterion that transfers a filtered
colimit presentation to a selected family of objects over a fixed target.  The
underlying diagram and cocone belong to `ObjectProperty.Over.Basic`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty.Over

variable {C : Type u} [Category.{v} C] {X : C}

/-- A full selected subcategory is final in a filtered ambient selected
subcategory when every ambient stage maps to a selected stage. -/
@[stacks 07C3 "final selected over-objects"]
theorem inclusion_final_of_factorization
    {P Q : ObjectProperty (CategoryTheory.Over X)}
    (hPQ : P ≤ Q) (hQfiltered : IsFiltered Q.FullSubcategory)
    (hfactor : ∀ A : Q.FullSubcategory,
      ∃ B : P.FullSubcategory, Nonempty (A.obj ⟶ B.obj)) :
    (ObjectProperty.ιOfLE hPQ).Final := sorry

/-- Under the same factorization hypothesis, the smaller selected
subcategory is filtered. -/
@[stacks 07C3 "filtered selected over-objects"]
theorem isFiltered_of_factorization
    {P Q : ObjectProperty (CategoryTheory.Over X)}
    (hPQ : P ≤ Q) (hQfiltered : IsFiltered Q.FullSubcategory)
    (hfactor : ∀ A : Q.FullSubcategory,
      ∃ B : P.FullSubcategory, Nonempty (A.obj ⟶ B.obj)) :
    IsFiltered P.FullSubcategory := sorry

/-- A filtered colimit presentation of `X` by `Q`-objects restricts to the
selected `P`-objects when every `Q`-object factors through one of them. -/
@[stacks 07C3 "filtered-colimit restriction over a target"]
theorem isFilteredColimit_of_factorization
    {P Q : ObjectProperty (CategoryTheory.Over X)}
    (hPQ : P ≤ Q) (hQfiltered : IsFiltered Q.FullSubcategory)
    (hQcolimit : Nonempty (IsColimit (forgetCocone Q)))
    (hfactor : ∀ A : Q.FullSubcategory,
      ∃ B : P.FullSubcategory, Nonempty (A.obj ⟶ B.obj)) :
    IsFiltered P.FullSubcategory ∧ Nonempty (IsColimit (forgetCocone P)) := sorry

end CategoryTheory.ObjectProperty.Over
