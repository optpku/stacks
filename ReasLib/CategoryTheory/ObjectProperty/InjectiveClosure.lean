/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small Abelian Subcategories with Enough Injectives

This leaf isolates the set-theoretic closure used to reduce constructions in a large abelian
category to a small weak-Serre full subcategory with enough injectives. The owner is an existence
theorem, not a typeclass assumption: having enough injectives in the ambient category is the
mathematical input from which the smaller subcategory is obtained.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.ObjectProperty.InjectiveClosure

variable {A : Type u} [_root_.CategoryTheory.Category.{v} A] [Abelian A]

/-- Any small object property in an abelian category with enough injectives is contained in a
small weak-Serre property whose full subcategory has enough injectives. -/
@[stacks 015R "small abelian subcategory with enough injectives"]
theorem ofProperty [EnoughInjectives A]
    (E : ObjectProperty A) [ObjectProperty.Small.{w} E] :
    ∃ P : ObjectProperty A,
      E ≤ P ∧ ObjectProperty.Small.{w} P ∧
        IsWeakSerreClass P ∧ EnoughInjectives P.FullSubcategory := sorry

/-- Remark 13.26.13 (`015R`): every set-indexed family in an abelian category with enough
injectives lies in a small weak-Serre full subcategory with enough injectives. -/
@[stacks 015R]
theorem ofFamily [EnoughInjectives A] {I : Type w} (X : I → A) :
    ∃ P : ObjectProperty A,
      (∀ i, P (X i)) ∧ ObjectProperty.Small.{w} P ∧
        IsWeakSerreClass P ∧ EnoughInjectives P.FullSubcategory := sorry

end CategoryTheory.ObjectProperty.InjectiveClosure
