/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.SmallSubcategory.EnoughInjectives
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small Abelian Subcategories with Enough Injectives

This leaf exposes the small abelian subcategory construction for reducing constructions in a
large abelian category with enough injectives. The selected full subcategory has exact inclusion
and preserves and reflects injectivity. It need not contain every ambient isomorphic copy of its
objects: imposing that condition would in general destroy smallness. Its object universe also
accommodates the ambient Hom types.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.ObjectProperty.InjectiveClosure

variable {A : Type u} [_root_.CategoryTheory.Category.{v} A] [Abelian A]

/-- Any small object property in an abelian category with enough injectives is contained in a
small abelian full subcategory with exact inclusion, enough injectives, and the same injective
objects as the ambient category. -/
@[stacks 015R "small abelian subcategory with enough injectives"]
theorem ofProperty [EnoughInjectives A]
    (E : ObjectProperty A) [ObjectProperty.Small.{w} E] :
    ∃ B : SmallAbelianSubcategory.{max v w, v, u} A,
      B.Contains E ∧ EnoughInjectives B.FullSubcategory ∧
        ∀ Y : B.FullSubcategory, Injective Y ↔ Injective Y.obj := by
  exact SmallAbelianSubcategory.exists_containing_enoughInjectives E

/-- Remark 13.26.13 (`015R`): every set-indexed family in an abelian category with enough
injectives lies in a small abelian full subcategory with exact inclusion, enough injectives, and
the same injective objects as the ambient category. -/
@[stacks 015R]
theorem ofFamily [EnoughInjectives A] {I : Type w} (X : I → A) :
    ∃ B : SmallAbelianSubcategory.{max v w, v, u} A,
      (∀ i, B.carrier (X i)) ∧ EnoughInjectives B.FullSubcategory ∧
        ∀ Y : B.FullSubcategory, Injective Y ↔ Injective Y.obj := by
  exact SmallAbelianSubcategory.exists_containingFamily_enoughInjectives X

end CategoryTheory.ObjectProperty.InjectiveClosure
