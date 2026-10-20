/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.ShiftedFamily
import StacksCheckRecall

@[expose] public section

/-!
# Products of Shifted Modules

The canonical comparison and its Grothendieck `AB4*` generalization are owned by ReasLib.  This
file records the module-category specialization from the source.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable (R : Type u) [Ring R]

/- Remark 19.13.5 (1): for `R`-modules `M n`, the canonical map from `⨁ M n[-n]` to
`∏ M n[-n]` is an isomorphism in `D(R)`. -/
@[stacks 07DA] #check fun (M : ℤ → ModuleCat.{u} R) ↦
  (DerivedCategory.ShiftedFamily.comparison_isIso M :
    IsIso (DerivedCategory.ShiftedFamily.comparison M))

/- Remark 19.13.5 (2): the same comparison is invertible in the derived category of any
Grothendieck abelian category with exact countable products. -/
@[stacks 07DA] #check
  fun (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
      [IsGrothendieckAbelian.{v} A] [CountableAB4Star A]
      (M : ℤ → A) ↦
    (DerivedCategory.ShiftedFamily.comparison_isIso M :
      IsIso (DerivedCategory.ShiftedFamily.comparison M))

end CategoryTheory
