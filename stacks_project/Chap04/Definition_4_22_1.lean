/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Presentation
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace Limits

universe uI vI uC vC

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

section Filtered

variable [IsFiltered I]
variable {M : I ⥤ C} (c : Cocone M)

/- Definition 4.22.1 (1): a filtered cocone is essentially constant when one leg is split epi
and the remaining legs eventually factor through its section. -/
@[stacks 05PU "filtered cocone: split leg and eventual factorization"]
#check (c.IsEssentiallyConstant : Prop)

end Filtered

section Cofiltered

variable [IsCofiltered I]
variable {M : I ⥤ C} (d : Cone M)

/- Definition 4.22.1 (2): dually, a cofiltered cone is essentially constant when one leg is split
mono and the remaining legs eventually factor through its retraction. -/
@[stacks 05PU "cofiltered cone: split leg and eventual factorization"]
#check (d.IsEssentiallyConstant : Prop)

end Cofiltered

end Limits
end CategoryTheory
