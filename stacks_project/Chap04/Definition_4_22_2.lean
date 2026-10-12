/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram
public import Mathlib.CategoryTheory.Filtered.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe uI vI uC vC

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

section Filtered

variable [IsFiltered I]
variable (F : I ⥤ C)

/- Definition 4.22.2 (1): a directed system is essentially constant when it admits an essentially
constant cocone. -/
@[stacks 05PV "essentially constant directed systems"]
#check (IsFiltered.IsEssentiallyConstant F : Prop)

end Filtered

section Cofiltered

variable [IsCofiltered I]
variable (F : I ⥤ C)

/- Definition 4.22.2 (2): a directed inverse system is essentially constant when it admits an
essentially constant cone. -/
@[stacks 05PV "essentially constant directed inverse systems"]
#check (IsCofiltered.IsEssentiallyConstant F : Prop)

end Cofiltered

end CategoryTheory
