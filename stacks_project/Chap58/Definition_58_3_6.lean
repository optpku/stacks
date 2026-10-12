/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Galois.SetValued
import StacksCheckRecall

@[expose] public section

universe vC uC w

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable (F : C ⥤ Type w)

/- Definition 58.3.6 -/
@[stacks 0BMY] #check (CategoryTheory.Functor.IsGalois F : Prop)

end CategoryTheory
