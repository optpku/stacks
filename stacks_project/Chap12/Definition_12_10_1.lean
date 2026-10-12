/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A)

/- Definition 12.10.1 (1) [02MO]: Serre subcategories are modeled by the canonical mathlib
object-property class; Lemma 12.10.2 supplies its exact-sequence characterization. -/
@[stacks 02MO "(1)"]
#check (P.IsSerreClass : Prop)

/- Definition 12.10.1 (2) [02MO]: a weak Serre subcategory uses the source-faithful
four-out-of-five exactness predicate. -/
@[stacks 02MO "(2)"]
#check (P.IsWeakSerreClass : Prop)

#check @IsWeakSerreClass.ofClosure

#check @IsWeakSerreClass.ofIsSerreClass

end Abelian

end CategoryTheory.ObjectProperty
