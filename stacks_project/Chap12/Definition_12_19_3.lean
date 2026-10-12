/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable {A B : FilteredObject C} (f : A ⟶ B)

/- Definition 12.19.3 [0123] (1): strictness is the stagewise compatibility of quotient
filtrations with the image filtration. -/
@[stacks 0123]
#check (Strict f : Prop)

/- Definition 12.19.3 [0123] (2): strictness is equivalently the canonical stagewise equality. -/
@[stacks 0123]
#check (strict_iff_quotient_eq_inf f :
  Strict f ↔ ∀ p : ℤ,
    A.filtration.quotient f.hom p = imageSubobject f.hom ⊓ B.filtration p)

end CategoryTheory.FilteredObject.Hom
