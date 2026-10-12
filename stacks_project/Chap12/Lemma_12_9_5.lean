/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.FiniteLength
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/- Lemma 12.9.5: in a short exact sequence the middle object is Noetherian iff the two outer
objects are Noetherian. -/
@[stacks 0FCI]
#check ShortComplex.isNoetherianObject_iff_of_shortExact (S := S)

/- The reusable owner is the Serre-class structure on Noetherian objects. -/
#check (inferInstance : (isNoetherianObject : ObjectProperty C).IsSerreClass)

end CategoryTheory
