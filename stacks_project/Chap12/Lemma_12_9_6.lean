/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.JordanHolder
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (A : C)

/- Lemma 12.9.6 [0FCJ]: an object is Artinian and Noetherian iff it admits a composition series
from the zero subobject to the whole object.  The reusable formalization factors this through the
canonical finite-length object property. -/
@[stacks 0FCJ]
#check isFiniteLengthObject_iff A

@[stacks 0FCJ]
#check isFiniteLengthObject_iff_existsCompositionSeries A

section FiniteLength

variable [IsFiniteLengthObject A]

#check existsCompositionSeries A

end FiniteLength

#check (inferInstance : JordanHolderLattice (Subobject A))

end CategoryTheory
