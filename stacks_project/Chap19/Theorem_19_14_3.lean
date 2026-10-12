/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.GabrielPopescu
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.IsGrothendieckAbelian.GabrielPopescu

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/- Theorem 19.14.3 (1): the canonical Gabriel-Popescu left adjoint is exact. -/
@[stacks 0F5U] #check
  (tensorExact (separator C) (isSeparator_separator C) :
    exactFunctor (ModuleCat (End (separator C))ᵐᵒᵖ) C (tensorObj (separator C)))

/- Theorem 19.14.3 (2): the canonical tensor and coyoneda functors form an adjunction. -/
@[stacks 0F5U] #check
  (tensorObjPreadditiveCoyonedaObjAdjunction (separator C) :
    tensorObj (separator C) ⊣ preadditiveCoyonedaObj (separator C))

/- Theorem 19.14.3 (3): the canonical Gabriel-Popescu embedding is full. -/
@[stacks 0F5U] #check
  (coyonedaSeparatorFull (C := C) :
    (preadditiveCoyonedaObj (separator C)).Full)

/- Theorem 19.14.3 (4): the canonical Gabriel-Popescu embedding is faithful. -/
@[stacks 0F5U] #check
  (coyonedaSeparatorFaithful (C := C) :
    (preadditiveCoyonedaObj (separator C)).Faithful)

end CategoryTheory.IsGrothendieckAbelian.GabrielPopescu
