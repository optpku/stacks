/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated.Kernel
import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation]

/- Lemma 13.6.10 (1): the morphism property obtained from the kernel of localization at `S` is
the canonical saturation of `S`. -/
@[stacks 05RL] #check
  (MorphismProperty.Localization.kernel_trW_eq_saturation S :
    (Functor.kernel S.Q).trW = (MorphismProperty.saturation (C := D)) S)

/- Fixed-point form of part (1) for a saturated multiplicative system. -/
section

variable [S.IsSaturatedMultiplicativeSystem]

#check (MorphismProperty.Localization.kernel_trW_eq_self S)

end

variable (P : ObjectProperty D) [P.IsTriangulated]

/- Lemma 13.6.10 (2): the object property obtained from the Verdier quotient by `P` is the
retract closure of `P`, i.e. its canonical saturation under direct summands. -/
#check (ObjectProperty.VerdierQuotient.kernel_eq_retractClosure P)

/- Fixed-point form of part (2) for a retract-stable triangulated object property. -/
section

variable [P.IsStableUnderRetracts]

#check (ObjectProperty.VerdierQuotient.kernel_eq_self P)

end

end CategoryTheory
