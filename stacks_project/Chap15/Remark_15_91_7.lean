/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Regular

import StacksCheckRecall

/-!
# Principal-adic glueing along a nonzerodivisor

The reusable regularity and glueing-pair statements are owned by
`ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Regular`.

@stack 0BNS
-/

universe u

open scoped nonZeroDivisors

section

variable {R : Type u} [CommRing R] (f : R) (hf : f ∈ nonZeroDivisors R)

-- The image of `f` remains a nonzerodivisor in the `(f)`-adic completion.
@[stacks 0BNS "regularity in the principal-adic completion"]
#check
  (AdicCompletion.principalAdicCompletion_algebraMap_mem_nonZeroDivisors f hf :
    algebraMap R (principalAdicCompletion f) f ∈
      nonZeroDivisors (principalAdicCompletion f))

-- Remark 15.91.7: consequently, the completion and localization form a glueing pair.
@[stacks 0BNS "Remark 15.91.7"]
#check
  (LocalizedModule.Away.BeauvilleLaszlo.principalAdicCompletion_isGlueingPair_of_mem_nonZeroDivisors
      f hf :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f)

end
