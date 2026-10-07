module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
public import ReasLib.RingTheory.AdicCompletion.Principal.Regular

import Mathlib.Tactic.CrossRefAttribute

/-!
# Beauville-Laszlo glueing along a regular element

The principal-adic completion of a ring and localization away from a nonzerodivisor form a
Beauville-Laszlo glueing pair.

@stack 0BNS
-/

@[expose] public section

universe u

open scoped nonZeroDivisors

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R : Type u} [CommRing R]

/-- Remark 15.91.7: a nonzerodivisor and its principal-adic completion form a
Beauville-Laszlo glueing pair. -/
@[stacks 0BNS, stacks 0BP8 "Remark 15.91.7"]
theorem principalAdicCompletion_isGlueingPair_of_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f := sorry

end LocalizedModule.Away.BeauvilleLaszlo
