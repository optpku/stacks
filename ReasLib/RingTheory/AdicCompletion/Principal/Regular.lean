module

public import ReasLib.RingTheory.Ideal.Principal

import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular elements in principal-adic completions

A regular element remains regular in its principal-adic completion.

@stack 0BNS
-/

@[expose] public section

universe u

open scoped nonZeroDivisors

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- The image of a nonzerodivisor in its principal-adic completion is a nonzerodivisor. -/
@[stacks 0BNS "a nonzerodivisor remains regular in the principal-adic completion"]
theorem principalAdicCompletion_algebraMap_mem_nonZeroDivisors
    (f : R) (hf : f ∈ nonZeroDivisors R) :
    algebraMap R (principalAdicCompletion f) f ∈
      nonZeroDivisors (principalAdicCompletion f) := sorry

end AdicCompletion
