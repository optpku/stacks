/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
import StacksCheckRecall

/-!
# Lemma 10.63.17

@stack 05C0
-/

@[expose] public section

/- Lemma 10.63.17 (Stacks 05C0): localization by elements acting regularly on a module does not
change its exact associated primes when the localized module is viewed over the base ring. -/

universe u v

section


variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

@[stacks 05C0] #check
  (associatedPrimesOfModule.Localization.eq_of_isSMulRegular (M := M) S :
    (∀ s : S, IsSMulRegular M s) →
      associatedPrimesOfModule R M =
        associatedPrimesOfModule R (LocalizedModule S M))

@[stacks 05C0 "pointwise exact-association companion"]
#check @associatedPrimesOfModule.Localization.mem_iff_of_isSMulRegular
@[stacks 05C0 "ideal-membership companion"]
#check @Ideal.IsAssociatedToModule.Localization.iff_of_isSMulRegular
@[stacks 05C0 "associated-prime set companion"]
#check @associatedPrimes.Localization.eq_of_isSMulRegular

end
