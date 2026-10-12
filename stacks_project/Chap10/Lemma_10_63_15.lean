/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
import StacksCheckRecall

@[expose] public section

open IsLocalRing

/-!
Lemma 10.63.15 (Stacks 0310): exact association at a prime ascends to the maximal ideal after
localization, and descends when the prime is finitely generated.

@stack 0310
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {p : Ideal R} [p.IsPrime]

@[stacks 0310 "(1)"] #check
  (associatedPrimesOfModule.Localization.maximalIdeal_mem_atPrime (R := R) (M := M) :
    p ∈ associatedPrimesOfModule R M →
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M))

@[stacks 0310 "(2)"] #check
  (associatedPrimesOfModule.Localization.mem_of_maximalIdeal_mem_atPrime
      (R := R) (M := M) :
    maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) →
      p.FG → p ∈ associatedPrimesOfModule R M)

#check @associatedPrimesOfModule.Localization.mem_iff_maximalIdeal_mem_atPrime

end
