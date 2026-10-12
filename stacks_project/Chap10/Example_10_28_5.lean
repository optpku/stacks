/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.28.5

@stack 05KC
-/

/- Example 10.28.5 (Stacks, tag `05KC`): the family of principal ideals of a ring `R` is an Oka
family. In mathlib this is the canonical theorem `Ideal.isOka_isPrincipal`, proved in the slightly
stronger generality of commutative semirings. -/
@[stacks 05KC]
#check @Ideal.isOka_isPrincipal
