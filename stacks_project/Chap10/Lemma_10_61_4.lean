/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.Noetherian
import StacksCheckRecall

/-!
# Noetherian Jacobson rings

@stack 00KX
-/

@[expose] public section

@[stacks 00KX "(1), one-dimensional domain criterion"]
#check @IsJacobsonRing.of_ringKrullDim_eq_one_of_infinite

@[stacks 00KX "(2), prime-over criterion"]
#check @IsJacobsonRing.of_prime_isMaximal_or_infinite_primesOver
