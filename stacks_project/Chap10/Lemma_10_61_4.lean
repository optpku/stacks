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
