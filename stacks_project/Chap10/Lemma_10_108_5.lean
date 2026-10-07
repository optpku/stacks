module

public import ReasLib.RingTheory.Ideal.Pure.Topology
import StacksCheckRecall

/-!
# Finitely generated pure ideals

@stack 05KK
-/

@[expose] public section

@[stacks 05KK "source four-clause form"]
#check @Ideal.Pure.fg_tfae

@[stacks 05KK "pure finite ideal / idempotent bridge"]
#check @Ideal.exists_idempotent_generator_of_pure_fg

@[stacks 05KK "pure ideal / open zero-locus bridge"]
#check @Ideal.Pure.exists_idempotent_generator_of_isOpen_zeroLocus

@[stacks 05KK "projective quotient bridge"]
#check @Ideal.Pure.iff_projective_quotient
