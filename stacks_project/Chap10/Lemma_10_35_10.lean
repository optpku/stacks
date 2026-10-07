module

public import ReasLib.Algebra.Module.End.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.35.10

For a nonzero vector space whose dimension is smaller than the cardinality of
its base field, every endomorphism has a monic polynomial evaluation which is
not invertible.

@stack 00FT
-/

-- Lemma 10.35.10: the cardinality obstruction for polynomial evaluations of
-- a vector-space endomorphism.
@[stacks 00FT]
#check @Module.End.exists_monic_aeval_not_isUnit_of_rank_lt_cardinal
