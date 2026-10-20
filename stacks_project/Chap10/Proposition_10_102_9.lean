module

public import ReasLib.RingTheory.LocalRing.BuchsbaumEisenbud
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.102.9
@stack 00N1

The reusable Buchsbaum--Eisenbud owner supplies both the depth formulation and
the source-facing regular-sequence formulation.
-/

#check @FiniteFreeComplex.ExactInPositiveDegrees

@[stacks 00N1 "depth formulation"]
#check @FiniteFreeComplex.exactInPositiveDegrees_iff_rankMinorIdeal_depth

@[stacks 00N1 "source regular-sequence formulation"]
#check @FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud
