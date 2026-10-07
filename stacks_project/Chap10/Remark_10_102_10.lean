module

public import ReasLib.RingTheory.LocalRing.BuchsbaumEisenbud.Threshold
import StacksCheckRecall

/-!
# Threshold for unit rank-minor ideals

@stack 0GLM
-/

@[expose] public section

/- Remark 10.102.10: if a bounded finite free complex satisfies the equivalent conditions of
Proposition 10.102.9, then its unit rank-minor ideals form a terminal interval. In the displayed
zero-based differential indexing, the cutoff `j` corresponds to the source cutoff shifted by
one. -/
@[stacks 0GLM]
#check @FiniteFreeComplex.rankMinorIdeal_eq_top_iff_ge_threshold

#check @FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud
