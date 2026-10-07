module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
import StacksCheckRecall

/-!
# Situation 10.102.1

@stack 00MS
-/

@[expose] public section

/- Situation 10.102.1, tag `00MS`: a bounded finite free complex is now owned by
`FiniteFreeComplex`, whose chosen standard-coordinate models support matrix-minor constructions
without introducing a chapter-specific wrapper. -/
@[stacks 00MS "finite free complex"]
#check @_root_.FiniteFreeComplex
@[stacks 00MS "finite free term"]
#check @FiniteFreeComplex.term
@[stacks 00MS "finite free differential"]
#check @FiniteFreeComplex.diffAt
@[stacks 00MS "alternating rank"]
#check @FiniteFreeComplex.alternatingRank
