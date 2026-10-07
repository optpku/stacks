module

public import ReasLib.RingTheory.Ideal.Oka.SpanRank
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.28.6

@stack 05KD

The canonical owners are `Ideal.IsOka`, `Submodule.spanRank`, and the ReasLib
infinite-cardinal specialization `Ideal.isOka_spanRank_le`.
-/

@[stacks 05KD "Oka-family owner"]
#check @Ideal.IsOka

@[stacks 05KD "generator-cardinality owner"]
#check @Submodule.spanRank

@[stacks 05KD "infinite-cardinal specialization"]
#check @Ideal.isOka_spanRank_le
