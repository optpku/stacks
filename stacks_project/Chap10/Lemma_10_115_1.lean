module

public import ReasLib.Data.Finsupp.Weight
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.115.1

@stack 051M

The owner theorem works for every finite linearly ordered coordinate type and
does not require the ambient finite set to be nonempty. The source's `Fin n`
case is therefore recalled directly.
-/

@[stacks 051M "tail-dominating weights distinguish multi-indices"]
#check @Finsupp.weight_eq_iff_eq_of_tailDominates

#check @Finsupp.coordinateSpread
#check @Finsupp.pairSpread
#check @Finsupp.tailDominates
#check @Finsupp.exists_tail_dominating_weights
