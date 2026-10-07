module

import StacksCheckRecall
public import ReasLib.RingTheory.Flat.FaithfullyFlat.CountablyGenerated

@[expose] public section

/-!
Chapter 10, Lemma 10.95.2 is the faithfully flat descent direction of the reusable
countable-generation base-change criterion.

@stack 0GVD
-/

@[stacks 0GVD]
#check @Module.CountablyGenerated.of_baseChange

@[stacks 0GVD "base-change equivalence"]
#check @Module.CountablyGenerated.iff_baseChange
