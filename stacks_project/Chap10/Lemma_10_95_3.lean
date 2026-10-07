module

import StacksCheckRecall
public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective.CountablyGenerated

@[expose] public section

/-!
Chapter 10, Lemma 10.95.3 is faithfully flat descent for the canonical predicate of a countably
generated projective module. Its two components remain independently accessible.

@stack 05A6
-/

@[stacks 05A6]
#check Module.CountablyGeneratedProjective.of_baseChange

@[stacks 05A6 "countably generated projective equivalence"]
#check @Module.CountablyGeneratedProjective.iff_baseChange

@[stacks 05A6 "countable-generation projection"]
#check @Module.CountablyGeneratedProjective.countablyGenerated

@[stacks 05A6 "projective projection"]
#check @Module.CountablyGeneratedProjective.projective

@[stacks 05A6 "countable-generation base-change projection"]
#check @Module.CountablyGenerated.of_baseChange
