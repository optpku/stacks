/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Locus
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.129.4

@stack 00RC
-/

/- Theorem 10.129.4, tag `00RC`, is a canonical recall: the flatness locus is the neutral
owner `Module.flatOverBaseLocus`, and its finite-presentation openness theorem is
`Module.isOpen_flatOverBaseLocus_of_finitePresentation`. -/
@[stacks 00RC "flatness locus owner"]
#check @Module.flatOverBaseLocus
@[stacks 00RC "flatness locus membership"]
#check @Module.mem_flatOverBaseLocus
@[stacks 00RC "relative flatness locus membership"]
#check @Module.mem_flatOverBaseLocus_iff_flatAtPrimeOver
@[stacks 00RC "basic-open flatness locus"]
#check @Module.basicOpen_subset_flatOverBaseLocus_of_flat_away
@[stacks 00RC "flatness locus openness"]
#check @Module.isOpen_flatOverBaseLocus_of_finitePresentation
