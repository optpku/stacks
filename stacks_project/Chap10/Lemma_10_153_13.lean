module

public import ReasLib.Algebra.Module.DirectSumDevissage.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.153.13

@stack 05D6

The chapter item is a direct recall of the neutral module owner.  The
source-facing Henselian statement is preserved by the tagged `of_henselian`
theorem in `ReasLib`; the internal-direct-sum packaging is exposed there
through `iff_internal`.  The former chapter file contained only recursive
choice/projection proof scaffolding and therefore did not provide a reusable
mathematical owner.
-/

/- Lemma 10.153.13 (tag `05D6`): a countably generated Mittag-Leffler module
over a Henselian local ring is an internal direct sum of finitely presented
submodules. -/
@[stacks 05D6]
#check @Module.IsDirectSumOfFinitePresentation.of_henselian

#check @Module.IsDirectSumOfFinitePresentation
#check @Module.IsDirectSumOfFinitePresentation.iff_internal
#check @Module.IsDirectSumOfFinitePresentation.HasComplementSummand
#check @Module.IsDirectSumOfFinitePresentation.of_hasComplementSummand
#check @Module.IsDirectSumOfFinitePresentation.hasComplementSummand_of_henselian
