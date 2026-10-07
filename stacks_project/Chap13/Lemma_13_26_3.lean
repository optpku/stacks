module

import ReasLib.CategoryTheory.Filtration.FiniteInjective.Splitting
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.3

The splitting theorem is owned by the neutral finite filtered-injective API in ReasLib. Its
inductive proof through finite filtration stages is deliberately not exposed as chapter-local
infrastructure.
-/

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

/- Lemma 13.26.3 (`05TQ`): every strict monomorphism from a finite filtered-injective object
splits. -/
@[stacks 05TQ] #check @splitMono

end CategoryTheory.FilteredObject.Finite.FilteredInjective
