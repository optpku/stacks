/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.IntervalSplit.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.2

The interval-presentation predicate packages integers `a ≤ b`, an injective family indexed by
`Set.Icc a b`, and an isomorphism to the canonical interval-split finite filtered object.  Its
canonical filtration has stage `F^p` equal to the tail biproduct on indices `n ≥ p`, so this is
precisely the formal version of the presentation in the source.
-/

namespace CategoryTheory.FilteredObject.IntervalSplit

/- Lemma 13.26.2 (`05TP`): a finite filtered object is filtered injective if and only if it has
an injective interval presentation. -/
@[stacks 05TP] #check @FilteredInjective.iff_hasPresentation

/- The canonical predicate owning the interval endpoints, injective summands, and filtered
isomorphism occurring in the statement. -/
#check @HasInjectivePresentation

/- Each filtration stage of the canonical model is injective when its interval components are
injective. -/
#check @Stage.injective

/- Componentwise injectivity equips the canonical interval-split object with filtered
injectivity. -/
#check @FilteredInjective.of_components

end CategoryTheory.FilteredObject.IntervalSplit
