/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension
import StacksCheckRecall

@[expose] public section

/-!
# Equation 13.26.13.4

The reusable owner is an extension object consisting of the additive filtered functor and its
associated-graded and forgetful comparisons. Keeping both comparisons as natural isomorphisms
avoids imposing a definitionally strict split presentation on downstream constructions.
-/

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

/- Equation 13.26.13.4 (`05U0`): an additive functor admits an additive extension from finite
filtered-injective objects to finite filtered objects. -/
@[stacks 05U0] #check @Extension.nonempty

/- The extension owns the filtered functor used in the subsequent homotopy construction. -/
#check @Extension.functor

/- The extension commutes naturally with every associated-graded piece. -/
#check @Extension.gradedIso

/- Its forgetful comparison records that the extension recovers the original functor. -/
#check @Extension.forgetIso

/- A left exact functor has the canonical extension obtained by mapping finite filtrations. -/
#check @Extension.ofLeftExact

/- The canonical left-exact extension uses the neutral graded-piece comparison. -/
#check @Extension.ofLeftExact_gradedIso

end CategoryTheory.FilteredObject.Finite.FilteredInjective
