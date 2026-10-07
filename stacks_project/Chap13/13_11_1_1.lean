module

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksCheckRecall

@[expose] public section

/- 13.11.1.1 (`05RS`): for a distinguished triangle, the five-term cohomology segment
`H i X ⟶ H i Y ⟶ H i Z ⟶ H (i + 1) X ⟶ H (i + 1) Y` is the final truncation of
the canonical exact homology sequence.  The reusable owners are the general homological-functor
theorem and exactness under `ComposableArrows.δlast`; no derived-category specialization is
needed. -/
@[stacks 05RS] #check @DerivedCategory.homologyFunctor
@[stacks 05RS] #check @CategoryTheory.Functor.homologySequenceComposableArrows₅_exact
@[stacks 05RS] #check @CategoryTheory.ComposableArrows.Exact.δlast
