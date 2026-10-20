module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Horseshoe
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.18.9 (013T)

The injective horseshoe is owned by
`CochainComplex.InjectiveResolution.Horseshoe`.  The structure is the reusable data owner: it
records the resolving row, its source comparison, short exactness, and the prescribed outer
resolution maps.  The chapter entry therefore exposes the row-level and strictly-bounded views
as checks instead of maintaining a second upper-triangular construction.
-/

open CategoryTheory

/- The canonical data owner and its views. -/
@[stacks 013T "injective horseshoe data"]
#check @CochainComplex.InjectiveResolution.Horseshoe
@[stacks 013T "injective horseshoe row"]
#check @CochainComplex.InjectiveResolution.Horseshoe.row
@[stacks 013T "injective horseshoe comparison"]
#check @CochainComplex.InjectiveResolution.Horseshoe.rowComparison
@[stacks 013T "injective horseshoe middle comparison"]
#check @CochainComplex.InjectiveResolution.Horseshoe.middleComparison
@[stacks 013T "injective horseshoe middle resolution"]
#check @CochainComplex.InjectiveResolution.Horseshoe.middleResolution

/- The individual quasi-isomorphism APIs avoid unpacking a conjunction in downstream proofs. -/
@[stacks 013T "left comparison"]
#check @CochainComplex.InjectiveResolution.Horseshoe.leftComparison_quasiIso
@[stacks 013T "right comparison"]
#check @CochainComplex.InjectiveResolution.Horseshoe.rightComparison_quasiIso
@[stacks 013T "middle comparison"]
#check @CochainComplex.InjectiveResolution.Horseshoe.middleComparison_quasiIso

/- Existence with a prescribed left resolution and the common lower-bound refinement. -/
@[stacks 013T "prescribed-left existence"]
#check @CochainComplex.InjectiveResolution.Horseshoe.nonempty
@[stacks 013T "strict lower bound"]
#check @CochainComplex.InjectiveResolution.Horseshoe.exists_strictlyGE

/- Source-facing row-level bridges.  These retain the textbook existential shape while delegating
the actual construction to the neutral horseshoe owner. -/
@[stacks 013T "horseshoe existence"]
#check @CochainComplex.InjectiveResolution.exists_horseshoe
@[stacks 013T "row-level horseshoe existence"]
#check @CochainComplex.InjectiveResolution.exists_horseshoe_row
@[stacks 013T "strictly nonnegative row-level existence"]
#check @CochainComplex.InjectiveResolution.exists_horseshoe_row_strictlyGE_zero
