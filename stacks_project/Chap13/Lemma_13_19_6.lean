module

import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Lifting
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.19.6

The bounded-above projective factorization statements are owned by
`CochainComplex.ProjectiveMinus` in ReasLib.  The chapter keeps the textbook labels while
recalling the namespace-level API directly.
-/

/- Homotopy factorization through a quasi-isomorphism. -/
@[stacks 0649]
#check @CochainComplex.ProjectiveMinus.exists_homotopy_lift

/- Strict factorization for a termwise epimorphic quasi-isomorphism. -/
@[stacks 0649]
#check @CochainComplex.ProjectiveMinus.exists_lift_of_termwiseEpi

/- The kernel acyclicity bridge used by the strict factorization. -/
@[stacks 0649]
#check @CochainComplex.acyclic_kernel_of_quasiIso_of_termwiseEpi
