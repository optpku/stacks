module

import ReasLib.Algebra.Homology.CochainComplex.QuasiIso.Termwise
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.18.6.1

The generic owner for acyclic cokernels is formulated for homological complexes in
`HomologicalComplex.CokernelAcyclic`; the cochain specialization and its boundary-subobject
corollary are exposed here through the neutral termwise quasi-isomorphism leaf.
-/

/- The cokernel of a termwise monomorphic quasi-isomorphism is acyclic. -/
@[stacks 013Q]
#check @CategoryTheory.HomologicalComplex.cokernel_acyclic_of_quasiIso_of_mono
@[stacks 013Q]
#check @CochainComplex.acyclic_cokernel_of_quasiIso_of_termwiseMono

/- The image/intersection computation for incoming boundaries. -/
@[stacks 013Q]
#check @CochainComplex.image_dTo_comp_eq_inf_of_quasiIso_of_termwiseMono
@[stacks 013Q]
#check @CochainComplex.image_dTo_comp_eq_inf_of_quasiIso_of_termwiseMono
