module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Domination.Pushout

/-!
# Factorization criterion for tensor-kernel domination

@stack 059D
-/

@[expose] public section

/- Lemma 10.88.5 is owned by the reusable finite-cokernel factorization API. -/

@[stacks 059D]
#check @LinearMap.Dominates.iff_factorsThrough
