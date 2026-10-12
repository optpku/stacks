/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
