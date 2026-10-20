/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.AtPrime.TensorProduct.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.124.3

@stack 07NC
-/

/- Lemma 10.124.3 [stacks 07NC]: canonical recall of the quasi-finite
completed-local tensor-product splitting.  The reusable owner is
`AdicCompletion.AtPrime.TensorProduct.exists_prodAlgEquiv_of_quasiFiniteAt`,
whose distinguished projection is the canonical completed-local tensor map. -/
@[stacks 07NC]
#check @AdicCompletion.AtPrime.TensorProduct.exists_prodAlgEquiv_of_quasiFiniteAt
