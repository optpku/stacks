/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.TensorProduct.SeparableClosure
import StacksCheckRecall

/-!
# Galois Action on Tensor-Product Primes

The reusable construction and its profinite support live in
`Algebra.TensorProduct.SeparableClosure.Galois`.  This chapter entry is a thin
source-facing recall of the resulting transitivity statement.

@stack 04KP
-/

@[expose] public section

/- Lemma 10.47.14 (Tag 04KP): the canonical left-factor Galois action on
`PrimeSpectrum (SeparableClosure k ⊗[k] K)`. -/
@[stacks 04KP "canonical action"]
#check @Algebra.TensorProduct.SeparableClosure.Galois.Action.primes

/- Lemma 10.47.14 (Tag 04KP): the Galois group of a separable closure acts
transitively on the primes of `SeparableClosure k ⊗[k] K`. -/
@[stacks 04KP]
#check @Algebra.TensorProduct.SeparableClosure.Galois.pretransitive

/- Lemma 10.47.14 (Tag 04KP), elementwise form: any two such primes are
conjugate under the canonical action. -/
@[stacks 04KP "elementwise form"]
#check @Algebra.TensorProduct.SeparableClosure.Galois.exists_smul_eq

end
