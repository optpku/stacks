/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.12.5: the tensor-product associator and its action on pure tensors are canonical.

@stack 00D0
-/

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type x} [AddCommGroup P] [Module R P]

/- Domain triage: this item lies in the linear algebra of threefold tensor products.
The `core/canonical` owner abstraction is the associator `TensorProduct.assoc R M N P`.
The `PiTensorProduct` declarations `tmulEquivDep` and `subsingletonEquiv` from Lemma `10.12.4`
provide one realization of the same comparison, but in this file they belong only to the
`bridge/view` layer and should not appear as a parallel public owner API. -/
@[stacks 00D0 "associator"]
#check @TensorProduct.assoc

/- Lemma 10.12.5 on pure tensors: the canonical associator sends
`((m ⊗[R] n) ⊗[R] p)` to `m ⊗[R] (n ⊗[R] p)`. -/
@[stacks 00D0 "pure tensor action"]
#check @TensorProduct.assoc_tmul

end
