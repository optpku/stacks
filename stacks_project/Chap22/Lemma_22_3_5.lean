/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v

variable {R : Type u} [CommRing R]
variable (A B : CochainDGAlgebra.{u, v} R)

/- Lemma 22.3.5 (065X): the underlying cochain complex of the tensor-product DGA is the canonical
total tensor complex. -/
@[stacks 065X]
#check (CochainDGAlgebra.tensorProduct_toCochainComplex A B :
  (A ⊗[R] B).toCochainComplex =
    CochainDGAlgebra.Tensor.complex A B)
