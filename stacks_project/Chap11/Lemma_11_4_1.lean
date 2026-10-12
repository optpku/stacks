/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Centralizer.TensorProduct
import StacksCheckRecall

@[expose] public section

/-! Lemma 11.4.1 is the tensor-product centralizer computation. -/

@[stacks 0749] #check @Subalgebra.centralizer_tensorProduct_subalgebra_eq

end
