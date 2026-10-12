/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.TensorProduct.Separable
import StacksCheckRecall

@[expose] public section

/- Lemma 9.13.4 [stacks 0CKN]: the tensor-product decomposition over an algebraically closed
field is owned by the reusable separable tensor-product comparison API. -/
#check Algebra.TensorProduct.separableToPiAlgHom
#check Algebra.TensorProduct.separableToPiAlgHom_apply_tmul
#check Algebra.TensorProduct.separableToPiAlgHom_bijective
@[stacks 0CKN]
#check Algebra.TensorProduct.separableToPiAlgEquiv
