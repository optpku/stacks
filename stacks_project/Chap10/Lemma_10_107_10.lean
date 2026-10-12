/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.TensorProduct.FiniteRelations
import StacksCheckRecall

/-!
# Finite relations in tensor products

@stack 04VX
-/

@[expose] public section

/- Lemma 10.107.10: finite tensor relations admit a coefficient-matrix presentation. -/
@[stacks 04VX]
#check @TensorProduct.finsupp_sum_tmul_eq_zero_iff_exists_generator_matrix

@[stacks 04VX "right-exactness owner"]
#check @rTensor_exact
