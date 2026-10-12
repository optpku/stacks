/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.TensorProduct.Kernel.FinitePresentation
import StacksCheckRecall

/-!
# Factoring tensor-kernel elements through finitely presented modules

@stack 059L

This is the source-facing factorization statement. Its witnesses are kept explicit: a finitely
presented module, the factor map into it, and the map onward to the original target.
-/

@[expose] public section

/- Lemma 10.89.4: if a tensor element dies under a map from a finitely presented
module, the map factors through another finitely presented module where that element already
dies. -/
@[stacks 059L "tensor-kernel factorization"]
#check @LinearMap.exists_finitePresentation_factorization_of_mem_ker_rTensor
