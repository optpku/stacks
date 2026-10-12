/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.TensorProduct
import StacksCheckRecall

@[expose] public section

-- Lemma 11.4.7: Tensor product of finite central simple algebras is simple.

@[stacks 074F] #check @CSA.instIsSimpleRing_tensorProduct
@[stacks 074F] #check @CSA.instIsCentral_tensorProduct

end
