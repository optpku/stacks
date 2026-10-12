/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.Centralizer.TensorProduct
import StacksCheckRecall

@[expose] public section

@[stacks 074U] #check @Subalgebra.centralizer_tensorProduct_bijective
@[stacks 074U] #check @Subalgebra.centralizer_tensorProduct_algEquiv

end
