module

public import ReasLib.Algebra.CentralSimple.TensorProduct
import StacksCheckRecall

@[expose] public section

-- Lemma 11.4.7: Tensor product of finite central simple algebras is simple.

@[stacks 074F] #check @CSA.instIsSimpleRing_tensorProduct
@[stacks 074F] #check @CSA.instIsCentral_tensorProduct

end
