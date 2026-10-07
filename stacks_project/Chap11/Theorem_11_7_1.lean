module

public import ReasLib.Algebra.CentralSimple.Centralizer.Centralizer
import StacksCheckRecall

@[expose] public section

@[stacks 074T] #check @Subalgebra.isSimpleRing_centralizer
@[stacks 074T] #check @Subalgebra.finrank_centralizer
@[stacks 074T] #check @Subalgebra.centralizer_centralizer_eq

end
