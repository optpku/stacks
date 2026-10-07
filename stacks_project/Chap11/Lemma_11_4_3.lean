module

public import ReasLib.Algebra.CentralSimple.TwoSidedSubmodule
import StacksCheckRecall

@[expose] public section

-- Lemma 11.4.3: Two-sided submodule descent for tensor products over central division algebras.

@[stacks 074B] #check @two_sided_submodule_eq_generated_by_inter_tmul_one
#check @Subbimodule.eq_baseChange_comap
#check @two_sided_submodule_comm_eq_generated_by_inter_tmul_one

end
