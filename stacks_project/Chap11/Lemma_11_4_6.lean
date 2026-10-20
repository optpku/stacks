/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.SimpleModule.SimpleModule
import StacksCheckRecall

@[expose] public section

section
variable {k : Type*} [Field k]

@[stacks 074E] #check @IsSimpleModule.nonempty_linearEquiv
@[stacks 074E] #check @IsSimpleModule.nonempty_linearEquiv_fin_fun
@[stacks 074E] #check @IsSimpleModule.linearEquiv_iff_finrank_eq
@[stacks 074E] #check @IsSimpleModule.matrix_fun
@[stacks 074E] #check @IsSimpleModule.matrix_fin_fun
@[stacks 074E] #check @matrix_endomorphism_alg_equiv_op
@[stacks 074E] #check @IsSimpleModule.end_isUnit_of_ne_zero
@[stacks 074E] #check @IsSimpleModule.finiteDimensional_end
@[stacks 074E] #check @IsSimpleModule.doubleCentralizerAlgEquiv
@[stacks 074E] #check @IsSimpleModule.centerEquiv
@[stacks 074E] #check @IsSimpleModule.finrank_mul_finrank_end
@[stacks 074E] #check @IsSimpleModule.end_algEquiv_matrix
@[stacks 074E] #check @IsSimpleModule.doubleCentralizerAlgEquiv_finite

end

end
