/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.TwoSidedSubmodule
import StacksCheckRecall

@[expose] public section

-- Lemma 11.4.4: Simplicity of tensor product with a central division algebra.

@[stacks 074C] #check @IsSimpleRing.tensorProduct_of_central_division

end
