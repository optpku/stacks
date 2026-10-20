/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Existence
import StacksCheckRecall

@[expose] public section

@[stacks 0746] #check @FiniteDimensional.exists_simpleSubmodule
@[stacks 0746] #check @FiniteDimensional.exists_simpleSubmodule_regular
@[stacks 0746] #check @IsSimpleModule.finiteDimensional

end
