/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Centralizer.Centralizer
import StacksCheckRecall

@[expose] public section

@[stacks 074T] #check @Subalgebra.isSimpleRing_centralizer
@[stacks 074T] #check @Subalgebra.finrank_centralizer
@[stacks 074T] #check @Subalgebra.centralizer_centralizer_eq

end
