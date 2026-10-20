/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Triangle.Split
import StacksCheckRecall

@[expose] public section

/- Lemma 13.4.11 is owned by the reusable split-distinguished-triangle API. -/
@[stacks 05QT] #check @CategoryTheory.Pretriangulated.SplitTriangle.isSplitEpi₂_of_mor₃_eq_zero

@[stacks 05QT] #check @CategoryTheory.Pretriangulated.SplitTriangle.isIso_biprodDesc_of_rightInverse₂

@[stacks 05QT] #check @CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished

end
