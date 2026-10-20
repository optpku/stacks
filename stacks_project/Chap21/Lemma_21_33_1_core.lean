/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import StacksCheckRecall

@[expose] public section

/- Core owner surface for the relative derived cup product used by Chapter 21. -/

namespace CategoryTheory

#check @Adjunction.rightAdjointTensorMapAdjointOf
#check @Adjunction.rightAdjointTensorMapOf
#check @Adjunction.rightAdjointTensorMapOf_spec
#check @Adjunction.rightAdjointLaxMonoidal
#check @Functor.LaxMonoidal.μ

end CategoryTheory
