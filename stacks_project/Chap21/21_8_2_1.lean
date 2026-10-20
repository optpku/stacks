/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Refinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 21.8.2.1 (Tag 03F4): a morphism from the formal coproduct of a refinement to that of
the original family induces the canonical map from the original Cech complex to the refined
Cech complex. -/
@[stacks 03F4 "Cech-complex map induced by a refinement"]
#check @CategoryTheory.cechComplexMapOfRefinement

/- The construction is natural in the coefficient presheaf, with a named degreewise formula. -/
#check @CategoryTheory.cechComplexMapOfRefinementNatTrans
#check @CategoryTheory.cechComplexMapOfRefinement_f

end
