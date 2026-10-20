/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.5.7

The two assertions are the canonical homological and triangulated structures
on a functor lifted through a triangulated localization.  Their neutral owners
are recalled from `ReasLib`; the intermediate shift structure is exposed as
part of the same reusable API.
-/

@[stacks 05R7] #check @CategoryTheory.Localization.lift_isHomological
@[stacks 05R7] #check @CategoryTheory.Localization.liftCommShift
@[stacks 05R7] #check @CategoryTheory.Localization.lift_isTriangulated
