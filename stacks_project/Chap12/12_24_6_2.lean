/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Equation 12.24.6.2 [012T] is the specialization to a filtered-complex differential of the
morphism-level inclusion of eventual boundaries into the intrinsic boundary representative. -/
@[stacks 012T]
#check FilteredObject.Hom.Representative.Boundary.eventual_le_image
