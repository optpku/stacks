/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.ObjectProperty.InjectiveClosure
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.26.13

The neutral owner states the genuine existence theorem directly from ambient enough injectives;
no auxiliary typeclass assumes the desired closure.
-/

namespace CategoryTheory.ObjectProperty.InjectiveClosure

/- Remark 13.26.13 (`015R`): every set-indexed family in an abelian category with enough
injectives is contained in a small abelian full subcategory with enough injectives. -/
@[stacks 015R] #check @ofFamily

/- The object-property form used to close an already specified small collection. -/
#check @ofProperty

end CategoryTheory.ObjectProperty.InjectiveClosure
