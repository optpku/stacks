/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Admissible
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

-- Definition 13.40.9: admissibility is a property of the canonical inclusion of a strictly
-- full triangulated object property and is owned by the pretriangulated shared API.
@[stacks 0FXD] #check @CategoryTheory.ObjectProperty.IsRightAdmissible
#check @CategoryTheory.ObjectProperty.IsLeftAdmissible
#check @CategoryTheory.ObjectProperty.IsAdmissible
