/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap55.Definition_55_3_4_Genus

/- Definition 55.3.4: the genus of a numerical type `T` is the integer whose
cast to `ℚ` is the associated rational genus expression. -/
@[stacks 0C72] #check (NumericalType.genus : NumericalType → ℤ)
