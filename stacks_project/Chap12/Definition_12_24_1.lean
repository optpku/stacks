/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Definition
import StacksCheckRecall

@[expose] public section

/- Definition 12.24.1 [012L]: a filtered complex in `𝒜` is a cochain complex in the category
of filtered objects. The canonical, more general owner is `CategoryTheory.FilteredComplex`,
which requires only zero morphisms rather than an abelian structure. -/

@[stacks 012L] #check @CategoryTheory.FilteredComplex
