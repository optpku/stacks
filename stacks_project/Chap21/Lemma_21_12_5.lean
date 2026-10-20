/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Products
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.12.5

The low-degree product comparison for sheaf cohomology is already owned by
`CategoryTheory.Sheaf.Cohomology.Products`.
-/

open CategoryTheory.Sheaf.Cohomology

@[stacks 060L "degree-zero cohomology of a product"]
#check @productComparison_isIso_zero

@[stacks 060L "degree-one cohomology of a product"]
#check @productComparison_injective_one
