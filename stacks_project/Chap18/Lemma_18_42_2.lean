/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Tensor
import StacksCheckRecall

/-!
# Tensor products and constant module sheaves

The canonical comparison is constructed in ReasLib as a sheaf isomorphism;
its objectwise component is exactly the source formula.
-/

@[expose] public section

/- Lemma 18.42.2 (093K): for finitely presented `Q`, sections of the constant
sheaf on `M ⊗ Q` identify with the tensor product of the sections of `M̲` by
`Q`. -/
@[stacks 093K]
#check (@CategoryTheory.ConstantSheaf.tensorAppIso)

/- The reusable sheaf-level natural comparison. -/
#check (@CategoryTheory.ConstantSheaf.tensorIso)
#check (@CategoryTheory.ConstantSheaf.tensorComparison)
