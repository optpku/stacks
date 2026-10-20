/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductComposition
import StacksCheckRecall

@[expose] public section

/- [stacks 0FP6] Lemma 20.31.7: the relative derived cup product is compatible with composition
of derived pushforwards.  This is exactly the categorical owner theorem
`CategoryTheory.relativeDerivedCupProduct_comp_commSq`, specialized to derived categories of
`𝒪_X`-modules on ringed spaces. -/
@[stacks 0FP6] #check @CategoryTheory.relativeDerivedCupProduct_comp_commSq

/- Equality-form companion to the previous square-form recall. -/
#check @CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated
