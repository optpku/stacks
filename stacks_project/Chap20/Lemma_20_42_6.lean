/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import StacksCheckRecall

@[expose] public section

/- Lemma 20.42.6 (0BYS): the canonical map
`K ⊗ (M ⟹ L) ⟶ M ⟹ (K ⊗ L)` and its functoriality are owned by the generic braided closed
monoidal API.  The ringed-space derived category supplies the ambient instances. -/
@[stacks 0BYS]
#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison

#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_uncurry
#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_tensor
#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_target
#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_source
