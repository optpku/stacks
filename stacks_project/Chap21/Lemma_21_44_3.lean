/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.44.3

Strict perfectness under tensor product is owned directly for commutative ring sheaves on
arbitrary sites, so the ringed-site entry needs no chapter-to-chapter bridge theorem.
-/

/- Lemma 21.44.3 (09J8): the total tensor product of two strictly perfect complexes on a ringed
site is strictly perfect. -/
@[stacks 09J8] #check @SheafOfModules.CochainComplex.IsStrictlyPerfect.tensorObj

#check @CochainComplex.boundedTermsIn_tensorObj

end
