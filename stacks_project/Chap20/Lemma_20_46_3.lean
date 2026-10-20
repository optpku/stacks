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
# Lemma 20.46.3

The canonical owner is stated for a commutative ring sheaf on an arbitrary site.  Its proof
factors through the reusable bounded-termwise tensor API and the tensor closure of finite-free
retract module sheaves.
-/

/- Lemma 20.46.3 (09J2): the total tensor product of two strictly perfect complexes is strictly
perfect. -/
@[stacks 09J2] #check @SheafOfModules.CochainComplex.IsStrictlyPerfect.tensorObj

#check @CochainComplex.tensorObj_isStrictlyGE
#check @CochainComplex.tensorObj_isStrictlyLE
#check @CochainComplex.boundedTermsIn_tensorObj
#check @SheafOfModules.CochainComplex.IsTermwiseFiniteFreeRetract.tensorObj

end
