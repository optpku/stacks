/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Localization
import StacksCheckRecall

@[expose] public section

/-!
# 21.3.0.1

The source-facing factorization of a bounded-below right derived functor is a
specialization of the model-independent uniqueness comparison for a lifted
functorial injective resolution.
-/

open CategoryTheory

/- 21.3.0.1 (Stacks 05U5): a right derived functor is isomorphic to the
composite through any lifted bounded-below injective-resolution functor. -/
@[stacks 05U5] #check
  @HomotopyCategory.Plus.InjectiveResolutionFunctor.isIsomorphic_rightDerived_lift

#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.lift_comp_isRightDerivedFunctor
#check @Functor.rightDerivedUnique

end
