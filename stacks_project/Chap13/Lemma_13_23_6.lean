/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.InjectiveResolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Lemma 13.23.6

The appropriate owner for the factorization through the bounded-below derived
category is Mathlib's `DerivedCategory.Plus.Qh`; ReasLib records the precise
inversion and equivalence results for injective resolution functors, including
the model-independent localization criterion.
-/

/- Lemma 13.23.6 (Stacks 05TK): a functorial injective resolution inverts
bounded-below quasi-isomorphisms and hence descends across `D⁺`. -/
@[stacks 05TK] #check @HomotopyCategory.Plus.InjectiveResolutionFunctor.isInvertedBy

#check @DerivedCategory.Plus.Qh
#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.lift_isEquivalence_of_isLocalization
#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.Lift.isEquivalence
#check @HomotopyCategory.Plus.Injective.toDerived
#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.toDerived.isEquivalence_of_resolution

end
