/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Mathlib
import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.23.2

The reusable owners are the bounded-below injective homotopy category,
`CochainComplex.InjectiveResolutionChoice`, and
`HomotopyCategory.Plus.InjectiveResolutionFunctor`.  They are independent of
the Chapter 13 presentation and can be imported directly from ReasLib.
-/

open CategoryTheory
open scoped CategoryTheory

/- Definition 13.23.2 (Stacks 013W): bounded-below injective resolutions,
their homotopy category, and functorial realizations. -/
@[stacks 013W] #check @CochainComplex.InjectiveResolutionChoice

#check @HomotopyCategory.Plus.injective
#check @HomotopyCategory.Plus.Injective
#check @HomotopyCategory.Plus.termsIn
#check @HomotopyCategory.Plus.TermsIn
#check @HomotopyCategory.Plus.Injective.ι
#check @HomotopyCategory.Plus.TermsIn.toCochain
#check @CochainComplex.Plus.TermsIn.toHomotopy
#check @CochainComplex.Plus.TermsIn.toHomotopyCompιIso
#check @CochainComplex.InjectivePlus.toHomotopy
#check @HomotopyCategory.Plus.Injective.toInjectivePlus
#check @HomotopyCategory.Plus.Injective.fromInjectiveObject
#check @HomotopyCategory.Plus.Injective.fromInjectiveObjectCompιIso
#check @HomotopyCategory.Plus.Injective.fromInjectiveObject_map_bijective
#check @HomotopyCategory.Plus.Injective.nonempty_fromInjectiveObject_fullyFaithful
#check @HomotopyCategory.Plus.InjectiveResolutionFunctor

end
