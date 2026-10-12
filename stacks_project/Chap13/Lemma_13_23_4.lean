/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Lemma 13.23.4

Enough injectives provides both an objectwise resolution choice and a
functorial realization.  The latter is canonical only up to the compatible
natural isomorphism exposed by ReasLib.
-/

/- Lemma 13.23.4 (Stacks 013X): existence and compatible uniqueness of
bounded-below injective resolution functors. -/
@[stacks 013X] #check @CochainComplex.nonempty_injectiveResolutionChoice

#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.nonempty
#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.existsUniqueIso

end
