/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.23.3

An objectwise choice of bounded-below injective resolutions is functorial only
up to a uniquely compatible homotopy-category realization.  ReasLib keeps the
choice, its comparison maps, and this realization relation at their natural
homotopy layer.
-/

/- Lemma 13.23.3 (Stacks 05TJ): an objectwise injective-resolution choice has
a functorial homotopy-category realization. -/
@[stacks 05TJ] #check @CochainComplex.InjectiveResolutionChoice.exists_resolutionFunctor

#check @CochainComplex.InjectiveResolutionChoice.homotopyObj
#check @CochainComplex.InjectiveResolutionChoice.comparison
#check @CochainComplex.InjectiveResolutionChoice.IsRealizedBy

end
