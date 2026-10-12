/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Lemma 13.23.5

The injective full subcategory is triangulated at the homotopy layer.  A
functorial resolution carries its exactness as an explicitly quantified,
noncanonical shift comparison, rather than as a global local-instance side
effect.
-/

/- Lemma 13.23.5 (Stacks 014W): a bounded-below injective resolution functor
is exact as a triangulated functor. -/
@[stacks 014W] #check @HomotopyCategory.Plus.InjectiveResolutionFunctor.exact

#check @HomotopyCategory.Plus.injective
#check @HomotopyCategory.Plus.Injective
#check @Functor.HasTriangulatedStructure

end
