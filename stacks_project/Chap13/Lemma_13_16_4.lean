/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Homology.Conservative
import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
import StacksCheckRecall

@[expose] public section

/- Lemma 13.16.4 is owned by the shared cohomology-conservativity and
right-acyclicity-characterization APIs.  The all-positive-integers predicates
are the canonical surfaces; their natural-number views remain available for
the source-facing compatibility theorems. -/
@[stacks 015C] #check @CategoryTheory.DerivedCategory.isIso_iff_homology_map_isIso
@[stacks 015C] #check @CategoryTheory.Functor.RightDerived.Bounded.Vanishes.aboveZero
@[stacks 015C] #check @CategoryTheory.Functor.RightAcyclic.Bounded.iff_zero_and_vanishes
@[stacks 015C] #check @CategoryTheory.Functor.RightAcyclic.Bounded.iff_vanishes
@[stacks 015C] #check @CategoryTheory.Functor.RightDerived.Vanishes.aboveZero
@[stacks 015C] #check @CategoryTheory.Functor.RightAcyclic.iff_zero_and_vanishes
@[stacks 015C] #check @CategoryTheory.Functor.RightAcyclic.iff_vanishes

end
