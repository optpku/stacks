/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Realization.DerivedLimit
import StacksCheckRecall

/-!
# Remark 15.88.6

@stack 07KZ
-/

@[expose] public section

open CategoryTheory

/- Remark 15.88.6 (1): the derived inverse limit of a realization is a derived limit of the
prescribed stage tower after restriction to the inverse-limit ring. -/
@[stacks 07KZ "(1), a realization computes the derived limit"]
#check @ModuleCat.DerivedTower.Realization.isDerivedLimit

/- Remark 15.88.6 (2): the isomorphism class of the derived inverse limit is independent of the
chosen realization. -/
@[stacks 07KZ "(2), independence of the realization"]
#check @ModuleCat.DerivedTower.Realization.derivedInverseLimitIsomorphic

/- Remark 15.88.6 (3): the cohomology of the derived inverse limit lies in the canonical Milnor
short exact sequence involving `lim` and `R¹ lim` of stage cohomology. -/
@[stacks 07KZ "(3), Milnor cohomology short exact sequence"]
#check @ModuleCat.DerivedTower.Realization.cohomologyShortExact

end
