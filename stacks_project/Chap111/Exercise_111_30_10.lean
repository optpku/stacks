/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Complex.FiniteReplacement
import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
import StacksCheckRecall

@[expose] public section

/- Exercise 111.30.10: a bounded-below complex of finite filtered objects over an abelian
category with enough injectives admits a filtered quasi-isomorphism to a bounded-below
complex of filtered-injective objects. In fact the comparison may be chosen termwise as a
strict monomorphism. -/

@[stacks 028H] #check @CategoryTheory.FilteredComplex.StrictReplacement.exists_of_finiteComplex
@[stacks 028H] #check @CochainComplex.FilteredInjectivePlus.Resolution.nonempty

#check @CochainComplex.FilteredInjectivePlus.Resolution.quasiIso
#check @CochainComplex.FilteredInjectivePlus.Resolution.termMono
#check @CochainComplex.FilteredInjectivePlus.Resolution.termStrict
#check @CochainComplex.FilteredInjectivePlus.Resolution.strictlyGE

end
