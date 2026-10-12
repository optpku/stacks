/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.23.7

Comparison of injective resolutions belongs to the homotopy category and does
not require choosing a derived category.  The reusable owner is
`CochainComplex.InjectiveResolution`.
-/

/- Remark 13.23.7 (Stacks 013Y): two injective resolutions of the same
cochain complex have a unique compatible homotopy comparison. -/
@[stacks 013Y] #check @CochainComplex.InjectiveResolution.existsUnique_homotopyComparison

#check @CochainComplex.InjectiveResolution.IsHomotopyComparison
#check @CochainComplex.InjectiveResolution.comparison_bijective
#check @CochainComplex.InjectiveResolution.isIso_of_isHomotopyComparison

end
