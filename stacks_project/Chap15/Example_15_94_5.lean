module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.PrincipalCohomology
import StacksCheckRecall

/-!
# Example 15.94.5 (0BKG)

The principal derived-completion object and its four cohomological consequences are owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.PrincipalCohomology`.

@stack 0BKG
-/

@[expose] public section

/- Example 15.94.5 (1): degree `-1` cohomology is the principal Tate module. -/
@[stacks 0BKG "(1), degree minus one as the Tate module"]
#check @CategoryTheory.DerivedCategory.PrincipalCompletion.moduleHomologyNegOne_isIsomorphic_tateModule

/- Example 15.94.5 (2): degree-zero cohomology lies in the Milnor short exact sequence. -/
@[stacks 0BKG "(2), degree-zero Milnor short exact sequence"]
#check @CategoryTheory.DerivedCategory.PrincipalCompletion.moduleHomologyZero_shortExact

/- Example 15.94.5 (3): all cohomology outside degrees `-1` and `0` vanishes. -/
@[stacks 0BKG "(3), cohomological amplitude"]
#check @CategoryTheory.DerivedCategory.PrincipalCompletion.moduleHomology_isZero_of_ne_zero_or_negOne

/- Example 15.94.5 (4): cohomology of an arbitrary principal derived completion lies in the
Tate-module short exact sequence. -/
@[stacks 0BKG "(4), cohomology short exact sequence"]
#check @CategoryTheory.DerivedCategory.PrincipalCompletion.cohomology_shortExact

#check @CategoryTheory.DerivedCategory.PrincipalCompletion.ofModule
#check @CategoryTheory.DerivedCategory.PrincipalCompletion.moduleHomology
