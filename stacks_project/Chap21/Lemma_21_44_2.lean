/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect.MappingCone
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.44.2

The ringed-site statement is a direct specialization of the arbitrary-site module-sheaf owner.
-/

/- Lemma 21.44.2 (08FM): mapping cones preserve strict perfectness. -/
@[stacks 08FM] #check @SheafOfModules.CochainComplex.IsStrictlyPerfect.mappingCone

#check @CochainComplex.boundedTermsIn_mappingCone

end
