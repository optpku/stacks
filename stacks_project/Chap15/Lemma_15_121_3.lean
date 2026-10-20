module

public import ReasLib.Algebra.Module.End.FiniteLength.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.121.3 (0GT0)

This source file keeps the legacy repository path `Lemma_15_121_3`.  The flat local base-change
formula is owned by `Module.End.finiteLengthDeterminant_baseChange_pow_closedFiberLength` in
ReasLib.

@stack 0GT0
-/

/- Lemma 15.121.3: flat local base change raises the determinant to the length of the closed
fiber. -/
@[stacks 0GT0 "Lemma 15.121.3: determinant under flat local base change"]
#check @Module.End.finiteLengthDeterminant_baseChange_pow_closedFiberLength

#check @IsLocalRing.isFiniteLength_baseChange_iff
#check @Module.End.finiteLengthDeterminant
#print axioms Module.End.finiteLengthDeterminant_baseChange_pow_closedFiberLength

end
