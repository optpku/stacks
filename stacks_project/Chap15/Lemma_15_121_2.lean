/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.End.FiniteLength.Norm
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.121.2 (0GSZ)

This source file keeps the legacy repository path `Lemma_15_121_2`.  The residue-field norm
formula is owned by `Module.End.finiteLengthDeterminant_algebraLsmul_eq_norm_pow_length` in
ReasLib.

@stack 0GSZ
-/

/- Lemma 15.121.2: the determinant of scalar multiplication on a finite-length module is the
residue-field norm raised to the module length. -/
@[stacks 0GSZ "Lemma 15.121.2: determinant of scalar multiplication"]
#check @Module.End.finiteLengthDeterminant_algebraLsmul_eq_norm_pow_length

#check @IsLocalRing.isFiniteLength_restrictScalars
#check @Module.End.finiteLengthDeterminant
#print axioms Module.End.finiteLengthDeterminant_algebraLsmul_eq_norm_pow_length

end
