module

public import ReasLib.LinearAlgebra.Matrix.SmithNormalForm
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.125.5

@stack 0ASR

This source-facing file recalls the two canonical owners: `IsBezout` for the
finitely-generated-principal condition and `IsElementaryDivisorDomain` for the
matrix Smith form.  The concrete diagonal and matrix predicate are exposed by
the same ReasLib leaf for downstream matrix-level reuse.
-/

/- Definition 15.125.5 (1): Bézout domains. -/
@[stacks 0ASR "Definition 15.125.5 (1), Bezout domain"]
#check @IsBezout

/- Definition 15.125.5 (2): elementary divisor domains. -/
@[stacks 0ASR "Definition 15.125.5 (2), elementary divisor domain"]
#check @IsElementaryDivisorDomain

#check @Matrix.smithNormalDiagonal
#check @Matrix.HasElementaryDivisorDiagonal
#check @Matrix.hasElementaryDivisorDiagonal_of_smithNormalDiagonal
#check @isBezout_of_isElementaryDivisorDomain
#check @isElementaryDivisorDomain_of_isPrincipalIdealRing
