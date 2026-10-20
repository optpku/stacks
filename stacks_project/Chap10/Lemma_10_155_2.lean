module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Specified
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.155.2

@stack 04GP

The specified-residue-field theorem, intrinsic strict-henselization owner, and
neutral residue-coordinate interface are recalled directly from ReasLib.
-/

@[stacks 04GP "specified separable-closure bridge"]
#check @IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv

@[stacks 04GP "intrinsic existence theorem"]
#check @IsStrictHenselizationOf.exists_strict

@[stacks 04GP "neutral residue-coordinate interface"]
#check @IsStrictHenselizationOf.ResidueField.Coordinate.exists_of_isSepClosure
