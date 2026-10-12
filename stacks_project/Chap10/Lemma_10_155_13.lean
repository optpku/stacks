/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.Tensor
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Strict henselization after henselian base change

The source chooses a common separable closure to write an equality of
constructions.  The reusable statement is the owner-level assertion in
`IsStrictHenselizationOf.BaseChange.Tensor`: it keeps the residue-field
comparison map explicit; the chapter-level base-map bridge is exposed as
`isStrict_of_baseResidueField`.

@stack 0C2Z
-/

/- Lemma 10.155.13 (tag `0C2Z`): if a local map induces a bijection on residue
fields, the tensor of a henselization with a strict henselization over the
henselization of the source is a strict henselization of the target. -/
#check @IsStrictHenselizationOf.BaseChange.Tensor.carrier
#check @IsStrictHenselizationOf.BaseChange.Tensor.algebra

@[stacks 0C2Z]
#check @IsStrictHenselizationOf.BaseChange.Tensor.isStrict
#check @IsStrictHenselizationOf.BaseChange.Tensor.isStrict_of_baseResidueField
#check @IsStrictHenselizationOf.BaseChange.AtPrime.Tensor.isStrict
#check @IsStrictHenselizationOf.BaseChange.AtPrime.Tensor.isStrict_of_bijectiveComparison
