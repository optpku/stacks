/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Composition.Specified
import StacksCheckRecall

@[expose] public section

/-!
# Strict Henselizations over a Henselization

@stack 0BSL
-/

/- Remark 10.155.4: composition with a henselization preserves the intrinsic strict-henselization
property. -/
@[stacks 0BSL "strict henselization composed with a henselization"]
#check @IsStrictHenselizationOf.of_henselization

/- Remark 10.155.4: existence with a specified separable closure of the original residue field. -/
@[stacks 0BSL "specified residue-field coordinate"]
#check @IsStrictHenselizationOf.exists_over_henselization_with_residueFieldEquiv
