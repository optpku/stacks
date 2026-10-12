/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.Lift
import StacksCheckRecall

@[expose] public section

/-!
# Frobenius base-change support for Lemma 10.42.4

The former rational-function Frobenius proof stage is subsumed by the neutral finite purely
inseparable lift API.

@stack 04KM
-/

/- Lemma 10.42.4, tag `04KM`: every essentially finite-type field extension admits a finite
purely inseparable lift whose top extension is separably generated. -/
@[stacks 04KM "finite purely inseparable lift"]
#check @FieldExtension.PurelyInseparable.Lift.existsOfEssFiniteType
