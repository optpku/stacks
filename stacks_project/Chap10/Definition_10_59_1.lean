/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel
public import ReasLib.RingTheory.Ideal.OfDefinition
import StacksCheckRecall

/-!
# Definition 10.59.1

@stack 07DU
-/

@[expose] public section

/- Definition 10.59.1 (Tag 07DU): the ideal-of-definition predicate and the two length-valued
Hilbert-Samuel functions are recalled from neutral shared owners. -/
@[stacks 07DU]
#check @Ideal.IsIdealOfDefinition
@[stacks 07DU]
#check @Ideal.hilbertSamuelChi
@[stacks 07DU]
#check @Ideal.hilbertSamuelPhi
