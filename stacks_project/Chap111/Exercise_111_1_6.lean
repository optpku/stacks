/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Int.MulTwo
public import ReasLib.Algebra.Module.Int.AwayTwoThree
import StacksCheckRecall

@[expose] public section

/- Exercise 111.1.6 (1): a concrete nonsplit short exact sequence of `ℤ`-modules. -/
@[stacks 02CL] #check
  (Int.MulTwo.nonsplit :
    Int.MulTwo.shortComplex.ShortExact ∧ ¬ Nonempty Int.MulTwo.shortComplex.Splitting)

/- Companion checks for the second concrete example. -/
#check (Int.AwayTwoThree.shortExact : Int.AwayTwoThree.shortComplex.ShortExact)
#check (Int.AwayTwoThree.not_splitting :
  ¬ Nonempty Int.AwayTwoThree.shortComplex.Splitting)
#check (Int.AwayTwoThree.instFaithfullyFlat :
  @Module.FaithfullyFlat ℤ Int.AwayTwoThree _ _ Algebra.toModule)
#check (Int.AwayTwoThree.baseChange_shortExact :
  Int.AwayTwoThree.baseChange.ShortExact)

/- Exercise 111.1.6 (2): the nonsplit sequence becomes split after faithfully flat
base change to `AwayTwoThree`. -/
@[stacks 02CL] #check
  (Int.AwayTwoThree.baseChange_splits :
    Nonempty Int.AwayTwoThree.baseChange.Splitting)
