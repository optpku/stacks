/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.PresentationSequence

@[expose] public section

/- 16.3.1.1: the conormal sequence for composable algebra presentations,
after identifying its right term with a tensor product. -/
@[stacks 07EW]
#check @Algebra.Generators.Cotangent.exact_postcomp_equiv
