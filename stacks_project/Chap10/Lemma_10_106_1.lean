/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RegularLocalRing.AssociatedGraded
import StacksCheckRecall

/-!
# Lemma 10.106.1

@stack 00NO
-/

@[expose] public section

/- Lemma 10.106.1 [stacks 00NO]: canonical reusable polynomial presentation
of the associated graded ring of a regular local ring. -/
@[stacks 00NO]
#check @IsRegularLocalRing.associatedGradedEquivMvPolynomial

/- The parameterized form also records the images of the polynomial
variables. -/
@[stacks 00NO "parameterized associated-graded presentation"]
#check @IsLocalRing.IsRegularSystemOfParameters.associatedGradedMap_bijective

@[stacks 00NO "canonical parameterized associated-graded equivalence"]
#check @IsLocalRing.IsRegularSystemOfParameters.associatedGradedEquiv

@[stacks 00NO "associated-graded images of regular parameters"]
#check @IsLocalRing.IsRegularSystemOfParameters.associatedGradedEquiv_X

@[stacks 00NO "parameterized associated-graded equivalence"]
#check @IsLocalRing.IsRegularSystemOfParameters.existsAssociatedGradedEquiv
