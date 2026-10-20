/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField.PresentationAtPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.135.8

@stack 00SG

The four source conditions are assembled by the ReasLib presentation-at-prime owner.  The
individual neighbourhood equivalences remain available as fine-grained APIs.
-/

@[stacks 00SG "four complete-intersection criteria at a prime"]
#check @Algebra.IsCompleteIntersectionOver.atPrime_tfae

@[stacks 00SG "local complete-intersection criterion at a prime"]
#check @Algebra.IsCompleteIntersectionOver.atPrime_iff_localNearPrime

@[stacks 00SG "global complete-intersection criterion at a prime"]
#check @Algebra.IsCompleteIntersectionOver.atPrime_iff_globalNearPrime

@[stacks 00SG "local and global neighbourhood comparison"]
#check @IsLocalCompleteIntersection.nearPrime_iff_globalNearPrime

@[stacks 00SG "regular-sequence polynomial presentation"]
#check @Algebra.PolynomialPresentationAtPrime.kernelGeneratedByRegularSequence
