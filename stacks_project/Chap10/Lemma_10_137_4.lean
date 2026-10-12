/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.OverField.Smooth

@[expose] public section

/-!
# Smooth Algebras as Local Complete Intersections

The source result is the field-specialized consequence of the reusable
smoothness, standard-smooth-cover, and complete-intersection interfaces.

@stack 00T5
-/

/- Lemma 10.137.4, tag `00T5`: every smooth algebra over a field is a local
complete intersection. -/
@[stacks 00T5 "smooth algebra over a field is local complete intersection"]
#check @Algebra.Smooth.isLocalCompleteIntersection
