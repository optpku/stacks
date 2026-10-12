/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_127_10

/-!
@stack 00QU

# Canonical base-change property of the Chapter 10 approximation

The source-facing predicate in Lemma 10.127.10 is definitionally the neutral
`Hom.baseChange_isLocalizationOfQuotient` property, so no comparison theorem is needed.
-/

@[expose] public section

#check @DirectedLocalHomApproximation.HasLocalizationOfQuotientTransitions
#check @Ring.DirectLimit.Algebra.Approximation.Hom.baseChange_isLocalizationOfQuotient
