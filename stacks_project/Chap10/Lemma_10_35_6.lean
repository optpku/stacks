/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Jacobson.Noetherian
import StacksCheckRecall

/-!
# Lemma 10.35.6

@stack 00G4

The source statement is recalled from the reusable Jacobson criteria owner. The final check is
the dimension-at-most-one interface used by later dimension arguments.
-/

/- Lemma 10.35.6 (1): the ring of integers is a Jacobson ring. -/
@[stacks 00G4 "(1)"]
#check Int.instIsJacobsonRing

/- Lemma 10.35.6 (2): a Noetherian domain with infinitely many maximal ideals, in which every
nonzero prime ideal is maximal, is a Jacobson ring. -/
@[stacks 00G4 "(2)"]
#check @IsJacobsonRing.of_nonzero_prime_isMaximal_of_infinite_maximalSpectrum

/- Canonical dimension-at-most-one companion to Lemma 10.35.6. -/
@[stacks 00G4 "dimension-at-most-one companion"]
#check @IsJacobsonRing.of_dimensionLEOne_of_infinite_maximalSpectrum
