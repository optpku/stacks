/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_8_7_Cover
public import stacks_project.Chap61.Lemma_61_8_7_Over
import StacksCheckRecall

@[expose] public section

open Algebra.WLocalIndEtale

/- Commutative square A → Cover A, B → Over A B. -/
@[stacks 097X] #check Cover
@[stacks 097X] #check Over
@[stacks 097X] #check comm

/- Lemma 61.8.7 (1): A → Cover A is faithfully flat and ind-étale. -/
@[stacks 097X] #check instFaithfullyFlat
@[stacks 097X] #check indEtale

/- Lemma 61.8.7 (2): B → Over A B is faithfully flat and ind-étale. -/
@[stacks 097X] #check instFaithfullyFlat_over
@[stacks 097X] #check indEtale_over

/- Lemma 61.8.7 (3): PrimeSpectrum (Cover A) is w-local. -/
@[stacks 097X] #check instWLocalSpace

/- Lemma 61.8.7 (4): PrimeSpectrum (Over A B) is w-local. -/
@[stacks 097X] #check instWLocalSpace_over

/- Lemma 61.8.7 (5): PrimeSpectrum.comap (toOver A B) is w-local. -/
@[stacks 097X] #check instIsWLocalMap

/- Lemma 61.8.7 (6): closed points of PrimeSpectrum (Over A B) are the inverse
image of those of PrimeSpectrum (Cover A). -/
@[stacks 097X] #check closedPoints_eq_preimage

/- Lemma 61.8.7 (7): closed points of PrimeSpectrum (Cover A) surject onto
PrimeSpectrum A. -/
@[stacks 097X] #check surjOn_closedPoints

/- Lemma 61.8.7 (8): closed points of PrimeSpectrum (Over A B) surject onto
PrimeSpectrum B. -/
@[stacks 097X] #check surjOn_closedPoints_over

/- Lemma 61.8.7 (9): localizations of Cover A at maximal ideals are strictly
henselian. -/
@[stacks 097X] #check instStrictHenselianLocalRing
