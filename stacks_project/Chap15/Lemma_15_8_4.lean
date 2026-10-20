module

public import ReasLib.RingTheory.FittingIdeal.Operations
import StacksCheckRecall

/-!
# Basic properties of Fitting ideals

Lemma 15.8.4 collects the generation, direct-sum, base-change, finite-generation, quotient,
surjection, annihilator, and support properties of intrinsic Fitting ideals.

@stack 07ZA
-/

-- Lemma 15.8.4 (1): a bound on generators gives the unit Fitting ideal.
@[stacks 07ZA "(1), generator bound"]
#check @FittingIdeal.eq_top_of_surjective

-- Lemma 15.8.4 (2) and (3): Fitting ideals of direct sums.
@[stacks 07ZA "(2), zeroth Fitting ideal of a direct sum"]
#check @FittingIdeal.directSum_zero

@[stacks 07ZA "(3), Fitting ideal of a direct sum"]
#check @FittingIdeal.directSum

-- Lemma 15.8.4 (4): Fitting ideals commute with base change.
@[stacks 07ZA "(4), base change"]
#check @fittingIdeal_baseChange

-- Lemma 15.8.4 (5): Fitting ideals of finitely presented modules are finitely generated.
@[stacks 07ZA "(5), finite generation"]
#check @Module.FinitePresentation.fittingIdeal_fg

-- Lemma 15.8.4 (6): Fitting ideals increase under a module surjection.
@[stacks 07ZA "(6), module surjection"]
#check @FittingIdeal.mono_of_surjective

-- Lemma 15.8.4 (7): the zeroth Fitting ideal lies in the annihilator.
@[stacks 07ZA "(7), annihilator containment"]
#check @FittingIdeal.zero_le_annihilator

-- Lemma 15.8.4 (8): the zeroth Fitting ideal cuts out the support.
@[stacks 07ZA "(8), support"]
#check @Module.zeroLocus_fittingIdeal_zero_eq_support

-- Lemma 15.8.4 (9): the zeroth Fitting ideal of `R ⧸ I` is `I`.
@[stacks 07ZA "(9), quotient module"]
#check @FittingIdeal.quotientAtZero
