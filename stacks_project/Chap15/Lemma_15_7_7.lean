/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Pullback.BaseChange.Descent
import StacksCheckRecall

/-!
# Lemma 15.7.7

For clauses (1)--(5), the hypothesis
`IsIso S.tensorPullbackComparison` expresses the source construction
`D' = D ×_C C'`.  Clause (6) supplies this hypothesis for a flat
`B'`-algebra, and clause (7) packages the construction as an equivalence of
the corresponding full subcategories.

@stack 08KQ
-/

@[stacks 08KQ "(1) finite-type descent across a surjective pullback"]
#check @FiberProductBaseChangeSituation.finiteType_iff_of_comparison_isIso

@[stacks 08KQ "(2) flatness descent across a surjective pullback"]
#check @FiberProductBaseChangeSituation.flat_iff_of_comparison_isIso

@[stacks 08KQ "(3) flat finite-presentation descent across a surjective pullback"]
#check @FiberProductBaseChangeSituation.flat_finitePresentation_iff_of_comparison_isIso

@[stacks 08KQ "(4) smoothness descent across a surjective pullback"]
#check @FiberProductBaseChangeSituation.smooth_iff_of_comparison_isIso

@[stacks 08KQ "(5) etaleness descent across a surjective pullback"]
#check @FiberProductBaseChangeSituation.etale_iff_of_comparison_isIso

@[stacks 08KQ "(6) flat algebra is recovered from its pullback system"]
#check @FiberProductBaseChangeSituation.tensorPullbackComparison_isIso_of_flat

@[stacks 08KQ "flat algebra object property"]
#check @SurjectiveRingPullbackSituation.flatAlgebraProperty

@[stacks 08KQ "category of flat algebras over the pullback"]
#check @SurjectiveRingPullbackSituation.FlatAlgebraCat

@[stacks 08KQ "category of componentwise-flat algebra systems"]
#check @SurjectiveRingPullbackSituation.FlatAlgebraSystemCat

@[stacks 08KQ "base-change functor on flat algebra subcategories"]
#check @SurjectiveRingPullbackSituation.flatAlgebraBaseChangeFunctor

@[stacks 08KQ "(7) equivalence of flat algebra gluing systems"]
#check @SurjectiveRingPullbackSituation.flatAlgebraBaseChangeFunctor_isEquivalence
