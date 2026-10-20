/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition.Derived
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Reduction.Decomposition.Derived
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.8

@stack 0GSW
-/

/- Lemma 15.97.8 (Tag 0GSW): for bounded complexes of finite free modules representing the
same derived object, the integer-indexed degree decomposition ideals agree.  The first block is
the source-level owner; the second records its nonnegative extension-by-zero specialization. -/

#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.degreeIdeal
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.degreeIdeal_le_ker_iff
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.degreeIdeal_fg
@[stacks 0GSW "derived invariance of integer eta decomposition ideals"]
#check @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.degreeIdeal_eq_of_isIsomorphic

#check @CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition.degreeIdeal
#check @CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition.degreeIdeal_le_ker_iff
#check @CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition.degreeIdeal_fg
#check @CochainComplex.BerthelotOgus.Nat.Reduction.Decomposition.degreeIdeal_eq_of_isIsomorphic
