/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DerivedInvariance
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.1

@stack 0GSS
-/

/- Lemma 15.97.1, tag `0GSS`: derived-isomorphic bounded complexes of finite free modules have
eta determinantal ideals that agree after the alternating-rank power correction. -/
@[stacks 0GSS "derived invariance of Berthelot-Ogus determinantal ideals"]
#check @CochainComplex.BerthelotOgus.Int.DeterminantalIdeal.pow_mul_eq_of_isIsomorphic_of_bounded

-- The reusable core only needs chosen upper bounds for the two complexes.
#check @CochainComplex.BerthelotOgus.Int.DeterminantalIdeal.pow_mul_eq_of_isIsomorphic
