/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DeterminantalIdeal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.3

@stack 0GSU
-/

/- Lemma 15.97.3: the degree-`i` determinantal ideal of the scalar-differential presentation
of a bounded finite-free complex commutes with base change when the chosen nonzerodivisor remains
a nonzerodivisor. -/
@[stacks 0GSU "base change of Berthelot-Ogus determinantal ideals"]
#check @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal_baseChange_of_bounded

-- The degree-local core works for arbitrary base change without the source-level hypotheses.
#check @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal_baseChange
