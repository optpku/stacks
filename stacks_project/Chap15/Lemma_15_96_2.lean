/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Homology
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta

@[expose] public section

/-!
# Lemma 15.96.2

@stack 0F7P
-/

/-! # The Berthelot-Ogus eta homology comparison -/

/- Lemma 15.96.2, tag `0F7P`: the degree-`i` divided-coordinate comparison canonically identifies
cohomology modulo `f`-torsion with the cohomology of the integer-indexed Berthelot-Ogus eta complex. -/
@[stacks 0F7P "Berthelot-Ogus eta homology comparison"]
#check @CochainComplex.BerthelotOgus.Int.comparison_bijective_of_nonZeroDivisor

-- Canonical downstream use bundles termwise regularity in the eta domain.
#check @CochainComplex.BerthelotOgus.Int.comparison_bijective

-- The nonnegative owner remains available as the extension-by-zero specialization.
#check @CochainComplex.BerthelotOgus.Nat.comparison_bijective_of_nonZeroDivisor
