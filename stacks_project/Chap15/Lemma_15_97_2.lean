/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DeterminantalIdeal

@[expose] public section

/-!
# Lemma 15.97.2

@stack 0GST
-/

/- Lemma 15.97.2: multiplying a nonzerodivisor by a unit does not change the degreewise
Berthelot-Ogus eta determinantal ideal of a bounded finite-free complex. -/
@[stacks 0GST "unit invariance of the Berthelot-Ogus eta determinantal ideal"]
#check @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal_eq_unit_mul_of_bounded

-- The degree-local core does not require boundedness, regularity, or source-term freeness.
#check @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal_eq_unit_mul
