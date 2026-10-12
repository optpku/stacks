/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Dimension
import StacksCheckRecall

/-!
# Proposition 10.60.9

@stack 00KQ
-/

@[expose] public section

/- Proposition 10.60.9: for a Noetherian local ring `R` and `d : ℕ`, Krull dimension `d`,
Hilbert-Samuel degree `d`, and the existence of a minimally sized `d`-element parameter family
generating an ideal of definition are equivalent. -/
@[stacks 00KQ]
#check @Ideal.HilbertSamuel.dimension_tfae

/- The dimension comparison is also available as fine-grained reusable implications. -/
#check @Ideal.HilbertSamuel.degree_eq_iff_ringKrullDim_eq
#check @IsLocalRing.exists_parameterIdeal_of_ringKrullDim_eq
#check @IsLocalRing.not_exists_parameterIdeal_of_lt_ringKrullDim
#check @Ideal.IsIdealOfDefinition.ringKrullDim_le_spanFinrank
