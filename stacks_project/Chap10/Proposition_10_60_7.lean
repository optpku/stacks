/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Artinian.DimensionZero
import StacksCheckRecall

/-!
# Proposition 10.60.7

@stack 00KJ
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 10.60.7: the ten standard Artinian-ring criteria are owned by
`IsArtinianRing.dimensionZero_tfae`; the remaining checks expose its principal reusable
components. -/
@[stacks 00KJ "source ten-clause form"]
#check @IsArtinianRing.dimensionZero_tfae

@[stacks 00KJ "Noetherian zero-dimensional criterion"]
#check @isArtinianRing_iff_isNoetherianRing_krullDimLE_zero

@[stacks 00KJ "finite-length criterion"]
#check @isArtinianRing_iff_isFiniteLength

@[stacks 00KJ "discrete-spectrum criterion"]
#check @PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero

@[stacks 00KJ "local Hilbert-Samuel dimension criterion"]
#check @Ideal.HilbertSamuel.degree_eq_iff_ringKrullDim_eq

@[stacks 00KJ "local nilpotent-maximal-ideal criterion"]
#check @isArtinianRing_iff_isNilpotent_maximalIdeal
