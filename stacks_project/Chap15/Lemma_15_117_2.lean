/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.NagataDescent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.2 (0GLS)

This source file keeps the legacy repository path `Lemma_15_117_2`; the reusable `N-2` companion and
the source-facing Nagata theorem are owned by ReasLib.

@stack 0GLS
-/

/- Lemma 15.117.2: Nagata descent along a separable fraction-field extension. -/
@[stacks 0GLS "Lemma 15.117.2: Nagata descent"]
#check @IsExtensionOfDiscreteValuationRings.nagataRing_of_separable_fractionRingExtension

#check @IsExtensionOfDiscreteValuationRings.isN2Ring_of_separable_fractionRingExtension
#check @NagataRing
#print axioms IsExtensionOfDiscreteValuationRings.nagataRing_of_separable_fractionRingExtension

end
