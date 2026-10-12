/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Tower
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.112.3

Compatibility entry point for the reusable tower API of extensions of
discrete valuation rings, owned by
`ReasLib.RingTheory.DiscreteValuationRing.Extension.Tower`.

@stack 0BRL
-/

/- Lemma 15.112.3 (1), tag `0BRL`: ramification indices multiply in towers. -/
@[stacks 0BRL "(1), ramification index in a tower"]
#check @IsExtensionOfDiscreteValuationRings.ramificationIndex_algebra_tower

/- Lemma 15.112.3 (2), tag `0BRL`: residue degrees multiply in towers. -/
@[stacks 0BRL "(2), residue degree in a tower"]
#check @IsExtensionOfDiscreteValuationRings.residueDegree_algebra_tower
