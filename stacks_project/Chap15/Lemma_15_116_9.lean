/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparable
import StacksCheckRecall

@[expose] public section

/-!
@stack 09EY
# Lemma 15.116.9

The ramification-elimination alternatives are owned by the ReasLib tower API.  The
`SourceTower` view uses the source tensor products themselves and records the two canonical maps
between their integral closures as weakly unramified DVR extensions.
-/

open IsExtensionOfDiscreteValuationRings
open DVR.Field

/- Lemma 15.116.9: source-facing alternatives for a degree-`p` purely inseparable step. -/
@[stacks 09EY "Lemma 15.116.9: purely inseparable ramification elimination"]
#check @IsWeakSolutionFor.ramificationElimination

/- Lemma 15.116.9: the same alternatives when the composite DVR extension is already an instance. -/
#check @IsWeakSolutionFor.ramificationElimination_of_extension

/- Lemma 15.116.9: source normalized tower with the two tensor-field clauses. -/
@[stacks 09EY "Lemma 15.116.9: normalized third alternative"]
#check @DVR.BaseChange.SourceTower
#check @DVR.BaseChange.SourceTower.spec
#check @DVR.BaseChange.SourceTower.left_isField
#check @DVR.BaseChange.SourceTower.right_isField
#check @DVR.BaseChange.SourceTower.normalized
#check @DVR.BaseChange.SourceTower.composite_isField
#check @DVR.BaseChange.SourceTower.left
#check @DVR.BaseChange.SourceTower.right
#check @DVR.BaseChange.SourceTower.toWeakSolution

/- Lemma 15.116.9: canonical reusable notions used by the alternatives. -/
#check @IsExtensionOfDiscreteValuationRings.WeaklyUnramified
#check @DVR.Field.IsTotallyRamified
#check @IsWeakSolutionFor
