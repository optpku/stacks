/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization
import StacksCheckRecall

/-!
# Lemma 10.70.2 recall

The chart-localization construction and its three consequences are reusable
ReasLib API.  This file retains the source label without creating parallel
chapter declarations.

@stack 07Z3
-/

@[expose] public section

/- Lemma 10.70.2 (07Z3): the chart parameter is regular, its extended center
is principal, and localization away from it recovers the base localization. -/
@[stacks 07Z3] #check @AffineBlowupChart.parameter_isRegular
@[stacks 07Z3] #check @AffineBlowupChart.map_ideal_eq_span_parameter
@[stacks 07Z3] #check @AffineBlowupChart.instIsLocalizationAway
