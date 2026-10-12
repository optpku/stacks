/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective.PowerSeries
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.93.5

@stack 05A1
-/

/- Lemma 10.93.5: a universally injective map into a finite-variable formal power-series
module has projective source when the source is a direct sum of countably generated submodules. -/
@[stacks 05A1]
#check @LinearMap.UniversallyInjective.projective_to_mvPowerSeries

@[stacks 05A1 "universally injective projective criterion"]
#check @LinearMap.UniversallyInjective.projective

@[stacks 05A1 "flat power-series module"]
#check @Module.Flat.mvPowerSeries

@[stacks 05A1 "Mittag-Leffler power-series module"]
#check @Module.MittagLeffler.mvPowerSeries
