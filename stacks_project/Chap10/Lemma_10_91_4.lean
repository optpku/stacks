/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.PowerSeries
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.91.4

@stack 059T
-/

/- Lemma 10.91.4: finite-variable formal power series over a Noetherian ring are flat and
Mittag-Leffler over the coefficient ring. -/
@[stacks 059T]
#check @MvPowerSeries.fin_flat_mittagLeffler

@[stacks 059T "flat power-series module"]
#check @Module.Flat.mvPowerSeries

@[stacks 059T "Mittag-Leffler power-series module"]
#check @Module.MittagLeffler.mvPowerSeries

@[stacks 059T "combined flat Mittag-Leffler power-series module"]
#check @MvPowerSeries.flat_mittagLeffler
