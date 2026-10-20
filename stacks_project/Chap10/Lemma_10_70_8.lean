/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Scaling
public import ReasLib.RingTheory.Ideal.PowerTorsion
import StacksCheckRecall

/-!
# Principal scaling of affine blowup charts

The reusable construction belongs to `AffineBlowupChart.Scaling`.  This
source file is deliberately a recall block: it keeps the textbook entry near
the chapter while downstream users import the neutral ReasLib leaf directly.
-/

@[expose] public section

open scoped AffineBlowupChart

/-
Lemma 10.70.8 (Stacks tag `0BBI`): for `a : I` and `f : R`, principal
scaling gives `AffineBlowupChart.Scaling.map I a f`.  Its kernel is the
principal power-torsion ideal of the image of `f`, equivalently the
corresponding primary component.

The atomic reusable API below intentionally replaces the source's bundled
surjectivity-and-kernel conclusion.

@stack 0BBI
-/

#check @AffineBlowupChart.Scaling.chart
#check @AffineBlowupChart.Scaling.powerElement
@[stacks 0BBI] #check @AffineBlowupChart.Scaling.map
#check @AffineBlowupChart.Scaling.map_powerFraction
#check @AffineBlowupChart.Scaling.surjective
#check @AffineBlowupChart.Scaling.mem_ker_iff
#check @AffineBlowupChart.Scaling.ker_eq_primaryComponent
#check @Ideal.principalPowerTorsion
