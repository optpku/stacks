/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.RatFuncPowerSeries
import StacksCheckRecall

/-!
# Example 15.40.2 (07EM)

The first five recalls expose the explicit geometrically regular local hypersurface with purely
inseparable residue field.  The final recall is the related rational-function shift into a power
series ring.

@stack 07EM
-/

@[expose] public section

/- Example 15.40.2 (1): the hypersurface localization is local. -/
@[stacks 07EM "Example 15.40.2 (1): local hypersurface"]
#check @PurelyInseparableSmoothLocal.isLocalRing

/- Example 15.40.2 (2): the hypersurface localization is smooth over the ground field. -/
@[stacks 07EM "Example 15.40.2 (2): smooth hypersurface localization"]
#check @PurelyInseparableSmoothLocal.smooth

/- Example 15.40.2 (3): the hypersurface localization is geometrically regular. -/
@[stacks 07EM "Example 15.40.2 (3): geometrically regular local hypersurface"]
#check @PurelyInseparableSmoothLocal.isGeometricallyRegular

/- Example 15.40.2 (4): its residue field is purely inseparable over the ground field. -/
@[stacks 07EM "Example 15.40.2 (4): purely inseparable residue field"]
#check @PurelyInseparableSmoothLocal.residueField_isPurelyInseparable

/- Example 15.40.2 (5): the ground-field map is formally smooth for the maximal-ideal-adic
topology. -/
@[stacks 07EM "Example 15.40.2 (5): adic formal smoothness of the local hypersurface"]
#check @PurelyInseparableSmoothLocal.formallySmoothForAdic

/- The concrete rational-function shift and its value on the distinguished generator. -/
#check @RatFunc.PowerSeriesShift.map
#check @RatFunc.PowerSeriesShift.map_X

/- Example 15.40.2 (6): the shift `s ↦ t + x` into the power series ring over a perfect
closure is formally smooth for the maximal-ideal-adic topology. -/
@[stacks 07EM "Example 15.40.2 (6): rational-function shift"]
#check @RatFunc.PowerSeriesShift.formallySmoothForAdic
