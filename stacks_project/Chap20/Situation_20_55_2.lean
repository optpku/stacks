/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Situation 20.55.2 (0GT4): an ideal sheaf is locally principal regular when every point has a
neighborhood on which the ideal inclusion is multiplication by a regular local generator. -/
@[stacks 0GT4]
#check @IdealSheaf.IsRegularPrincipal

@[stacks 0GT4 "principal chart"]
#check @IdealSheaf.Chart

@[stacks 0GT4 "regular principal generator"]
#check @IdealSheaf.Chart.action_mono
