/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
import StacksCheckRecall

@[expose] public section

/- 20.2.0.4: higher direct images of module sheaves are computed from injective resolutions. -/
@[stacks 0715]
#check @AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.isoHomologyPushforward
