/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange.HorizontalComposition
import StacksCheckRecall

@[expose] public section

/- [stacks 0ATM] Remark 20.28.5: horizontally composable derived base-change maps compose to the
derived base-change map for the outer rectangle. -/

namespace AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.HorizontalComposition

@[stacks 0ATM] #check @squareIso
#check @map
#check @map_isMapAt
#check @map_eq

end AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.HorizontalComposition
