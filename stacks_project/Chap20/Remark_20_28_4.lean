/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange.Composition
import StacksCheckRecall

@[expose] public section

/- [stacks 0ATL] Remark 20.28.4: vertically composable derived base-change maps compose to the
derived base-change map for the outer rectangle. -/

namespace AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.Composition

@[stacks 0ATL] #check @squareIso
#check @pushforwardIso
#check @map
#check @map_isMapAt
#check @map_eq

end AlgebraicGeometry.RingedSpace.Hom.DerivedBaseChange.Composition
