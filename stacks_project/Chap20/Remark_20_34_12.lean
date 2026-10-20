/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.BaseChange
import StacksCheckRecall

@[expose] public section

/- Remark 20.34.12 (0G78): for closed subsets `Z` and `Z'`, a functor between their derived
module categories together with an isomorphism comparing the two derived direct images has a
canonical right mate

`ClosedSubset.DerivedBaseChange.map squareIso`.

Its objectwise mate equation and its compatibility with the two adjunction counits are exposed by
`ClosedSubset.DerivedBaseChange.app_spec` and
`ClosedSubset.DerivedBaseChange.counitCommSq`. -/

@[stacks 0G78]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.map
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.app
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.IsMapAt
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.app_isMapAt
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.app_spec
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.IsMapAt.eq_app
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.IsMap.eq_map
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.counitCommSq
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange.app_comp_counit
