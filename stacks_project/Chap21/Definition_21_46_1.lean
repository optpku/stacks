/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local
import StacksCheckRecall

/-!
# Definition 21.46.1

The reusable local finite-Tor-dimension owner is
`RingedSite.Hom.ModuleDerived.LocallyHasFiniteTorDimension` in
`ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local`.
-/

@[expose] public section

/- Definition 21.46.1 (08FZ): Tor-amplitude and finite Tor dimension are represented by the
canonical derived-object, local, and module-sheaf predicates below. -/
@[stacks 08FZ "(1), derived-object Tor-amplitude"]
#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn

@[stacks 08FZ "(2), derived-object finite Tor dimension"]
#check @RingedSite.Hom.ModuleDerived.HasFiniteTorDimension

@[stacks 08FZ "(3), local finite Tor dimension"]
#check @RingedSite.Hom.ModuleDerived.LocallyHasFiniteTorDimension

@[stacks 08FZ "(4), module-sheaf Tor dimension"]
#check @RingedSite.ModuleCat.HasTorDimensionLE

end
