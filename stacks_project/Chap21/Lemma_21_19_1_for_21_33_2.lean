/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Flat
import StacksCheckRecall

@[expose] public section

/- Compatibility shim to the canonical Chapter 21 owner file. -/

/- The 21.33 tensor arguments use the same canonical derived adjunction and flat comparison. -/
@[stacks 07A6 "derived module adjunction"]
#check @RingedSite.Hom.moduleDerivedAdjunction

@[stacks 0735 "flat derived pullback comparison"]
#check @RingedSite.Hom.modulePullbackDerived.Flat.comparison
