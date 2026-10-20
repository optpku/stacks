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

/- This compatibility module now defers directly to the canonical ReasLib owners.  Direct
downstream files should import `ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction`
instead of this historical path. -/

/- Canonical derived pullback/pushforward data remain discoverable from this compatibility path. -/
@[stacks 07A6 "derived module adjunction"]
#check @RingedSite.Hom.moduleDerivedAdjunction

@[stacks 0735 "flat derived pullback isomorphism"]
#check @RingedSite.Hom.modulePullbackDerived.Flat.exactIso
