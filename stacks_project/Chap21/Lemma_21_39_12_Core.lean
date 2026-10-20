/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.12 (08RX), core recall.

The reusable owner is `RingedSite.Hom.DerivedPoint.lowerShriek`: it first applies the exact
forgetful functor from derived modules to additive presheaves and then the derived colimit over
the projection to a point.  The chapter file deliberately keeps no chaotic-site aliases or local
derived-category instances; downstream files can import the ReasLib owner directly.
-/

@[stacks 08RX "derived lower shriek to a point"]
#check @RingedSite.Hom.DerivedPoint.lowerShriek

#check @RingedSite.Hom.underlyingAbelianPresheafDerived
