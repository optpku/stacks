/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction

/-! # Absolute derived adjunctions on opens ringed sites -/

@[expose] public section

open CategoryTheory
open scoped RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

universe u

namespace AlgebraicGeometry.RingedSpace

/-- On opens ringed sites, K-flat and K-injective resolutions give the two absolute
derived universal properties of module pullback and pushforward. These are the
composite-derived conditions for the canonical derived unit and counit, not the
mere existence of some adjunction between the two functors. -/
theorem moduleDerivedAdjunctionHasPair {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    DerivedAdjunction.HasPair f := sorry

/-- The canonical total-derived pullback--pushforward adjunction for opens ringed sites. -/
noncomputable def moduleDerivedAdjunctionOfOpens {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    L(f)^* ⊣ R(f)_* :=
  @RingedSite.Hom.moduleDerivedAdjunction _ _ (opensRingedSiteHom f)
    _ _ _ (opensRingedSiteHom.DerivedPushforward.hasDerived f) _
    (moduleDerivedAdjunctionHasPair f)

end AlgebraicGeometry.RingedSpace
