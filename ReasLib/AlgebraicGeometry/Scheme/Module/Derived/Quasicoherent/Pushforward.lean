/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent

/-!
# Derived Pushforward and the Quasicoherent Coherator

This module records the compatibility between ambient derived pushforward and the
right-derived coherator for flat quasi-compact, quasi-separated morphisms of schemes.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.Derived

/-- For a flat quasi-compact, quasi-separated morphism of schemes, ambient derived
pushforward followed by the derived coherator is naturally isomorphic to the derived
coherator followed by right-derived quasicoherent pushforward. -/
theorem pushforwardCoherator_isomorphic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    IsIsomorphic
      (RingedSpace.moduleDerivedPushforward f.toShHom ⋙ coherator Y)
      (coherator X ⋙ pushforward f) := sorry

end AlgebraicGeometry.Scheme.QCoh.Derived
