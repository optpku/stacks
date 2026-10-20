/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution

@[expose] public section

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- A source-facing pure injective resolution is the canonical explicit pure injective
coresolution. -/
abbrev PureInjectiveResolution (N : ModuleCat.{v} A) :=
  PureInjectiveCoresolution N

end ModuleCat
