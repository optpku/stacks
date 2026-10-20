/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- An `m`-pseudo-coherent derived `𝒪_X`-module on a scheme. -/
abbrev IsMPseudoCoherent (X : Scheme.{u})
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) : Prop :=
  RingedSpace.ModuleDerived.IsMPseudoCoherent E m

/-- A pseudo-coherent derived `𝒪_X`-module on a scheme. -/
abbrev IsPseudoCoherent (X : Scheme.{u})
    (E : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  RingedSpace.ModuleDerived.IsPseudoCoherent E

end AlgebraicGeometry.Scheme
