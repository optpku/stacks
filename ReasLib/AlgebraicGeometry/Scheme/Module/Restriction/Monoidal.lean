/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Restriction

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restriction along an open immersion is strong monoidal via its comparison with pullback. -/
@[implicit_reducible]
noncomputable def restrictionMonoidal : (restrictFunctor f).Monoidal :=
  Functor.Monoidal.transport (restrictFunctorIsoPullback f).symm

/-- Open-immersion restriction carries the canonical transported monoidal structure. -/
noncomputable instance instRestrictionMonoidal : (restrictFunctor f).Monoidal :=
  restrictionMonoidal f

end AlgebraicGeometry.Scheme.Modules
