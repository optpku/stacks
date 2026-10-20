/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction of module sheaves along an open immersion is additive. -/
instance restrictFunctor_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).Additive :=
  Functor.additive_of_iso (restrictFunctorIsoPullback f).symm

end AlgebraicGeometry.Scheme.Modules
