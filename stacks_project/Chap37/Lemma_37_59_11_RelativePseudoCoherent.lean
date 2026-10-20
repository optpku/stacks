/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Module

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- The derived relative pseudo-coherence API is provided by its reusable mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ), Prop)

/- The ordinary-module specialization is re-exported by the same reusable owner. -/
#check
  (AlgebraicGeometry.Scheme.Modules.IsMPseudoCoherentOver :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [LocallyOfFiniteType f] (m : ℤ), Prop)
