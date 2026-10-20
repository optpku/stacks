/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A surjective finite locally free morphism transfers the resolution property from its
source to its target. -/
theorem hasResolutionProperty_of_surjective_finiteLocallyFree {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [IsFiniteLocallyFree f] (hX : HasResolutionProperty X) :
    HasResolutionProperty Y := sorry

end AlgebraicGeometry.Scheme
