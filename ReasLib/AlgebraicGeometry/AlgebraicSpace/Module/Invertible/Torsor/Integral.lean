/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor

/-! # Integrality of multiplicative torsors -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The multiplicative torsor of an invertible module on an integral algebraic
space is integral. -/
instance instIsIntegral_gmTorsor {S : Scheme.{u}} {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] [IsIntegral X] :
    IsIntegral (Modules.gmTorsor L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
